-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SecondQuant.fockOp_hasZeroDeficiencyOn_of_farisLavine
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:12:44.272964+00:00
-- url     : https://prove2.me/submissions/b5d0cb6d-0d12-44f1-aa5f-6d3db17b2f17

/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0. -/
import Mathlib
import Definitions.Def_ChapterNavierStokesFockFarisLavine
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 2000
open scoped ENNReal
namespace BookProof.NavierStokesFlow.SecondQuant
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.FarisLavineLift
variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]
variable {D : ∀ m, Submodule ℂ (S m)}
theorem single_mem_fockCore [DecidableEq ι] (m : ι) (x : S m) (hx : x ∈ D m) :
    lp.single 2 m x ∈ fockCore D := by
  have hne_zero : ∀ {j : ι}, j ≠ m → ((lp.single 2 m x : lp S 2) : ∀ j, S j) j = 0 := by
    intro j hj
    exact lp.single_apply_ne 2 m x hj
  constructor
  · refine (Set.finite_singleton m).subset ?_
    intro j hj
    simp only [Function.mem_support] at hj
    by_contra hcon
    have hjm : j ≠ m := by simpa using hcon
    exact hj (by rw [hne_zero hjm]; simp)
  · intro j
    rcases eq_or_ne j m with rfl | hjm
    · simpa [lp.single_apply_self] using hx
    · rw [hne_zero hjm]
      exact (D j).zero_mem

theorem fockCore_dense (hD : ∀ m, Dense ((D m : Submodule ℂ (S m)) : Set (S m))) :
    Dense ((fockCore D : Submodule ℂ (lp S 2)) : Set (lp S 2)) := by
  classical
  rw [Metric.dense_iff]
  intro f r hr
  -- first approximate `f` by a finite sector truncation
  have hsum := lp.hasSum_single (E := S) (p := 2) (by simp) f
  obtain ⟨s, hs⟩ :=
    (hsum.eventually (Metric.ball_mem_nhds f (by linarith : (0:ℝ) < r / 2))).exists
  -- then approximate each of the finitely many sector states from `D m`
  have hchoice : ∀ m : ι, ∃ y ∈ ((D m : Submodule ℂ (S m)) : Set (S m)),
      dist ((f : ∀ m, S m) m) y < r / (2 * ((s.card : ℝ) + 1)) := by
    intro m
    have hpos : 0 < r / (2 * ((s.card : ℝ) + 1)) := by positivity
    have hmem : (f : ∀ m, S m) m ∈ closure ((D m : Submodule ℂ (S m)) : Set (S m)) := by
      rw [(hD m).closure_eq]; trivial
    exact Metric.mem_closure_iff.mp hmem _ hpos
  choose y hyD hy using hchoice
  refine ⟨∑ m ∈ s, lp.single 2 m (y m), ?_, ?_⟩
  · -- the approximant is within `r` of `f`
    have hdiff : ‖(∑ m ∈ s, lp.single 2 m ((f : ∀ m, S m) m)) - ∑ m ∈ s, lp.single 2 m (y m)‖
        ≤ ∑ m ∈ s, ‖(f : ∀ m, S m) m - y m‖ := by
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun m _ => ?_))
      rw [← lp.single_sub]
      exact lp.norm_single (by norm_num) m _
    have hbound : ∑ m ∈ s, ‖(f : ∀ m, S m) m - y m‖ < r / 2 := by
      have hlt : ∀ m ∈ s, ‖(f : ∀ m, S m) m - y m‖ ≤ r / (2 * ((s.card : ℝ) + 1)) := by
        intro m _
        have h := hy m
        rw [dist_eq_norm] at h
        exact h.le
      have hcalc : ∑ m ∈ s, ‖(f : ∀ m, S m) m - y m‖
          ≤ (s.card : ℝ) * (r / (2 * ((s.card : ℝ) + 1))) := by
        calc ∑ m ∈ s, ‖(f : ∀ m, S m) m - y m‖
            ≤ ∑ _m ∈ s, r / (2 * ((s.card : ℝ) + 1)) := Finset.sum_le_sum hlt
          _ = (s.card : ℝ) * (r / (2 * ((s.card : ℝ) + 1))) := by simp [mul_comm]
      have heq : (s.card : ℝ) * (r / (2 * ((s.card : ℝ) + 1)))
          = (r / 2) * ((s.card : ℝ) / ((s.card : ℝ) + 1)) := by
        have hc : ((s.card : ℝ) + 1) ≠ 0 := by positivity
        field_simp
      have hfrac : (s.card : ℝ) / ((s.card : ℝ) + 1) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith
      have hlast : (s.card : ℝ) * (r / (2 * ((s.card : ℝ) + 1))) < r / 2 := by
        rw [heq]
        nlinarith [hr, hfrac]
      linarith
    have h1 : dist (∑ m ∈ s, lp.single 2 m ((f : ∀ m, S m) m)) f < r / 2 := hs
    have h2 : dist (∑ m ∈ s, lp.single 2 m (y m))
        (∑ m ∈ s, lp.single 2 m ((f : ∀ m, S m) m)) < r / 2 := by
      rw [dist_eq_norm, ← norm_neg]
      simpa using lt_of_le_of_lt hdiff hbound
    have htri := dist_triangle (∑ m ∈ s, lp.single 2 m (y m))
      (∑ m ∈ s, lp.single 2 m ((f : ∀ m, S m) m)) f
    simp only [Metric.mem_ball]
    linarith
  · -- and it lies in the finite-particle domain
    exact Submodule.sum_mem _ fun m _ => single_mem_fockCore m (y m) (hyD m)
theorem fockOp_comp (A B : ∀ m, D m →ₗ[ℂ] D m) :
    fockOp (fun m => (A m).comp (B m)) = (fockOp A).comp (fockOp B) := by
  refine LinearMap.ext fun v => Subtype.ext (lp.ext ?_)
  funext m
  rfl

theorem fockOp_sub (A B : ∀ m, D m →ₗ[ℂ] D m) :
    fockOp (fun m => A m - B m) = fockOp A - fockOp B := by
  refine LinearMap.ext fun v => Subtype.ext (lp.ext ?_)
  funext m
  rfl

theorem fockOp_commDom (A B : ∀ m, D m →ₗ[ℂ] D m) :
    fockOp (fun m => commDom (A m) (B m)) = commDom (fockOp A) (fockOp B) := by
  rw [commDom, ← fockOp_comp, ← fockOp_comp, ← fockOp_sub]
  rfl

theorem fockOp_isSymmetricDom (A : ∀ m, D m →ₗ[ℂ] D m)
    (hA : ∀ m, FullEsa.IsSymmetricDom (A m)) :
    FullEsa.IsSymmetricDom (fockOp A) := by
  intro x y
  have h1 := lp.hasSum_inner (𝕜 := ℂ) ((fockOp A x : fockCore D) : lp S 2) ((y : lp S 2))
  have h2 := lp.hasSum_inner (𝕜 := ℂ) ((x : lp S 2)) ((fockOp A y : fockCore D) : lp S 2)
  have hterm : ∀ m : ι,
      (inner ℂ (((fockOp A x : fockCore D) : lp S 2) m) ((y : lp S 2) m) : ℂ)
        = inner ℂ ((x : lp S 2) m) (((fockOp A y : fockCore D) : lp S 2) m) := by
    intro m
    exact hA m ⟨(x : lp S 2) m, (x.2).2 m⟩ ⟨(y : lp S 2) m, (y.2).2 m⟩
  have h2' : HasSum
      (fun m => (inner ℂ (((fockOp A x : fockCore D) : lp S 2) m) ((y : lp S 2) m) : ℂ))
      (inner ℂ ((x : lp S 2)) ((fockOp A y : fockCore D) : lp S 2)) := by
    simpa only [hterm] using h2
  exact h1.unique h2'

private theorem rpow_two_eq (x : ℝ) : x ^ ((2 : ℝ≥0∞).toReal) = x ^ 2 := by
  have h : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h, Real.rpow_natCast]

theorem fockOp_norm_le_of_sectors (H N : ∀ m, D m →ₗ[ℂ] D m) (cst : ℝ) (hc : 0 ≤ cst)
    (hb : ∀ (m : ι) (x : D m), ‖((H m x : D m) : S m)‖ ≤ cst * ‖((N m x : D m) : S m)‖)
    (v : fockCore D) :
    ‖((fockOp H v : fockCore D) : lp S 2)‖ ≤ cst * ‖((fockOp N v : fockCore D) : lp S 2)‖ := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h1 := lp.hasSum_norm hp ((fockOp H v : fockCore D) : lp S 2)
  have h2 := (lp.hasSum_norm hp ((fockOp N v : fockCore D) : lp S 2)).mul_left (cst ^ 2)
  have hterm : ∀ m : ι,
      ‖(((fockOp H v : fockCore D) : lp S 2) m)‖ ^ ((2 : ℝ≥0∞).toReal)
        ≤ cst ^ 2 * ‖(((fockOp N v : fockCore D) : lp S 2) m)‖ ^ ((2 : ℝ≥0∞).toReal) := by
    intro m
    rw [rpow_two_eq _, rpow_two_eq _]
    have hbm := hb m ⟨(v : lp S 2) m, (v.2).2 m⟩
    have hHm : (((fockOp H v : fockCore D) : lp S 2) m)
        = ((H m ⟨(v : lp S 2) m, (v.2).2 m⟩ : D m) : S m) := rfl
    have hNm : (((fockOp N v : fockCore D) : lp S 2) m)
        = ((N m ⟨(v : lp S 2) m, (v.2).2 m⟩ : D m) : S m) := rfl
    rw [hHm, hNm]
    nlinarith [norm_nonneg ((H m ⟨(v : lp S 2) m, (v.2).2 m⟩ : D m) : S m),
      norm_nonneg ((N m ⟨(v : lp S 2) m, (v.2).2 m⟩ : D m) : S m), hbm,
      mul_nonneg hc (norm_nonneg ((N m ⟨(v : lp S 2) m, (v.2).2 m⟩ : D m) : S m))]
  have hsum := hasSum_le hterm h1 h2
  rw [rpow_two_eq _, rpow_two_eq _] at hsum
  nlinarith [norm_nonneg ((fockOp H v : fockCore D) : lp S 2),
    norm_nonneg ((fockOp N v : fockCore D) : lp S 2),
    mul_nonneg hc (norm_nonneg ((fockOp N v : fockCore D) : lp S 2))]

theorem fockOp_norm_inner_le_of_sectors (A N : ∀ m, D m →ₗ[ℂ] D m) (c₂ : ℝ)
    (hb : ∀ (m : ι) (x : D m), ‖(inner ℂ ((x : S m)) ((A m x : D m) : S m) : ℂ)‖
      ≤ c₂ * (inner ℂ ((x : S m)) ((N m x : D m) : S m) : ℂ).re)
    (v : fockCore D) :
    ‖(inner ℂ ((v : lp S 2)) ((fockOp A v : fockCore D) : lp S 2) : ℂ)‖
      ≤ c₂ * (inner ℂ ((v : lp S 2)) ((fockOp N v : fockCore D) : lp S 2) : ℂ).re := by
  have hA := lp.hasSum_inner (𝕜 := ℂ) ((v : lp S 2)) ((fockOp A v : fockCore D) : lp S 2)
  have hN := lp.hasSum_inner (𝕜 := ℂ) ((v : lp S 2)) ((fockOp N v : fockCore D) : lp S 2)
  have hNre : HasSum
      (fun m => (inner ℂ ((v : lp S 2) m) (((fockOp N v : fockCore D) : lp S 2) m) : ℂ).re)
      ((inner ℂ ((v : lp S 2)) ((fockOp N v : fockCore D) : lp S 2) : ℂ).re) :=
    hN.map Complex.reAddGroupHom Complex.continuous_re
  have hterm : ∀ m : ι,
      ‖(inner ℂ ((v : lp S 2) m) (((fockOp A v : fockCore D) : lp S 2) m) : ℂ)‖
        ≤ c₂ * (inner ℂ ((v : lp S 2) m)
            (((fockOp N v : fockCore D) : lp S 2) m) : ℂ).re := by
    intro m
    exact hb m ⟨(v : lp S 2) m, (v.2).2 m⟩
  have hmaj := hNre.mul_left c₂
  have hsummable_norm : Summable fun m : ι =>
      ‖(inner ℂ ((v : lp S 2) m) (((fockOp A v : fockCore D) : lp S 2) m) : ℂ)‖ :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hterm hmaj.summable
  calc ‖(inner ℂ ((v : lp S 2)) ((fockOp A v : fockCore D) : lp S 2) : ℂ)‖
      = ‖∑' m : ι, (inner ℂ ((v : lp S 2) m)
          (((fockOp A v : fockCore D) : lp S 2) m) : ℂ)‖ := by rw [hA.tsum_eq]
    _ ≤ ∑' m : ι, ‖(inner ℂ ((v : lp S 2) m)
          (((fockOp A v : fockCore D) : lp S 2) m) : ℂ)‖ :=
        norm_tsum_le_tsum_norm hsummable_norm
    _ ≤ ∑' m : ι, c₂ * (inner ℂ ((v : lp S 2) m)
          (((fockOp N v : fockCore D) : lp S 2) m) : ℂ).re :=
        Summable.tsum_mono hsummable_norm hmaj.summable hterm
    _ = c₂ * (inner ℂ ((v : lp S 2)) ((fockOp N v : fockCore D) : lp S 2) : ℂ).re :=
        hmaj.tsum_eq
end BookProof.NavierStokesFlow.SecondQuant
-- Generated from ChapterNavierStokesFockFarisLavine.lean — theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_hasZeroDeficiencyOn_of_farisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant








open scoped ENNReal



open FarisLavineLift
open BookProof.NavierStokesFlow.FullEsa
open BookProof.NavierStokesFlow.FarisLavineLift

variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]
variable {D : ∀ m, Submodule ℂ (S m)}
theorem solution
    (H N : ∀ m, D m →ₗ[ℂ] D m) (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (farisLavine : ∀ (D' : Submodule ℂ (lp S 2)) (H' N' : D' →ₗ[ℂ] D') (a b : ℝ),
      Dense (D' : Set (lp S 2)) →
      (∀ x y : D', (inner ℂ (H' x : lp S 2) (y : lp S 2) : ℂ)
        = inner ℂ (x : lp S 2) (H' y : lp S 2)) →
      (∀ v : D', ‖(H' v : lp S 2)‖ ≤ a * ‖(N' v : lp S 2)‖) →
      (∀ v : D', ‖(inner ℂ (v : lp S 2)
          ((H' (N' v) : lp S 2) - (N' (H' v) : lp S 2)) : ℂ)‖
        ≤ b * ‖(inner ℂ (v : lp S 2) (N' v : lp S 2) : ℂ)‖) →
      HasZeroDeficiencyOn D' H')
    (hdense : ∀ m, Dense ((D m : Submodule ℂ (S m)) : Set (S m)))
    (hsym : ∀ m, FullEsa.IsSymmetricDom (H m))
    (hbound : ∀ (m : ι) (x : D m), ‖((H m x : D m) : S m)‖ ≤ c₁ * ‖((N m x : D m) : S m)‖)
    (hcomm : ∀ (m : ι) (x : D m),
      ‖(inner ℂ ((x : S m)) ((commDom (H m) (N m) x : D m) : S m) : ℂ)‖
        ≤ c₂ * (inner ℂ ((x : S m)) ((N m x : D m) : S m) : ℂ).re) :
    HasZeroDeficiencyOn (fockCore D) (fockOp H) := by
  refine farisLavine (fockCore D) (fockOp H) (fockOp N) c₁ c₂
    (fockCore_dense hdense) (fockOp_isSymmetricDom H hsym)
    (fockOp_norm_le_of_sectors H N c₁ hc₁ hbound) ?_
  intro v
  have hcommEq : ((fockOp H (fockOp N v) : fockCore D) : lp S 2)
      - ((fockOp N (fockOp H v) : fockCore D) : lp S 2)
      = ((fockOp (fun m => commDom (H m) (N m)) v : fockCore D) : lp S 2) := by
    rw [fockOp_commDom]
    rfl
  rw [hcommEq]
  refine le_trans (fockOp_norm_inner_le_of_sectors (fun m => commDom (H m) (N m)) N c₂
    hcomm v) ?_
  exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hc₂
#print axioms solution
