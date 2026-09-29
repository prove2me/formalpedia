-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SecondQuant.fockComparison_dense
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:12:23.165655+00:00
-- url     : https://prove2.me/submissions/d7208ec1-df06-4530-b61d-9495ca118930

import Definitions.Def_ChapterNavierStokesFockFarisLavine
-- Source: Leonardo Pedro, timepiece61595bc, Apache-2.0. Adapted to Prove2Me definitions.
namespace BookProof.NavierStokesFlow.SecondQuant
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FarisLavineLift
open scoped ENNReal
variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]
variable {D : ∀ m, Submodule ℂ (S m)}
@[simp] theorem ofSectors_apply (g : ∀ m, S m) (h : (Function.support fun m => ‖g m‖).Finite)
    (m : ι) : (ofSectors g h : ∀ m, S m) m = g m := rfl

@[simp] theorem mem_fockCore {f : lp S 2} :
    f ∈ fockCore D ↔
      (Function.support fun m => ‖(f : ∀ m, S m) m‖).Finite ∧ ∀ m, (f : ∀ m, S m) m ∈ D m :=
  Iff.rfl

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

@[simp] theorem fockOp_apply (A : ∀ m, D m →ₗ[ℂ] D m) (f : fockCore D) (m : ι) :
    ((fockOp A f : lp S 2) : ∀ m, S m) m = ((A m ⟨(f : lp S 2) m, (f.2).2 m⟩ : D m) : S m) := rfl

theorem fockOp_single [DecidableEq ι] (A : ∀ m, D m →ₗ[ℂ] D m) (m : ι) (x : D m) :
    (fockOp A ⟨lp.single 2 m (x : S m), single_mem_fockCore m (x : S m) x.2⟩ : lp S 2)
      = lp.single 2 m ((A m x : D m) : S m) := by
  set f : fockCore D := ⟨lp.single 2 m (x : S m), single_mem_fockCore m (x : S m) x.2⟩ with hf
  apply lp.ext
  funext j
  rw [fockOp_apply A f j]
  rcases eq_or_ne j m with rfl | hne
  · have hx : (⟨(f : lp S 2) j, (f.2).2 j⟩ : D j) = x := by
      ext
      change ((lp.single 2 j (x : S j) : lp S 2) : ∀ j, S j) j = (x : S j)
      exact lp.single_apply_self 2 j (x : S j)
    rw [hx, lp.single_apply_self]
  · have hz : (⟨(f : lp S 2) j, (f.2).2 j⟩ : D j) = 0 := by
      ext
      change ((lp.single 2 m (x : S m) : lp S 2) : ∀ j, S j) j = 0
      exact lp.single_apply_ne 2 m (x : S m) hne
    rw [hz, lp.single_apply_ne 2 m _ hne]
    simp

theorem fockOp_hasZeroDeficiencyOn (A : ∀ m, D m →ₗ[ℂ] D m)
    (hA : ∀ m, HasZeroDeficiencyOn (D m) (A m)) :
    HasZeroDeficiencyOn (fockCore D) (fockOp A) := by
  classical
  have key : ∀ (z : ℂ) (w : lp S 2),
      (∀ v : fockCore D, (inner ℂ ((fockOp A v : lp S 2)) w : ℂ) = inner ℂ ((v : lp S 2)) (z • w)) →
      ∀ m : ι, ∀ x : D m,
        (inner ℂ ((A m x : D m) : S m) ((w : ∀ m, S m) m) : ℂ)
          = inner ℂ ((x : S m)) (z • (w : ∀ m, S m) m) := by
    intro z w hw m x
    have hv := hw ⟨lp.single 2 m (x : S m), single_mem_fockCore m (x : S m) x.2⟩
    rw [fockOp_single A m x] at hv
    rw [lp.inner_single_left] at hv
    have hz : ((z • w : lp S 2) : ∀ m, S m) m = z • (w : ∀ m, S m) m := by
      simp [lp.coeFn_smul]
    rw [show ((⟨lp.single 2 m (x : S m), single_mem_fockCore m (x : S m) x.2⟩ :
        fockCore D) : lp S 2) = lp.single 2 m (x : S m) from rfl, lp.inner_single_left,
      hz] at hv
    exact hv
  constructor
  · intro w hw
    apply lp.ext
    funext m
    have hm := (hA m).1 ((w : ∀ m, S m) m) (fun x => key Complex.I w hw m x)
    simpa using hm
  · intro w hw
    apply lp.ext
    funext m
    have hw' : ∀ v : fockCore D,
        (inner ℂ ((fockOp A v : lp S 2)) w : ℂ)
          = inner ℂ ((v : lp S 2)) ((-Complex.I) • w) := by
      intro v
      simpa using hw v
    have hm := (hA m).2 ((w : ∀ m, S m) m) (fun x => by
      simpa using key (-Complex.I) w hw' m x)
    simpa using hm

theorem fockCore_ne_top {S : ℕ → Type*} [∀ m, NormedAddCommGroup (S m)]
    [∀ m, InnerProductSpace ℂ (S m)] (D : ∀ m, Submodule ℂ (S m))
    (v : ∀ m, S m) (hv : ∀ m, ‖v m‖ = 1) :
    (fockCore D : Submodule ℂ (lp S 2)) ≠ ⊤ := by
  intro htop
  set g : ∀ m, S m := fun m => ((1 : ℝ) / (m + 1) : ℝ) • v m with hg
  have hnorm : ∀ k : ℕ, ‖g k‖ = 1 / (k + 1) := by
    intro k
    have hpos : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
    simp only [hg, norm_smul, hv, Real.norm_eq_abs, mul_one]
    exact abs_of_nonneg hpos
  have hmem : Memℓp g 2 := by
    apply memℓp_gen
    have hcongr : ∀ k : ℕ, ‖g k‖ ^ (2 : ℝ≥0∞).toReal = (1 / ((k : ℝ) + 1)) ^ 2 := by
      intro k
      rw [hnorm k]
      norm_num
    rw [summable_congr hcongr]
    have hbase : Summable fun k : ℕ => (1 / ((k : ℝ)) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    have := (summable_nat_add_iff (f := fun k : ℕ => (1 / ((k : ℝ)) ^ 2)) 1).mpr hbase
    refine this.congr fun k => ?_
    rw [div_pow]
    norm_num
  have hmemCore : (⟨g, hmem⟩ : lp S 2) ∈ fockCore D := by rw [htop]; trivial
  have hfin := hmemCore.1
  have hinf : ¬ (Function.support fun m => ‖g m‖).Finite := by
    intro hfin'
    have hsub : Set.univ ⊆ Function.support fun m => ‖g m‖ := by
      intro k _
      simp only [Function.mem_support, hnorm k]
      positivity
    exact Set.infinite_univ (hfin'.subset hsub)
  exact hinf hfin

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

theorem fockOp_ge_norm_sq (N : ∀ m, D m →ₗ[ℂ] D m)
    (hb : ∀ (m : ι) (x : D m),
      ‖(x : S m)‖ ^ 2 ≤ (inner ℂ ((x : S m)) ((N m x : D m) : S m) : ℂ).re)
    (v : fockCore D) :
    ‖(v : lp S 2)‖ ^ 2
      ≤ (inner ℂ ((v : lp S 2)) ((fockOp N v : fockCore D) : lp S 2) : ℂ).re := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hnorm := lp.hasSum_norm hp ((v : lp S 2))
  have hN := lp.hasSum_inner (𝕜 := ℂ) ((v : lp S 2)) ((fockOp N v : fockCore D) : lp S 2)
  have hNre : HasSum
      (fun m => (inner ℂ ((v : lp S 2) m) (((fockOp N v : fockCore D) : lp S 2) m) : ℂ).re)
      ((inner ℂ ((v : lp S 2)) ((fockOp N v : fockCore D) : lp S 2) : ℂ).re) :=
    hN.map Complex.reAddGroupHom Complex.continuous_re
  have hterm : ∀ m : ι, ‖((v : lp S 2) m)‖ ^ ((2 : ℝ≥0∞).toReal)
      ≤ (inner ℂ ((v : lp S 2) m)
          (((fockOp N v : fockCore D) : lp S 2) m) : ℂ).re := by
    intro m
    rw [rpow_two_eq]
    exact hb m ⟨(v : lp S 2) m, (v.2).2 m⟩
  have hsum := hasSum_le hterm hnorm hNre
  rwa [rpow_two_eq] at hsum

end BookProof.NavierStokesFlow.SecondQuant

namespace ParentQDiag
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)
set_option autoImplicit false

private theorem parent_total_deficiency {I : Type*} (e : I → c.D) (lam : I → ℝ)
    (heig : ∀ i, c.comparison (e i) = ((lam i : ℂ)) • e i)
    (htotal : ∀ w : F, (∀ i, (inner ℂ ((e i : c.D) : F) w : ℂ) = 0) → w = 0) :
    HasZeroDeficiencyOn c.D c.comparison := by
  have hscalar (a : ℝ) (z : ℂ) (h : (a : ℂ) * z = Complex.I * z ∨ (a : ℂ) * z = -(Complex.I * z)) : z = 0 := by
    rcases h with h | h
    · have hz : ((a : ℂ) - Complex.I) * z = 0 := by linear_combination h
      apply (mul_eq_zero.mp hz).resolve_left
      intro ha
      have hIm := congrArg Complex.im (sub_eq_zero.mp ha)
      norm_num at hIm
    · have hz : ((a : ℂ) + Complex.I) * z = 0 := by linear_combination h
      apply (mul_eq_zero.mp hz).resolve_left
      intro ha
      have hIm := congrArg Complex.im ha
      norm_num at hIm
  constructor
  · intro w hw
    apply htotal w
    intro i
    apply hscalar (lam i)
    left
    have hh := hw (e i)
    rw [heig i] at hh
    simpa only [Submodule.coe_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal] using hh
  · intro w hw
    apply htotal w
    intro i
    apply hscalar (lam i)
    right
    have hh := hw (e i)
    rw [heig i] at hh
    simpa only [Submodule.coe_smul, inner_smul_left, inner_neg_right, inner_smul_right, Complex.conj_ofReal] using hh


open LpNat DiagonalEsa
private theorem diag_apply (d : ℕ) (p q : Fin d → ℕ → ℝ) (f : lpFiniteModes ℕ) (k : ℕ) :
    (((diagComparisonData d p q).comparison f : lpFiniteModes ℕ) : L2N) k =
      (((∑ i, p i k ^ 2) + (∑ i, q i k ^ 2) + 1 : ℝ) : ℂ) * ((f : L2N) k) := by
  let A : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ :=
    (∑ i, (diagOp (p i)).comp (diagOp (p i))) +
    (∑ i, (diagOp (q i)).comp (diagOp (q i))) + LinearMap.id
  change ((A f : L2N) k) = _
  dsimp only [A]
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply,
    Submodule.coe_add, Submodule.coe_sum, lp.coeFn_sum, lp.coeFn_add, Pi.add_apply, Finset.sum_apply,
    diagOp_coe, diagFun, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_one,
    mul_add, add_mul, Finset.sum_mul, pow_two, one_mul]
  simp [Complex.ofReal_mul, mul_assoc, mul_left_comm, mul_comm]
private theorem diag_basis (d : ℕ) (p q : Fin d → ℕ → ℝ) (k : ℕ) :
    (diagComparisonData d p q).comparison (basis k) =
      ((((∑ i, p i k ^ 2) + (∑ i, q i k ^ 2) + 1 : ℝ) : ℂ)) • basis k := by
  apply Subtype.ext
  apply lp.ext
  funext j
  rw [diag_apply]
  by_cases hj : k = j
  · subst j
    simp [basis]
  · simp [basis, lp.single_apply, hj]
private theorem basis_total (w : L2N) (hw : ∀ i, (inner ℂ ((basis i : lpFiniteModes ℕ) : L2N) w : ℂ) = 0) : w = 0 := by
  apply lp.ext
  funext i
  have hi := hw i
  simpa [basis, lp.inner_single_left] using hi


theorem parent_diag_deficiency (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    HasZeroDeficiencyOn (lpFiniteModes ℕ) (diagComparisonData d p q).comparison := by
  exact parent_total_deficiency (diagComparisonData d p q) basis
    (fun k => (∑ i, p i k ^ 2) + (∑ i, q i k ^ 2) + 1)
    (diag_basis d p q) basis_total


end ParentQDiag

namespace ParentQQuad
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)
set_option autoImplicit false

private theorem comparison_quad (v : c.D) :
    (inner ℂ ((v : F)) ((c.comparison v : c.D) : F) : ℂ).re
      = (∑ i, ‖((c.mom i v : c.D) : F)‖ ^ 2) + (∑ i, ‖((c.drift i v : c.D) : F)‖ ^ 2)
        + ‖(v : F)‖ ^ 2 := by
  have hs (A : c.D →ₗ[ℂ] c.D) (hA : FullEsa.IsSymmetricDom A) :
      (inner ℂ (v : F) ((A (A v) : c.D) : F)).re = ‖((A v : c.D) : F)‖ ^ 2 := by
    rw [← hA v (A v)]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  simp only [ComparisonData.comparison, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.id_apply, Submodule.coe_add, Submodule.coe_sum,
    inner_add_right, inner_sum, Complex.add_re, Complex.re_sum]
  simp_rw [hs _ (c.mom_symm _), hs _ (c.drift_symm _)]
  have hv : (inner ℂ (v : F) (v : F)).re = ‖(v : F)‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  rw [hv]


theorem parent_comparison_ge_norm_sq (v : c.D) :
    ‖(v : F)‖ ^ 2 ≤ (inner ℂ ((v : F)) ((c.comparison v : c.D) : F) : ℂ).re := by
  rw [comparison_quad]
  have h1 : 0 ≤ ∑ i, ‖((c.mom i v : c.D) : F)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0 ≤ ∑ i, ‖((c.drift i v : c.D) : F)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

end ParentQQuad
/-
Source adaptations: Copyright 2026 Leonardo Pedro, timepiece commit 61595bc.
https://github.com/leonardopedro/timepiece/tree/61595bc
Changed to restore public platform helper proofs and use Prove2Me definitions.
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.


   Copyright 2026 Leonardo Pedro

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

section Target
-- Generated from ChapterNavierStokesFockFarisLavine.lean — theorem BookProof.NavierStokesFlow.SecondQuant.fockComparison_dense
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant








open scoped ENNReal



open FarisLavineLift

variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]
variable {D : ∀ m, Submodule ℂ (S m)}



















open FarisLavineLift LpNat DiagonalEsa
theorem solution :
    Dense ((fockCore fiberCore : Submodule ℂ (lp fiberSector 2)) : Set (lp fiberSector 2)) := by
  exact fockCore_dense (fun _ => lpFiniteModes_dense)
#print axioms solution

end Target
