-- Prove2me | solution 1 for CauchyRiemannIndex.symLoop_of_symplecticPath_family
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T13:50:44.063986+00:00
-- url     : https://prove2.me/submissions/fe85d4fd-74db-4aa6-bc04-632501360712

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_symplectic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Order.Floor

open CauchyRiemannIndex Matrix

namespace CRJ3

variable {n : ℕ}

theorem J_mul_J (X : Mat n) : J₀ n * (J₀ n * X) = -X := by
  rw [← mul_assoc, show J₀ n * J₀ n = -1 from Matrix.J_squared _ _, neg_one_mul]

theorem J_tr : (J₀ n)ᵀ = -J₀ n := Matrix.J_transpose _ _

theorem tr_J_self {A : Mat n} (hA : IsSymplectic A) : Aᵀ * J₀ n * A = J₀ n := by
  have h := SymplecticGroup.transpose_mem hA
  rw [SymplecticGroup.mem_iff, transpose_transpose] at h
  exact h

theorem self_J_tr {A : Mat n} (hA : IsSymplectic A) : A * J₀ n * Aᵀ = J₀ n :=
  SymplecticGroup.mem_iff.1 hA

/-- The loop value attached to a path value `A` and derivative `B`. -/
def lv (A B : Mat n) : Mat n := J₀ n * B * J₀ n * Aᵀ * J₀ n

theorem lv_ode {A B : Mat n} (hA : IsSymplectic A) : J₀ n * lv A B * A = B := by
  have h := tr_J_self hA
  calc J₀ n * lv A B * A = J₀ n * (J₀ n * (B * J₀ n * (Aᵀ * J₀ n * A))) := by
        simp only [lv, mul_assoc]
    _ = B := by
        rw [h, J_mul_J, mul_assoc, show J₀ n * J₀ n = -1 from Matrix.J_squared _ _, mul_neg_one,
          neg_neg]

theorem lv_symm {A B : Mat n} (key : B * J₀ n * Aᵀ + A * J₀ n * Bᵀ = 0) :
    (lv A B)ᵀ = lv A B := by
  have e : B * J₀ n * Aᵀ = -(A * J₀ n * Bᵀ) := eq_neg_of_add_eq_zero_left key
  have : lv A B = J₀ n * (B * J₀ n * Aᵀ) * J₀ n := by simp only [lv, mul_assoc]
  conv_rhs => rw [this, e]
  simp only [lv, transpose_mul, J_tr, transpose_transpose, mul_assoc, neg_mul, mul_neg, neg_neg]

theorem hasDerivAt_transpose {f f' : ℝ → Mat n} {x : ℝ} (h : HasDerivAt f (f' x) x) :
    HasDerivAt (fun s => (f s)ᵀ) ((f' x)ᵀ) x := by
  letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Mat n) := Matrix.normedSpace
  let T : Mat n →L[ℝ] Mat n :=
    LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv (Fin n ⊕ Fin n)
      (Fin n ⊕ Fin n) ℝ ℝ).toLinearMap
  exact T.hasFDerivAt.comp_hasDerivAt x h

theorem path_key {A B : ℝ → Mat n} (hd : ∀ t, HasDerivAt A (B t) t)
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsSymplectic (A t)) (hd0 : B 0 = 0) (hd1 : B 1 = 0)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : B x * J₀ n * (A x)ᵀ + A x * J₀ n * (B x)ᵀ = 0 := by
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · subst h0; simp [hd0]
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · subst h1; simp [hd1]
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  have hg := ((hd x).mul_const (J₀ n)).mul (hasDerivAt_transpose (f' := B) (hd x))
  have hev : (fun t => A t * J₀ n * (A t)ᵀ) =ᶠ[nhds x] fun _ => J₀ n := by
    filter_upwards [Ioo_mem_nhds h0 h1] with t ht
    exact self_J_tr (hs t ⟨ht.1.le, ht.2.le⟩)
  have hc : HasDerivAt (fun t => A t * J₀ n * (A t)ᵀ) 0 x :=
    (hasDerivAt_const x (J₀ n)).congr_of_eventuallyEq hev
  exact hg.unique hc

/-- The loop attached to a path. -/
noncomputable def pl (A B : ℝ → Mat n) (t : ℝ) : Mat n := lv (A (Int.fract t)) (B (Int.fract t))

theorem fract_mem (t : ℝ) : Int.fract t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

theorem pl_symm {A B : ℝ → Mat n} (hd : ∀ t, HasDerivAt A (B t) t)
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsSymplectic (A t)) (hd0 : B 0 = 0) (hd1 : B 1 = 0)
    (t : ℝ) : (pl A B t).IsSymm :=
  lv_symm (path_key hd hs hd0 hd1 (fract_mem t))

theorem pl_unique {A B : ℝ → Mat n} (hd : ∀ t, HasDerivAt A (B t) t)
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsSymplectic (A t)) (h0 : A 0 = 1) (hd0 : B 0 = 0)
    (hd1 : B 1 = 0) (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution (pl A B) Ψ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, Ψ t = A t := by
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  have hsym := pl_symm hd hs hd0 hd1
  have hM : ∀ x, HasDerivAt (fun s => (Ψ s)ᵀ * J₀ n * A s)
      ((J₀ n * pl A B x * Ψ x)ᵀ * J₀ n * A x + (Ψ x)ᵀ * J₀ n * B x) x := fun x =>
    ((hasDerivAt_transpose (f' := fun x => J₀ n * pl A B x * Ψ x) (hΨ.2 x)).mul_const
      (J₀ n)).mul (hd x)
  have hM0 : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun s => (Ψ s)ᵀ * J₀ n * A s) 0 (Set.Ici x) x := by
    intro x hx
    have hfr : Int.fract x = x := Int.fract_eq_self.2 ⟨hx.1, hx.2⟩
    have hB : B x = J₀ n * pl A B x * A x := by
      rw [show pl A B x = lv (A x) (B x) by simp only [pl, hfr]]
      exact (lv_ode (hs x ⟨hx.1, hx.2.le⟩)).symm
    have key : (J₀ n * pl A B x * Ψ x)ᵀ * J₀ n * A x + (Ψ x)ᵀ * J₀ n * B x = 0 := by
      rw [hB, transpose_mul, transpose_mul, hsym x, J_tr]
      simp only [mul_assoc, neg_mul, mul_neg, J_mul_J]
      simp
    have hMx := hM x
    rw [key] at hMx
    exact hMx.hasDerivWithinAt
  have hcont : ContinuousOn (fun s => (Ψ s)ᵀ * J₀ n * A s) (Set.Icc 0 1) :=
    fun x _ => (hM x).continuousAt.continuousWithinAt
  intro t ht
  have hc := constant_of_has_deriv_right_zero hcont hM0 t ht
  simp only [hΨ.1, h0, transpose_one, one_mul, mul_one] at hc
  have hΨs := self_J_tr (fundamentalSolution_symplectic n (pl A B) hsym Ψ hΨ t)
  calc Ψ t = -(Ψ t * J₀ n * J₀ n) := by
        rw [mul_assoc, show J₀ n * J₀ n = -1 from Matrix.J_squared _ _, mul_neg_one, neg_neg]
    _ = -(Ψ t * J₀ n * ((Ψ t)ᵀ * J₀ n * A t)) := by rw [hc]
    _ = -(Ψ t * J₀ n * (Ψ t)ᵀ * J₀ n * A t) := by simp only [mul_assoc]
    _ = A t := by rw [hΨs, mul_assoc, J_mul_J, neg_neg]

theorem family (n : ℕ) (φ φ' : unitInterval → ℝ → Mat n)
    (hφ : Continuous fun p : unitInterval × ℝ => φ p.1 p.2)
    (hφ' : Continuous fun p : unitInterval × ℝ => φ' p.1 p.2)
    (hd : ∀ s t, HasDerivAt (φ s) (φ' s t) t)
    (hs : ∀ s, ∀ t ∈ Set.Icc (0 : ℝ) 1, IsSymplectic (φ s t))
    (h0 : ∀ s, φ s 0 = 1) (hd0 : ∀ s, φ' s 0 = 0) (hd1 : ∀ s, φ' s 1 = 0)
    (hn : ∀ s, (1 - φ s 1).det ≠ 0) :
    ∃ H : C(unitInterval × ℝ, Mat n),
      (∀ s t, H (s, t) = J₀ n * φ' s (Int.fract t) * J₀ n * (φ s (Int.fract t))ᵀ * J₀ n) ∧
      ∀ s, IsSymLoop (fun t => H (s, t)) ∧ IsNondegenerate (fun t => H (s, t)) ∧
        ∀ Ψ, IsFundamentalSolution (fun t => H (s, t)) Ψ → ∀ t ∈ Set.Icc (0 : ℝ) 1, Ψ t = φ s t := by
  have hc : Continuous fun p : unitInterval × ℝ => lv (φ p.1 p.2) (φ' p.1 p.2) := by
    unfold lv
    exact (((continuous_const.mul hφ').mul continuous_const).mul hφ.matrix_transpose).mul
      continuous_const
  have hcont : Continuous fun p : unitInterval × ℝ =>
      lv (φ p.1 (Int.fract p.2)) (φ' p.1 (Int.fract p.2)) :=
    ContinuousOn.comp_fract' (f := fun s x => lv (φ s x) (φ' s x)) hc.continuousOn
      (fun s => by simp [lv, hd0, hd1])
  let H : C(unitInterval × ℝ, Mat n) := ⟨_, hcont⟩
  have hH : ∀ s, (fun t => H (s, t)) = pl (φ s) (φ' s) := fun s => rfl
  refine ⟨H, fun s t => rfl, fun s => ?_⟩
  rw [hH s]
  have hu := pl_unique (hd s) (hs s) (h0 s) (hd0 s) (hd1 s)
  have hpc : Continuous (pl (φ s) (φ' s)) := by
    rw [← hH s]; exact H.continuous.comp (Continuous.prodMk_right s)
  have hper : Function.Periodic (pl (φ s) (φ' s)) 1 := fun t => by
    simp only [pl, Int.fract_add_one]
  refine ⟨⟨hpc, hper, pl_symm (hd s) (hs s) (hd0 s) (hd1 s)⟩, fun Ψ hΨ => ?_, hu⟩
  rw [hu Ψ hΨ 1 ⟨zero_le_one, le_rfl⟩]; exact hn s

end CRJ3

theorem solution (n : ℕ) (φ φ' : unitInterval → ℝ → Mat n)
    (hφ : Continuous fun p : unitInterval × ℝ => φ p.1 p.2)
    (hφ' : Continuous fun p : unitInterval × ℝ => φ' p.1 p.2)
    (hd : ∀ s t, HasDerivAt (φ s) (φ' s t) t)
    (hs : ∀ s, ∀ t ∈ Set.Icc (0 : ℝ) 1, IsSymplectic (φ s t))
    (h0 : ∀ s, φ s 0 = 1) (hd0 : ∀ s, φ' s 0 = 0) (hd1 : ∀ s, φ' s 1 = 0)
    (hn : ∀ s, (1 - φ s 1).det ≠ 0) :
    ∃ H : C(unitInterval × ℝ, Mat n),
      (∀ s t, H (s, t) = J₀ n * φ' s (Int.fract t) * J₀ n * (φ s (Int.fract t))ᵀ * J₀ n) ∧
      ∀ s, IsSymLoop (fun t => H (s, t)) ∧ IsNondegenerate (fun t => H (s, t)) ∧
        ∀ Ψ, IsFundamentalSolution (fun t => H (s, t)) Ψ → ∀ t ∈ Set.Icc (0 : ℝ) 1, Ψ t = φ s t :=
  CRJ3.family n φ φ' hφ hφ' hd hs h0 hd0 hd1 hn
