-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:36:52.933782+00:00
-- url     : https://prove2.me/submissions/2c64c420-3b37-45de-9bfc-4c83684f2c75

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_hasZeroDeficiencyOn_of_eigenvectors
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
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


theorem solution (d : ℕ) (p q : Fin d → ℕ → ℝ)
    (hunb : ∀ C : ℝ, ∃ k, C < |(∑ i, p i k ^ 2) + (∑ i, q i k ^ 2) + 1|) :
    ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ℕ,
      ‖(diagComparisonData d p q).comparison f‖ ≤ C * ‖f‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨k, hk⟩ := hunb C
  have h := hC (basis k)
  change ‖(diagComparisonData d p q).comparison (basis k)‖ ≤ C * ‖basis k‖ at h
  rw [diag_basis] at h
  change ‖(((∑ i, p i k ^ 2) + (∑ i, q i k ^ 2) + 1 : ℝ) : ℂ) • (basis k : lpFiniteModes ℕ)‖ ≤ C * ‖basis k‖ at h
  have hb : ‖basis k‖ = 1 := by
    change ‖((basis k : lpFiniteModes ℕ) : L2N)‖ = 1
    norm_num [basis, lp.norm_single]
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, hb, mul_one] at h
  exact (not_lt_of_ge h) hk

#print axioms solution
