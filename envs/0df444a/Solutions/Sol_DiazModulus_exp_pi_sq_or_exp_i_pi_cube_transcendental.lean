-- Prove2me | solution 1 for DiazModulus.exp_pi_sq_or_exp_i_pi_cube_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T16:33:44.875221+00:00
-- url     : https://prove2.me/submissions/dbb0a155-a52b-4c9d-8c58-848ebb564139

import Mathlib
import Theorems.Thm_DiazModulus_geometric_triple_not_logs

/-- If every element of a `ℚ`-subalgebra `B ⊆ ℂ` is algebraic over `ℚ[x]` for one `x ∈ B`,
then `B` has transcendence degree at most one over `ℚ`. -/
theorem pisq_trdeg_le_one_of_adjoin_singleton
    {B : Subalgebra ℚ ℂ} {x : ℂ} (hxB : x ∈ B)
    (halg : ∀ y ∈ B, IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) y) :
    Algebra.trdeg ℚ ↥B ≤ 1 := by
  set x' : (↥B) := ⟨x, hxB⟩ with hx'
  have hmap : Subalgebra.map B.val (Algebra.adjoin ℚ ({x'} : Set ↥B))
      = Algebra.adjoin ℚ ({x} : Set ℂ) := by
    rw [AlgHom.map_adjoin]
    congr 1
    simp [hx']
  let e : ↥(Algebra.adjoin ℚ ({x'} : Set ↥B)) ≃ₐ[ℚ] ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) :=
    (Subalgebra.equivMapOfInjective _ B.val Subtype.val_injective).trans
      (Subalgebra.equivOfEq _ _ hmap)
  have : Algebra.IsAlgebraic ↥(Algebra.adjoin ℚ ({x'} : Set ↥B)) ↥B := by
    constructor
    intro y
    refine IsAlgebraic.of_ringHom_of_comp_eq (f := (e : _ →+* _))
      (g := (B.val : ↥B →+* ℂ)) (halg y y.2) e.surjective Subtype.val_injective ?_
    ext c
    rfl
  simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ ({x'} : Set ↥B)

/-- The geometric triple `w = πi`, `z = -πi`: here `wz = π²` and `wz² = -iπ³`, and
`e^{πi} = -1` is algebraic. -/
theorem solution :
    Transcendental ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2)) ∨
      Transcendental ℚ (Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ) ^ 3)) := by
  by_contra h
  simp only [not_or, Transcendental, not_not] at h
  obtain ⟨ha, hb⟩ := h
  set w : ℂ := ((Real.pi : ℝ) : ℂ) * Complex.I with hw_def
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hw : w ≠ 0 := mul_ne_zero hπ Complex.I_ne_zero
  have hz : ∀ q : ℚ, -w ≠ (q : ℂ) := by
    intro q hq
    have := congrArg Complex.im hq
    simp [hw_def] at this
  -- transcendence degree: `-w` lies in `ℚ[w]`
  have htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({w, -w} : Set ℂ)) ≤ 1 := by
    have hle : Algebra.adjoin ℚ ({w, -w} : Set ℂ) ≤ Algebra.adjoin ℚ ({w} : Set ℂ) := by
      rw [Algebra.adjoin_le_iff]
      rintro y (rfl | rfl)
      · exact Algebra.subset_adjoin rfl
      · exact neg_mem (Algebra.subset_adjoin rfl)
    refine pisq_trdeg_le_one_of_adjoin_singleton (x := w) (Algebra.subset_adjoin (by simp)) ?_
    intro y hy
    have hy' : y ∈ Algebra.adjoin ℚ ({w} : Set ℂ) := hle hy
    have : y = algebraMap ↥(Algebra.adjoin ℚ ({w} : Set ℂ)) ℂ ⟨y, hy'⟩ := rfl
    rw [this]
    exact isAlgebraic_algebraMap _
  have e1 : IsAlgebraic ℚ (Complex.exp w) := by
    rw [hw_def, Complex.exp_pi_mul_I]
    exact (isAlgebraic_one (R := ℚ) (A := ℂ)).neg
  have e2 : IsAlgebraic ℚ (Complex.exp (w * -w)) := by
    have : w * -w = ((Real.pi : ℝ) : ℂ) ^ 2 := by
      rw [hw_def]
      linear_combination (-((Real.pi : ℝ) : ℂ) ^ 2) * Complex.I_sq
    rw [this]; exact ha
  have e3 : IsAlgebraic ℚ (Complex.exp (w * (-w) ^ 2)) := by
    have : w * (-w) ^ 2 = -(Complex.I * ((Real.pi : ℝ) : ℂ) ^ 3) := by
      rw [hw_def]
      linear_combination (((Real.pi : ℝ) : ℂ) ^ 3 * Complex.I) * Complex.I_sq
    rw [this, Complex.exp_neg]
    exact hb.inv
  exact DiazModulus.geometric_triple_not_logs w (-w) hw hz htr ⟨e1, e2, e3⟩

#print axioms solution
