-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.layerExists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:36.8858+00:00
-- url     : https://prove2.me/submissions/ea868277-23d3-409a-8fde-daed94f56838

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Polynomial
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : LayerExists := by
  intro n q d
  set f : ℚ[X] := cyclotomic (2 ^ n) ℚ * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ)) with hf
  let F := SplittingField f
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  have : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  have hmap' : ∀ φ : ℚ →+* F, f.map φ =
      cyclotomic (2 ^ n) F * (X ^ 2 + C (q : F)) * (X ^ 2 + C (d : F)) := by
    intro φ
    simp [f, map_cyclotomic, C_eq_natCast]
  have hmap := hmap' (algebraMap ℚ F)
  have hsp : Splits (f.map (algebraMap ℚ F)) := SplittingField.splits f
  rw [hmap] at hsp
  have hne : cyclotomic (2 ^ n) F * (X ^ 2 + C (q : F)) * (X ^ 2 + C (d : F)) ≠ 0 :=
    (((cyclotomic.monic _ F).mul (monic_X_pow_add_C _ two_ne_zero)).mul
      (monic_X_pow_add_C _ two_ne_zero)).ne_zero
  have hc : Splits (cyclotomic (2 ^ n) F) :=
    hsp.of_dvd hne (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
  have hqs : Splits (X ^ 2 + C (q : F)) :=
    hsp.of_dvd hne (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
  have hds : Splits (X ^ 2 + C (d : F)) := hsp.of_dvd hne (dvd_mul_left _ _)
  obtain ⟨ζ, hζ⟩ := hc.exists_eval_eq_zero (by
    rw [degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (by positivity)).ne')
  have hζp : IsPrimitiveRoot ζ (2 ^ n) := (isRoot_cyclotomic_iff_charZero (by positivity)).mp hζ
  obtain ⟨a, ha⟩ := hqs.exists_eval_eq_zero (by rw [degree_X_pow_add_C (by norm_num)]; norm_num)
  obtain ⟨b, hb⟩ := hds.exists_eval_eq_zero (by rw [degree_X_pow_add_C (by norm_num)]; norm_num)
  have ha2 : a ^ 2 = -(q : F) := by
    simp only [eval_add, eval_pow, eval_X, eval_C] at ha
    linear_combination ha
  have hb2 : b ^ 2 = -(d : F) := by
    simp only [eval_add, eval_pow, eval_X, eval_C] at hb
    linear_combination hb
  refine ⟨F, inferInstance, inferInstance, ζ, a, b, ?_⟩
  rw [show (DivisionRing.toRatAlgebra : Algebra ℚ F) = SplittingField.instAlgebra_1 f from
    Subsingleton.elim _ _]
  refine ⟨hζp, ha2, hb2, ?_⟩
  rw [← IntermediateField.toSubalgebra_inj, IntermediateField.adjoin_toSubalgebra,
    IntermediateField.top_toSubalgebra, eq_top_iff]
  refine (SplittingField.adjoin_rootSet f).symm.le.trans ?_
  rw [Algebra.adjoin_le_iff]
  intro x hx
  rw [mem_rootSet] at hx
  have hx' := hx.2
  rw [← eval_map_algebraMap, hmap'] at hx'
  simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C] at hx'
  rcases mul_eq_zero.mp hx' with hx' | hx'
  · rcases mul_eq_zero.mp hx' with hx' | hx'
    · have hxp : IsPrimitiveRoot x (2 ^ n) := (isRoot_cyclotomic_iff_charZero (by positivity)).mp hx'
      obtain ⟨i, -, hi⟩ := hζp.eq_pow_of_pow_eq_one hxp.pow_eq_one
      rw [← hi]
      exact pow_mem (Algebra.subset_adjoin (by simp)) i
    · have : x ^ 2 = a ^ 2 := by rw [ha2]; linear_combination hx'
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with rfl | rfl
      · exact Algebra.subset_adjoin (by simp)
      · exact neg_mem (Algebra.subset_adjoin (by simp))
  · have : x ^ 2 = b ^ 2 := by rw [hb2]; linear_combination hx'
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with rfl | rfl
    · exact Algebra.subset_adjoin (by simp)
    · exact neg_mem (Algebra.subset_adjoin (by simp))
end Formalism.TwoAdicCyclotomicDecomposition
