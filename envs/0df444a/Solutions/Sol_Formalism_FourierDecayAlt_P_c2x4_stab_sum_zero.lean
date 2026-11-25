-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c2x4_stab_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:57:09.353922+00:00
-- url     : https://prove2.me/submissions/fa8efcd3-fddb-440f-b9e0-b3024ac7f6ec

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x4_simpleLow_double
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x4_simpleUp_double
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_c2x4_ut_inv_super__b4a875ff4b5b
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_isUnit_det_monomialMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_monomialMatrix_conj_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_inv_super
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_unit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution {m : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (hC : Cond w d) (l u' : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ C2.LTset m) (hu : u' ∈ C2.UTset m)
    (he : l * C2.monoP w d * u' = C2.monoP w d) : C2.simpleLow l + C2.simpleUp u' = 0 := by
  have hPu := C2x2.isUnit_det_monomialMatrix w d hd
  have hinv : (C2.monoP w d)⁻¹ * l * C2.monoP w d = u'⁻¹ := by
    calc (C2.monoP w d)⁻¹ * l * C2.monoP w d
        = (C2.monoP w d)⁻¹ * l * C2.monoP w d * (u' * u'⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ (C2x2.ut_unit hu), Matrix.mul_one]
      _ = (C2.monoP w d)⁻¹ * (l * C2.monoP w d * u') * u'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = u'⁻¹ := by rw [he, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul]
  have hent : ∀ a b : Fin m, l (w a) (w b) = d a * u'⁻¹ a b / d b := by
    intro a b
    have := congrFun (congrFun hinv a) b
    rw [C2x2.monomialMatrix_conj_apply w d hd] at this
    rw [← this]; field_simp [hd a, hd b]
  have hui := C2x2.ut_inv hu
  rw [c2x4_simpleLow_double, c2x4_simpleUp_double]
  rw [← Equiv.sum_comp w]
  simp_rw [← Equiv.sum_comp w (fun q => if (w _).val = q.val + 1 then l (w _) q else 0)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro b _
  by_cases h1 : b.val = a.val + 1
  · have hab : a < b := by rw [Fin.lt_def]; omega
    have hsup := C2x2.ut_inv_super hu a (by omega)
    have hbe : b = ⟨a.val + 1, by omega⟩ := Fin.ext h1
    by_cases h2 : (w a).val = (w b).val + 1
    · have hwab : w b < w a := by rw [Fin.lt_def]; omega
      have hda := (hC a b hab hwab).2 h1
      rw [if_pos h2, if_pos h1, hent, hda]
      have e : d b * u'⁻¹ a b / d b = u'⁻¹ a b := by field_simp [hd b]
      rw [e, c2x4_ut_inv_super' hu a b h1]; ring
    · rw [if_neg h2, if_pos h1, zero_add]
      have hwab : w a < w b := by
        rcases lt_or_gt_of_ne (fun e : w a = w b => (ne_of_lt hab) (w.injective e)) with h | h
        · exact h
        · exact absurd ((hC a b hab h).1.mp h1) h2
      have hz := hl.1 (w a) (w b) hwab
      rw [hent] at hz
      have : u'⁻¹ a b = 0 := by
        rcases mul_eq_zero.mp (div_eq_zero_iff.mp hz |>.resolve_right (hd b)) with h | h
        · exact absurd h (hd a)
        · exact h
      rw [c2x4_ut_inv_super' hu a b h1, neg_eq_zero] at this
      exact this
  · rw [if_neg h1, add_zero]
    by_cases h2 : (w a).val = (w b).val + 1
    · rw [if_pos h2, hent]
      rcases lt_trichotomy a b with h | rfl | h
      · have hwab : w b < w a := by rw [Fin.lt_def]; omega
        exact absurd ((hC a b h hwab).1.mpr h2) h1
      · omega
      · rw [hui.1 a b h]; simp
    · rw [if_neg h2]
end Formalism.FourierDecayAlt.P
