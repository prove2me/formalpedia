-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x2.parsevalGroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:01.750773+00:00
-- url     : https://prove2.me/submissions/be4411e7-7847-4cc8-8868-01c54974ad8a

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PosSemidefEntryBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x2_sum_addChar_norm_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x2
namespace Formalism.FourierDecayAlt.P.A6x2
theorem _root_.solution : ParsevalGroup := by
  intro E _ _ G _ _ v
  classical
  rw [finsum_eq_sum_of_fintype]
  have hN : (Fintype.card G : ℝ) ≠ 0 := by
    have : 0 < Fintype.card G := Fintype.card_pos_iff.2 ⟨0⟩
    positivity
  have h1 : ∀ χ : AddChar G ℂ, ‖(Fintype.card G : ℂ)⁻¹ • ∑ g, χ (-g) • v g‖ ^ 2 =
      ((Fintype.card G : ℝ)⁻¹) ^ 2 * ‖∑ g, χ (-g) • v g‖ ^ 2 := by
    intro χ
    rw [norm_smul, mul_pow, norm_inv, Complex.norm_natCast]
  simp_rw [h1]
  rw [← Finset.mul_sum, sum_addChar_norm_sq]
  field_simp
end Formalism.FourierDecayAlt.P.A6x2
