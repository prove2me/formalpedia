-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.separated_set_sum_bound_of_disjoint_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:18.27628+00:00
-- url     : https://prove2.me/submissions/c6685924-b129-4d01-8c65-17092a24e8b8

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_separated_sum_le_prod_integrals

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hd : SeparatedPolydiscsDisjoint) (hi : InversePowerIntegralPi) : SeparatedSetSumBound := by
  intro ι _ ro S hro hro1 hS
  have h := separated_sum_le_prod_integrals hd ro S hro hS (fun _ z => ((1 + ‖z‖ ^ 2) ^ 2)⁻¹)
    (fun _ x => 4 * ((1 + ‖x‖ ^ 2) ^ 2)⁻¹)
    (fun _ _ => by positivity) (fun _ _ => by positivity) (fun _ => hi.1.const_mul 4) ?_
  · simp only [integral_const_mul, hi.2, Finset.prod_const, Finset.card_univ] at h
    have hV : 0 < (π * (ro / 2) ^ 2) ^ Fintype.card ι := by positivity
    rw [← le_div_iff₀ hV, ← div_pow] at h
    have : 4 * π / (π * (ro / 2) ^ 2) = 16 / ro ^ 2 := by field_simp; ring
    rwa [this] at h
  · intro _ D x hx
    have h1 : ‖x‖ ≤ ‖D‖ + 1 / 2 := by
      have := norm_le_norm_add_norm_sub' x D
      linarith
    have h2 : 1 + ‖x‖ ^ 2 ≤ 2 * (1 + ‖D‖ ^ 2) := by
      nlinarith [norm_nonneg x, norm_nonneg D, sq_nonneg (‖D‖ - 1 / 2)]
    have h3 : (1 + ‖x‖ ^ 2) ^ 2 ≤ 4 * (1 + ‖D‖ ^ 2) ^ 2 := by
      calc (1 + ‖x‖ ^ 2) ^ 2 ≤ (2 * (1 + ‖D‖ ^ 2)) ^ 2 := by gcongr
        _ = 4 * (1 + ‖D‖ ^ 2) ^ 2 := by ring
    show ((1 + ‖D‖ ^ 2) ^ 2)⁻¹ ≤ 4 * ((1 + ‖x‖ ^ 2) ^ 2)⁻¹
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
end Formalism.HermitianLatticeCounting.P
