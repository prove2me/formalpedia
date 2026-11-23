-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NthRootMeasurability.real_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:07.823797+00:00
-- url     : https://prove2.me/submissions/5abe987f-ab29-46f2-8941-3418f6bd5153

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NthRootMeasurability
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.NthRootMeasurability
theorem _root_.solution (s M : ℕ) (hs : 1 ≤ s) (hM : 2 ≤ M) (t z : ℂ) (ht : t ≠ 0) (hz : z ≠ 0) :
    ‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 *
      (‖t‖ ^ (2 * (s - 1) * (M + s - 2)) *
        ‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * z ^ s‖ ^ (2 * (M - 2)) /
          (‖t‖ ^ (2 * (s - 1) ^ 2) * (s : ℝ) ^ 2)) * ‖z‖ ^ (2 * (s - 1) ^ 2) =
      ‖z‖ ^ (2 * s * (M + s - 3)) := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 2 := ⟨M - 2, by omega⟩
  rw [show s' + 1 - 1 = s' by omega, show M' + 2 + (s' + 1) - 2 = M' + s' + 1 by omega,
    show M' + 2 - 2 = M' by omega, show M' + 2 + (s' + 1) - 3 = M' + s' by omega]
  simp only [norm_mul, norm_inv, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast]
  have hT : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hR : 0 < ‖z‖ := norm_pos_iff.mpr hz
  generalize ‖t‖ = T at hT ⊢
  generalize ‖z‖ = ρ at hR ⊢
  push_cast
  simp only [inv_pow, mul_pow, ← pow_mul]
  field_simp
  ring
end Formalism.FourierDecayAlt.P.NthRootMeasurability
