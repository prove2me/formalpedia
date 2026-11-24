-- Prove2me | solution 1 for Formalism.L2.Th1.D.KurUnram_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:14:38.071741+00:00
-- url     : https://prove2.me/submissions/e2cb204b-bfe9-4b87-a9f0-6fab6741c3c9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormRingALe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExistsUnitFactorizationBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Unram)
open UnramifiedCompletion
namespace Formalism.L2.Th1.D
theorem _root_.solution : KurIntegers → KurUnram := by
  intro hK l hl a ha h0
  obtain ⟨h1, hdiv, -⟩ := hK l
  have key : ∀ x ∈ ringB l, x ≠ 0 → ∃ k : ℕ, ‖x‖ = ‖(l : ℂ_[l])‖ ^ k := by
    intro x hx hx0
    obtain ⟨k, u, _, hu1, e⟩ := exists_unit hdiv hx hx0
    exact ⟨k, by rw [e, norm_mul, norm_pow, hu1, mul_one]⟩
  rcases le_total ‖a‖ 1 with h | h
  · obtain ⟨k, hk⟩ := key a ((h1 a).2 ⟨ha, h⟩) h0
    exact ⟨k, by rw [hk, zpow_natCast]⟩
  · have hi : ‖a⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ h
    obtain ⟨k, hk⟩ := key a⁻¹ ((h1 _).2 ⟨inv_mem ha, hi⟩) (inv_ne_zero h0)
    exact ⟨-k, by rw [zpow_neg, zpow_natCast, ← hk, norm_inv, inv_inv]⟩
end Formalism.L2.Th1.D
