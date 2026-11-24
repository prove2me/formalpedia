-- Prove2me | solution 1 for Formalism.LT.InvIntP.funEqLowCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:49:23.500806+00:00
-- url     : https://prove2.me/submissions/6c2e187d-bfd5-40e8-8bef-1816e2910e5c

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Theorems.Thm_Formalism_LT_InvIntP_coeff_expand_low

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
open Formalism Formalism.LT Formalism.LT.InvIntP
open Formalism.G Formalism.G.LogCR
namespace Formalism.LT.InvIntP
theorem _root_.solution {K : Type u} [NormedField K] {ι : Type v} (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K) (hq2 : 2 ≤ q) (D : MvPowerSeries ι K) (hD : IsFunEqTypeMv p q hq σ D)
    (N : ℕ) (hN : 1 ≤ N) (hlow : ∀ d : ι →₀ ℕ, d.degree < N → MvPowerSeries.coeff d D = 0)
    (d : ι →₀ ℕ) (hd : d.degree = N) : ‖MvPowerSeries.coeff d D‖ ≤ 1 := by
  have h := hD d
  rwa [map_sub, map_smul, coeff_expand_low q hq hq2 σ D N hN hlow d hd, smul_zero, sub_zero] at h
end Formalism.LT.InvIntP
