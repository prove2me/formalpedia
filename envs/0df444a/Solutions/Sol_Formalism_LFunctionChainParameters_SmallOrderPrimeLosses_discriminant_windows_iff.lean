-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.discriminant_windows_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:30:45.191184+00:00
-- url     : https://prove2.me/submissions/c6c33165-5cdc-4ab7-b21a-82d231df7b47

import Definitions.Def_Formalism_SizeWindowBrackets_PrimeClassLossHypothesesSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DiscriminantSettingSatisfied

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
namespace Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
theorem _root_.solution : WindowsDIff := by
  intro P e K
  constructor
  · rintro ⟨hε, hε1, he, hK, nx, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
      ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, Co0, CoK, Y1, YX, bo0, bosb⟩
    have h0 : (0 : ℝ) ≤ (P.x ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
    have hβ : (0 : ℝ) ≤ K * (P.x ^ 2)⁻¹ := mul_nonneg (by linarith) h0
    exact ⟨hε, hε1, he, hK, nx, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
      ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, le_refl (0 : ℝ), hβ, Co0, CoK, Y1, YX, le_refl (0 : ℝ), h0, bo0, bosb⟩
  · rintro ⟨hε, hε1, he, hK, nx, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
      ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, -, -, Co0, CoK, Y1, YX, -, -, bo0, bosb⟩
    exact ⟨hε, hε1, he, hK, nx, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
      ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, Co0, CoK, Y1, YX, bo0, bosb⟩
end Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
