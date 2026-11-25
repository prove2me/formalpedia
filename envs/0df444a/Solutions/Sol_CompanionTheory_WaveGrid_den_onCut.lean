-- Prove2me | solution 1 for CompanionTheory.WaveGrid.den_onCut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:14:14.888382+00:00
-- url     : https://prove2.me/submissions/bd32ce03-221e-4dea-bd77-3225322d427c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_QwBound
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PstMul
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NQText
import Theorems.Thm_CompanionTheory_WaveGrid_den_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_interlaces_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset
namespace CompanionTheory.WaveGrid
theorem _root_.solution (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : I.Interlaces k u u' ρ) (hc : I.OnCut u u' l Y) :
    ∀ i, 1 ≤ i → i ≤ k → 1 ≤ |Y + 1 / 2 + u i| ∧ 1 ≤ |Y + 1 / 2 + u' i| := by
  rcases hc with hA | hB
  · exact den_core k u u' ρ l Y hl1 hlk h hA
  · intro i hi1 hik
    exact (den_core k u' u ρ l Y hl1 hlk (Formalism.FourierDecayAlt.P.Interlace.interlaces_swap h) hB i hi1 hik).symm
end CompanionTheory.WaveGrid
