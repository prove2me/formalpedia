-- Prove2me | solution 1 for CompanionTheory.WaveGrid.Inhab.int_of_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:10:02.058329+00:00
-- url     : https://prove2.me/submissions/9a25d464-0024-449c-8773-45ed0c9e09b3

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqOfLamData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid CompanionTheory.WaveGrid.Inhab
open Formalism.FourierDecayAlt Finset CompanionTheory.WaveGrid GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
namespace CompanionTheory.WaveGrid.Inhab
theorem _root_.solution {k : ℕ} {u v : ℕ → ℝ} (hk : 1 ≤ k)
    (hu : ∀ i, 1 ≤ i → i ≤ k → ∃ m : ℤ, u i - ((k : ℝ) - 1) / 2 = m)
    (hv : ∀ i, 1 ≤ i → i ≤ k → ∃ m : ℤ, v i - ((k : ℝ) - 1) / 2 = m) :
    ∀ i ∈ Icc 1 k, ∃ n : ℤ, v i - u 1 = n := by
  intro i hi
  obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
  obtain ⟨m1, hm1⟩ := hu 1 le_rfl hk
  obtain ⟨m2, hm2⟩ := hv i hi1 hik
  exact ⟨m2 - m1, by push_cast; linarith⟩
end CompanionTheory.WaveGrid.Inhab
