-- Prove2me | solution 1 for CompanionTheory.WaveGrid.pairOK_of_moved
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:33:01.503613+00:00
-- url     : https://prove2.me/submissions/3c20eca2-b441-4a91-b344-b9a2a0caec30

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NQText
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
namespace CompanionTheory.WaveGrid
theorem _root_.solution (k l : ℕ) (lam u v : ℕ → ℝ) (x : ℝ)
    (h : ∀ s, 1 ≤ s → s ≤ k - 1 → lam s + 1 / 2 ≤ u s ∧ u (s + 1) ≤ lam s - 1 / 2)
    (hv : ∀ i, i ≠ l → v i = u i) (hx : (u l < x ∧ x < v l) ∨ (v l < x ∧ x < u l)) :
    ∃ e, PairOK k lam v e x := by
  rcases hx with ⟨h1, -⟩ | ⟨-, h2⟩
  · refine ⟨l - 1, fun s hs1 hsk hse => ⟨fun hlt => ?_, fun _ => ?_⟩⟩
    · have hsl : s ≠ l := by
        rintro rfl
        have := (h s hs1 hsk).1
        linarith
      rw [hv s hsl]
      exact (h s hs1 hsk).1
    · rw [hv (s + 1) (by omega)]
      exact (h s hs1 hsk).2
  · refine ⟨l, fun s hs1 hsk hse => ⟨fun _ => ?_, fun hle => ?_⟩⟩
    · rw [hv s hse]
      exact (h s hs1 hsk).1
    · have hsl : s + 1 ≠ l := by
        rintro rfl
        have := (h s hs1 hsk).2
        linarith
      rw [hv (s + 1) hsl]
      exact (h s hs1 hsk).2
end CompanionTheory.WaveGrid
