-- Prove2me | solution 1 for CompanionTheory.WaveGrid.inter_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:49:57.915791+00:00
-- url     : https://prove2.me/submissions/17519ea5-349b-4434-88ff-02344cef616f

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
import Theorems.Thm_CompanionTheory_WaveGrid_lamN_succ
import Theorems.Thm_CompanionTheory_WaveGrid_half_le_of_pos

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
theorem _root_.solution {k r : ℕ} {lam : Fin (2 * r + k + 1) → ℝ} (hc : Formalism.QuantumDeterminants.IsHCParam lam) {u : ℕ → ℝ} {b : ℝ}
    (hu : HypType k r lam u b) (s : ℕ) (hs1 : 1 ≤ s) (hsk : s ≤ k - 1) :
    lamN lam s + 1 / 2 ≤ u s ∧ u (s + 1) ≤ lamN lam s - 1 / 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have ht : t < 2 * r + k + 1 := by omega
  have e : lamN lam (t + 1) = lam ⟨t, ht⟩ := lamN_succ lam ⟨t, ht⟩
  obtain ⟨h1, h2⟩ := hu.inter.2 ⟨t, by omega⟩
  have h1' : lam ⟨t, ht⟩ < u (t + 1) := h1 (by simp only; omega)
  have h2' : u (t + 2) < lam ⟨t, ht⟩ := h2 (by simp only; omega)
  obtain ⟨a, ha⟩ := hc.2 ⟨t, ht⟩
  obtain ⟨m1, hm1⟩ := hu.half (t + 1) (by omega) (by omega)
  obtain ⟨m2, hm2⟩ := hu.half (t + 2) (by omega) (by omega)
  push_cast at ha
  rw [e]
  have k1 := half_le_of_pos (x := u (t + 1) - lam ⟨t, ht⟩) (m1 - a - r - 1) (by push_cast; linarith) (by linarith)
  have k2 := half_le_of_pos (x := lam ⟨t, ht⟩ - u (t + 2)) (a + r - m2) (by push_cast; linarith) (by linarith)
  constructor <;> linarith
end CompanionTheory.WaveGrid
