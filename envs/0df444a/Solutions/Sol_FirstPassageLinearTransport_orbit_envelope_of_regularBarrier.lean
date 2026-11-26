-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_envelope_of_regularBarrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:16.923256+00:00
-- url     : https://prove2.me/submissions/9c0f4ed4-ede3-45cc-8b50-dc7dc4b7506a

import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_normalizedCorrection_scaled_le_maximal
import Theorems.Thm_FirstPassageLinearTransport_orbit_lower_of_fixed_barrier
import Theorems.Thm_FirstPassageLinearTransport_orbit_upper_of_fixed_barrier
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n k M : ℕ} {h t : ℝ}
    (hkM : k ≤ M) (hnShell : n ∈ dyadicShell M)
    (hreg : MaximalParityRegular n M h)
    (hphase : (3 : ℝ) ^ h ≤ (n : ℝ) ^ t)
    (hphaseTwo : 2 * (3 : ℝ) ^ h ≤ (n : ℝ) ^ t)
    (hcorrAbsorb :
      2 * ((2 + Real.sqrt 3) * (3 : ℝ) ^ h * (3 : ℝ) ^ h) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t)) :
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ (orbit k n : ℝ) ∧
      (orbit k n : ℝ) ≤ centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
  have hnPos : 0 < n := by
    have hp : 0 < 2 ^ M := by positivity
    exact lt_of_lt_of_le hp (mem_dyadicShell.mp hnShell).1
  have hbounds := hreg k hkM
  have hSlo : (k : ℝ) / 2 - h ≤ oddCount n k := by
    have := (abs_le.mp hbounds).1
    linarith
  have hShi : (oddCount n k : ℝ) ≤ (k : ℝ) / 2 + h := by
    have := (abs_le.mp hbounds).2
    linarith
  have hcorr := normalizedCorrection_scaled_le_maximal
    (n := n) (M := M) (k := k) (h := h) hkM hreg
  exact ⟨orbit_lower_of_fixed_barrier hnPos hSlo hphase,
    orbit_upper_of_fixed_barrier hnPos hShi hphaseTwo hcorr hcorrAbsorb⟩
end FirstPassageLinearTransport
