-- Prove2me | solution 1 for FirstPassageLinearTransport.TimeoutRecertificationRun.shortcut_raw_le_relative_height
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:23:53.389866+00:00
-- url     : https://prove2.me/submissions/a347e4ad-98e3-4cec-937e-fcc584986a85

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_orbit_le_half_relative_height
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_le_two_mul_of_shortcut_prefix_le


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
namespace TimeoutRecertificationRun
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ R : ℝ}
    {L M S n elapsed q : ℕ}
    (hR : 4 ≤ R)
    (hcontract : (P.rHi : ℝ) * (1 + P.tau) ≤ 1)
    (hLowMargin : 2 * S ≤ M)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q)
    (hnShell : n ∈ dyadicShell M)
    (hnMax : n ∉ shellMultiplicativeHit M (R / 4)) :
    (∀ j : ℕ, j ≤ elapsed →
        (orbit j n : ℝ) ≤ (n : ℝ) * R / 2) ∧
      (∀ i : ℕ, i ≤ rawTime n elapsed →
        (rawOrbit i n : ℝ) ≤ (n : ℝ) * R) := by
  have hshortcut : ∀ j : ℕ, j ≤ elapsed →
      (orbit j n : ℝ) ≤ (n : ℝ) * R / 2 :=
    fun j hj => hrun.orbit_le_half_relative_height hR hcontract
      hLowMargin hnShell hnMax hj
  refine ⟨hshortcut, ?_⟩
  intro i hi
  have hraw := rawOrbit_le_two_mul_of_shortcut_prefix_le hshortcut i hi
  convert hraw using 1 <;> ring
end TimeoutRecertificationRun
end FirstPassageLinearTransport
