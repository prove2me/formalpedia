-- Prove2me | solution 1 for FirstPassageLinearTransport.initial_shortcut_raw_height_of_not_mem_shellMultiplicativeHit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:18:54.168974+00:00
-- url     : https://prove2.me/submissions/ae53fbcf-038c-474c-8054-b53069d35e87

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_orbit_lt_two_mul_of_not_mem_shellMultiplicativeHit
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_le_two_mul_of_shortcut_prefix_le

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M n : ℕ} {R : ℝ}
    (hn : n ∈ dyadicShell M)
    (hnGood : n ∉ shellMultiplicativeHit M (R / 4)) :
    (∀ j : ℕ, j ≤ M → (orbit j n : ℝ) < (n : ℝ) * R / 2) ∧
      (∀ i : ℕ, i ≤ rawTime n M →
        (rawOrbit i n : ℝ) ≤ (n : ℝ) * R) := by
  have hshortcut : ∀ j : ℕ, j ≤ M →
      (orbit j n : ℝ) < (n : ℝ) * R / 2 := by
    intro j hj
    have h := orbit_lt_two_mul_of_not_mem_shellMultiplicativeHit
      hn hnGood hj
    convert h using 1 <;> ring
  refine ⟨hshortcut, ?_⟩
  intro i hi
  have hle : ∀ j : ℕ, j ≤ M →
      (orbit j n : ℝ) ≤ (n : ℝ) * R / 2 :=
    fun j hj => (hshortcut j hj).le
  have hraw := rawOrbit_le_two_mul_of_shortcut_prefix_le hle i hi
  convert hraw using 1 <;> ring
end FirstPassageLinearTransport
