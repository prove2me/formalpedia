-- Prove2me | solution 1 for Erdos287.asymmetric_chen_coefficients_below_dense_occupancy_threshold
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-27T00:58:21.496127+00:00
-- url     : https://prove2.me/submissions/f8c9f41a-4201-42a0-baf4-2a0a9568f243

import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

/-- Rational enclosures for the three Chen terms with separate levels for
the two unswitched terms and the switched convolution. -/
theorem solution :
    let upper (θ τ a b : ℚ) :=
      let c : ℚ := 709 / 1250
      let d := (1 - b) / (2 + 1 / c)
      let dx := (θ / a - 3) / 1024
      let dt := (b - a) / 1024
      let scale : ℚ := 10 ^ 12
      let z (y : ℚ) := (y - 1) / (y + 1)
      let lowerLog (y : ℚ) :=
        2 * ∑ j ∈ Finset.range 7, z y ^ (2 * j + 1) / (2 * (j : ℚ) + 1)
      let upperLog (y : ℚ) := lowerLog y + 2 * z y ^ 15 / (15 * (1 - (z y) ^ 2))
      let firstUpper :=
        2 / θ + (↑(∑ i ∈ Finset.range 1024,
          let x := 1 + ((i : ℚ) + 1) * dx
          ⌈scale * (2 / θ) * dx * upperLog x / (x + 1)⌉) : ℚ) / scale
      let secondLower :=
        (↑(∑ i ∈ Finset.range 1024,
          let t := a + ((i : ℚ) + 1) * dt
          ⌊scale * dt * lowerLog ((θ - t) / a - 1) / ((θ - t) * t)⌋) : ℚ) / scale
      let thirdUpper :=
        ((2 * c / a) * ((1 + a / b) * upperLog (b / a) - 2 * (1 - a / b)) +
          (1 + 2 * c) * upperLog (b / a) * (b - d) ^ 3 /
            (3 * (1 - 3 * b) * d ^ 3)) / (2 * τ)
      firstUpper - secondLower + thirdUpper
    upper (2127 / 4000) (1 / 2) (569 / 4000) (877 / 4000) < 37167 / 10000 ∧
    upper (17 / 32) (103 / 200) (353 / 2500) (551 / 2500) < 37176 / 10000 ∧
    (37167 / 10000 : ℚ) + 1 / 1000 < 145 / 39 ∧
    (37176 / 10000 : ℚ) + 1 / 4000 < 145 / 39 ∧
    (106 / 39 : ℚ) < 1359 / 500 ∧
    (1359 / 500 : ℚ) < ∑ i ∈ Finset.range 7, 1 / (Nat.factorial i : ℚ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num
  · norm_num
  · decide +kernel

