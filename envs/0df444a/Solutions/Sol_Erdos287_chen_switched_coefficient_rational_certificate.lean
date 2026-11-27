-- Prove2me | solution 1 for Erdos287.chen_switched_coefficient_rational_certificate
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T22:37:56.493589+00:00
-- url     : https://prove2.me/submissions/10e8fced-4738-4066-8f9c-2ec8a8f11e83

import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

/-- The rational enclosure used for the three Chen sieve terms at level 0.5499.
The logarithm bounds use seven terms of the odd-power series. The two
rectangle sums round each term outwards before summation. -/
theorem solution :
    let θ : ℚ := 5499 / 10000
    let a : ℚ := 29 / 200
    let b : ℚ := 183 / 800
    let c : ℚ := 709 / 1250
    let d := (1 - b) / (2 + 1 / c)
    let dx := (θ / a - 3) / 1024
    let dt := (b - a) / 1024
    let scale : ℚ := 10 ^ 12
    let z (y : ℚ) := (y - 1) / (y + 1)
    let lowerLog (y : ℚ) :=
      2 * ∑ j ∈ Finset.range 7, z y ^ (2 * j + 1) / (2 * (j : ℚ) + 1)
    let upperLog (y : ℚ) :=
      lowerLog y + 2 * z y ^ 15 / (15 * (1 - (z y) ^ 2))
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
          (3 * (1 - 3 * b) * d ^ 3)) / (2 * θ)
    firstUpper - secondLower + thirdUpper < 3587 / 1000 ∧
    (897 / 250 : ℚ) + 1 / 13 < 11 / 3 ∧
    (897 / 250 : ℚ) + 1 / 100 < 18 / 5 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · norm_num
  · norm_num

