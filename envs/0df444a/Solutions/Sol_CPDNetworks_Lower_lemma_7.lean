-- Prove2me | solution 1 for CPDNetworks.Lower.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:16:01.815993+00:00
-- url     : https://prove2.me/submissions/733ff742-06da-43ff-81a7-38708f04d616

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Lower_Setting
set_option autoImplicit false
open CPDNetworks.Lower

theorem solution (ρ q q₁ q₂ : ℝ) (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2)
    (hq : -1 ≤ q ∧ q ≤ 1) (hq₁ : -1 ≤ q₁ ∧ q₁ ≤ 1) (hq₂ : -1 ≤ q₂ ∧ q₂ ≤ 1) :
    ∑ x : Bool, bern ρ x * (bern (ρ * (1 + q)) x / bern ρ x) ^ 2 = 1 + ρ / (1 - ρ) * q ^ 2 ∧
    ∑ x : Bool, bern ρ x *
        (bern (ρ * (1 + q₁)) x / bern ρ x * (bern (ρ * (1 + q₂)) x / bern ρ x)) =
      1 + ρ / (1 - ρ) * (q₁ * q₂) := by
  have h1 : (1 - ρ) ≠ 0 := by intro h; linarith
  have h0 : ρ ≠ 0 := hρ.ne'
  constructor
  · simp only [Fintype.sum_bool, bern]
    simp only [if_true, Bool.false_eq_true, if_false]
    field_simp
    ring
  · simp only [Fintype.sum_bool, bern]
    simp only [if_true, Bool.false_eq_true, if_false]
    field_simp
    ring
