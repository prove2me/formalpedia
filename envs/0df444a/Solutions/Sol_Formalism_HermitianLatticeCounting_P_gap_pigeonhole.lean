-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gap_pigeonhole
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:21.089155+00:00
-- url     : https://prove2.me/submissions/7e9680d2-4f22-40fe-83c7-0b78bb352781

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : GapPigeonhole := by
  intro a q τ ha haq hτ hlast h1
  by_contra hcon
  push Not at hcon
  have hq0 : q ≠ 0 := by omega
  have hx0 : 0 < (2 * τ 1) ^ ((1:ℝ) / q) := Real.rpow_pos_of_pos (by have := hτ 1; linarith) _
  have hx1 : (2 * τ 1) ^ ((1:ℝ) / q) ≤ 1 :=
    Real.rpow_le_one (by have := hτ 1; linarith) (by linarith) (by positivity)
  have hxq : ((2 * τ 1) ^ ((1:ℝ) / q)) ^ q = 2 * τ 1 := by
    rw [one_div]
    exact Real.rpow_inv_natCast_pow (by have := hτ 1; linarith) hq0
  generalize (2 * τ 1) ^ ((1:ℝ) / q) = x at *
  have key : ∀ k, 1 ≤ k → k ≤ a → x ^ k * τ (k + 1) < τ 1 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro _
      have := hcon 1 le_rfl ha
      rw [lt_div_iff₀ (hτ _)] at this
      simpa using this
    | succ k hk ih =>
      intro hka
      have h2 := hcon (k + 1) (by omega) hka
      rw [lt_div_iff₀ (hτ _)] at h2
      have h3 := ih (by omega)
      calc x ^ (k + 1) * τ (k + 1 + 1) = x ^ k * (x * τ (k + 1 + 1)) := by ring
        _ ≤ x ^ k * τ (k + 1) := by gcongr
        _ < τ 1 := h3
  have h4 := key a ha le_rfl
  rw [hlast] at h4
  have h5 : x ^ q ≤ x ^ a := pow_le_pow_of_le_one hx0.le hx1 haq
  linarith
end Formalism.HermitianLatticeCounting.P
