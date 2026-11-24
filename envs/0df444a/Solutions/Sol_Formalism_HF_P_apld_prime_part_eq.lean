-- Prove2me | solution 1 for Formalism.HF.P.apld_prime_part_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:58.592189+00:00
-- url     : https://prove2.me/submissions/976811d4-c8bc-4aa0-a6f5-45b2a3b1f853

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt Complex LSeries
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
variable {q : ℕ} [NeZero q] {a : ZMod q}
namespace Formalism.HF.P
theorem _root_.solution (a : ZMod q) (x : ℝ) (n : ℕ) :
    (if n.Prime then residueClass a n else 0) / (n : ℝ) ^ x =
      {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n := by
  by_cases hp : n.Prime
  · by_cases hn : (n : ZMod q) = a
    · have hmem : n ∈ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}} := ⟨hp, hn⟩
      rw [if_pos hp, Set.indicator_of_mem hmem]
      simp [residueClass, Set.indicator, hn, vonMangoldt_apply_prime hp]
    · have hmem : n ∉ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}} := fun h => hn h.2
      rw [if_pos hp, Set.indicator_of_notMem hmem]
      simp [residueClass, Set.indicator, hn]
  · have hmem : n ∉ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}} := fun h => hp h.1
    rw [if_neg hp, Set.indicator_of_notMem hmem, zero_div]
end Formalism.HF.P
