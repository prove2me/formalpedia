-- Prove2me | solution 1 for Formalism.SA.P.nat_log_floor_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:34.642816+00:00
-- url     : https://prove2.me/submissions/642bb932-7c49-4b31-8007-69670a8f90c9

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open NumberField Finset
variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
namespace Formalism.SA.P
theorem _root_.solution (u : ℝ) (_hu : 0 ≤ u) : u < 2 ^ (Nat.log 2 ⌊u⌋₊ + 1) := by
  have h1 : ⌊u⌋₊ < 2 ^ (Nat.log 2 ⌊u⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : u < ⌊u⌋₊ + 1 := Nat.lt_floor_add_one u
  have h3 : ((⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 ⌊u⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h3
  linarith
end Formalism.SA.P
