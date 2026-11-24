-- Prove2me | solution 1 for Formalism.HF.P.summable_F
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:11.661933+00:00
-- url     : https://prove2.me/submissions/582ae79b-cc1f-490c-8162-5283dbac03f8

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution (S : Set ℕ) {x : ℝ} (hx : 1 < x) :
    Summable (fun n : ℕ => {p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => 1 / (m : ℝ) ^ x) n) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (Real.summable_nat_rpow_inv.2 hx)
  · exact Set.indicator_nonneg (fun m _ => by positivity) n
  · calc _ ≤ 1 / (n:ℝ) ^ x := Set.indicator_le_self' (fun m _ => by positivity) n
      _ = _ := one_div _
end Formalism.HF.P
