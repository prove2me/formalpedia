-- Prove2me | solution 1 for Formalism.mxS_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:11.538086+00:00
-- url     : https://prove2.me/submissions/a4933afe-48aa-4562-9ce8-0950198ea49f

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSAux

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
namespace Formalism
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    mxS n x = (Ioi (n : ℝ)).indicator (fun x => x / n - 1) x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  show max (x / n - 1) 0 = _
  by_cases hx : x ∈ Ioi (n : ℝ)
  · rw [Set.indicator_of_mem hx]
    have h1 : 1 ≤ x / n := by
      rw [le_div_iff₀ hn0]
      have := Set.mem_Ioi.mp hx
      linarith
    exact max_eq_left (sub_nonneg.mpr h1)
  · rw [Set.indicator_of_notMem hx]
    have h1 : x / n ≤ 1 := (div_le_one hn0).mpr (le_of_not_gt (fun h => hx (Set.mem_Ioi.mpr h)))
    exact max_eq_right (sub_nonpos.mpr h1)
end Formalism
