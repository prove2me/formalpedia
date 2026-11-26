-- Prove2me | solution 1 for Erdos266.pSum_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:18:55.257716+00:00
-- url     : https://prove2.me/submissions/af6396c9-2bc6-41da-961b-fc0acc84e270

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_cnt_mono
public import Theorems.Thm_Erdos266_kOf_spec
public import Theorems.Thm_Erdos266_cnt_kOf_le
public import Theorems.Thm_Erdos266_le_kOf_of_cnt_le
public import Theorems.Thm_Erdos266_finSum_tendsto
public import Theorems.Thm_Erdos266_pSum_regroup
public import Theorems.Thm_Erdos266_pSum_mono
public import Theorems.Thm_Erdos266_kOf_tendsto

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution (i' : ℕ) :
    Tendsto (fun n => pSum i' n) atTop (𝓝 ((xinf i' : ℚ) : ℝ)) := by
  have hL : Tendsto (fun n => finSum i' (kOf n) Sinf) atTop (𝓝 ((xinf i' : ℚ) : ℝ)) :=
    (finSum_tendsto i').comp kOf_tendsto
  have hU : Tendsto (fun n => finSum i' (kOf n + 1) Sinf) atTop (𝓝 ((xinf i' : ℚ) : ℝ)) :=
    (finSum_tendsto i').comp ((tendsto_add_atTop_nat 1).comp kOf_tendsto)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · rw [eventually_atTop]
    refine ⟨cnt (4 * i' + 4), fun n hn => ?_⟩
    rw [← pSum_regroup]
    refine pSum_mono ?_ (cnt_kOf_le n)
    exact cnt_mono (le_kOf_of_cnt_le hn)
  · rw [eventually_atTop]
    refine ⟨cnt (4 * i' + 4), fun n hn => ?_⟩
    rw [← pSum_regroup]
    refine pSum_mono hn ?_
    exact (kOf_spec n).le
end Erdos266
