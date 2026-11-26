-- Prove2me | solution 1 for Erdos266.stepSt_snd_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:03:57.277127+00:00
-- url     : https://prove2.me/submissions/a4a9455e-076d-4354-a14e-1f9d347b0dfc

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_stepSt_eq


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {k : ℕ} {st : AlgSt} (h : Inv k st) {i : ℕ} (hi : i < dOf k) :
    (stepSt k st).2 i = st.2 i := by
  rw [stepSt_eq h]
  change (if dOf (k + 1) = dOf k + 1
      then Function.update st.2 (dOf k) (newQ k st h) else st.2) i = st.2 i
  split_ifs with hnew
  · exact Function.update_of_ne (by omega) _ _
  · rfl
end Erdos266
