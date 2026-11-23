-- Prove2me | solution 1 for Bl.general_b_fact_right.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:00.54283+00:00
-- url     : https://prove2.me/submissions/c55c9de5-aaf9-435c-925c-fa659630e35f

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRight_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Bl Bl.general_b_fact_right
namespace Bl.general_b_fact_right
theorem _root_.solution {V ι : Type*} [AddCommGroup V] [Module ℂ V] (L : List ι) (F : ι → Module.End ℂ V)
    (c : ι → ℂ) (x : V) (hL : ∀ j ∈ L, F j x = c j • x) : (L.map F).prod x = (L.map c).prod • x := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have h1 : ∀ j ∈ L, F j x = c j • x := fun j hj => hL j (List.mem_cons_of_mem a hj)
    have h2 : F a x = c a • x := hL a (by simp)
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [ih h1, map_smul, h2, smul_smul, mul_comm]
end Bl.general_b_fact_right
