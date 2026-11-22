-- Prove2me | solution 1 for Comp.CsgQ.toPMF_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:53:52.443254+00:00
-- url     : https://prove2.me/submissions/b5ef4550-1343-4a94-8a4e-8dc0f597ffde

import Definitions.Def_Comp_Basic
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Qualitative

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) :
    (G.toPMF h s a1 a2).support = G.supportQ s a1 a2 := by
  ext s'
  have happ : G.toPMF h s a1 a2 s' = ENNReal.ofReal ((G.K s a1 a2 s' : ℚ) : ℝ) := by
    unfold toPMF
    rw [PMF.ofFintype_apply]
  have hnn : (0 : ℚ) ≤ G.K s a1 a2 s' := h.1 s a1 a2 s'
  simp only [PMF.mem_support_iff, supportQ, Set.mem_setOf_eq, happ, ne_eq,
    ENNReal.ofReal_eq_zero, not_le]
  constructor
  · intro hpos
    have hq : (0 : ℚ) < G.K s a1 a2 s' := by exact_mod_cast hpos
    exact hq.ne'
  · intro hne
    have hq : (0 : ℚ) < G.K s a1 a2 s' := lt_of_le_of_ne hnn (Ne.symm hne)
    exact_mod_cast hq
end Comp.CsgQ
