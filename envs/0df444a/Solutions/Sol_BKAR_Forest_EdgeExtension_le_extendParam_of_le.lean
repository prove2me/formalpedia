-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.le_extendParam_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:37:17.69248+00:00
-- url     : https://prove2.me/submissions/a18e7c25-72eb-4eb7-91c8-b9532d90a7b9

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
import Theorems.Thm_BKAR_Forest_EdgeExtension_le_extendParam


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution (h : EdgeExtension F F' e)
    (u : F.EdgeParam → ℝ) {s top : ℝ}
    (hst : s ≤ top) (hu : ∀ e : F.EdgeParam, top ≤ u e)
    (e' : F'.EdgeParam) :
    s ≤ h.extendParam u s e' :=
  h.le_extendParam u (fun e => hst.trans (hu e)) e'
end BKAR.Forest.EdgeExtension
