-- Prove2me | solution 1 for FD1D.DyadicMass.succNode_castAdd_eq_leftNode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:46.908157+00:00
-- url     : https://prove2.me/submissions/6b3f9bbc-d6fd-4b2a-a9c7-9ab6859f9e0f

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution {L : ℕ} (d : Fin L)
    (v : Fin (2 ^ d.val)) :
    (⟨d.succ, childFinEquiv d.val (Fin.castAdd (2 ^ d.val) v)⟩ :
      CompleteHaarNode (L + 1)) = leftNode ⟨d, v⟩ := by
  rfl
end FD1D.DyadicMass
