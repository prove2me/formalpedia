-- Prove2me | solution 1 for FD1D.DyadicMass.succNode_natAdd_eq_rightNode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:50.044557+00:00
-- url     : https://prove2.me/submissions/becc17f3-d407-4d47-b4c7-296fb5f42488

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
    (⟨d.succ, childFinEquiv d.val (Fin.natAdd (2 ^ d.val) v)⟩ :
      CompleteHaarNode (L + 1)) = rightNode ⟨d, v⟩ := by
  rfl
end FD1D.DyadicMass
