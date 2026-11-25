-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.unitOfNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:05:13.66747+00:00
-- url     : https://prove2.me/submissions/29b3c6d8-9de9-4172-963c-c7e8963ed158

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_maj_add_left
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_maj_add_right
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_maj_smul_left
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_maj_smul_right
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_maj_self
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_sesq_ext
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_exists_im_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open BlockMetrics
namespace Formalism.IndefR.LatticeTransfer
theorem _root_.solution : UnitOfNorm := by
  intro K _ _ _ _ G _ _ V _ _ _ _ ι _ _ b X ρ hn v g x y
  refine sesq_ext (F := fun x y => Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) (ρ g y))
    (G := Formalism.HermitianLatticesTheory.majAt b X v) (σ := v.embedding) (exists_im_ne_zero v)
    ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ?_ x y
  · intro x x' y; simp only [map_add]; exact maj_add_left b X v _ _ _
  · intro x y y'; simp only [map_add]; exact maj_add_right b X v _ _ _
  · intro a x y; simp only [map_smul]; exact maj_smul_left b X v _ _ _
  · intro a x y; simp only [map_smul]; exact maj_smul_right b X v _ _ _
  · exact fun x x' y => maj_add_left b X v _ _ _
  · exact fun x y y' => maj_add_right b X v _ _ _
  · exact fun a x y => maj_smul_left b X v _ _ _
  · exact fun a x y => maj_smul_right b X v _ _ _
  · intro z
    show Formalism.HermitianLatticesTheory.majAt b X v (ρ g z) (ρ g z) = Formalism.HermitianLatticesTheory.majAt b X v z z
    rw [maj_self, maj_self, hn]
end Formalism.IndefR.LatticeTransfer
