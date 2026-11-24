-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.gl_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:28:59.290809+00:00
-- url     : https://prove2.me/submissions/86c2a259-c795-42f4-82a1-06cb81cf6f1f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z5
open Formalism.MainNotions.S PIW.AdelClassFin Formalism.L2.SG.Pf.LatDictZ
variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.L2.SG.Pf.LatDictZ.Z5
theorem _root_.solution (s : Finset ι) (e : ι → R) (M : Matrix n n R) (A : ι → Matrix n n R) (y : n → R) :
    gl s e M A *ᵥ y = M *ᵥ y + ∑ i ∈ s, e i • ((A i - M) *ᵥ y) := by
  unfold gl
  rw [Matrix.add_mulVec]
  congr 1
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Matrix.add_mulVec, ih, Matrix.smul_mulVec]
end Formalism.L2.SG.Pf.LatDictZ.Z5
