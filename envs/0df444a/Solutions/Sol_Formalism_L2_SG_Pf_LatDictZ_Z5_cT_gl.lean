-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.cT_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:00:46.223324+00:00
-- url     : https://prove2.me/submissions/54e39487-508c-4f67-a174-fb2534c90251

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
theorem _root_.solution (σ : R →+* R) {s : Finset ι} {e : ι → R} (hσ : ∀ i ∈ s, σ (e i) = e i) (M : Matrix n n R)
    (A : ι → Matrix n n R) :
    Formalism.UG.cT σ (gl s e M A) = gl s e (Formalism.UG.cT σ M) (fun i => Formalism.UG.cT σ (A i)) := by
  unfold gl Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.sub_apply, map_add, map_sum, map_mul, map_sub, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun k hk => by rw [hσ k hk]
end Formalism.L2.SG.Pf.LatDictZ.Z5
