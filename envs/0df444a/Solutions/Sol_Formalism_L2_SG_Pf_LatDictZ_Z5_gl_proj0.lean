-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.gl_proj0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:19:14.884918+00:00
-- url     : https://prove2.me/submissions/d5fc311a-a3a4-49bb-9ae4-758f32fb06d8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_gl_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z5
open Formalism.MainNotions.S PIW.AdelClassFin Formalism.L2.SG.Pf.LatDictZ
variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.L2.SG.Pf.LatDictZ.Z5
theorem _root_.solution {s : Finset ι} {e : ι → R} {f : R} (hf : ∀ i ∈ s, f * e i = 0) (M : Matrix n n R)
    (A : ι → Matrix n n R) (y : n → R) : f • (gl s e M A *ᵥ y) = f • (M *ᵥ y) := by
  rw [gl_mulVec, smul_add, Finset.smul_sum]
  have h : ∑ i ∈ s, f • e i • ((A i - M) *ᵥ y) = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [smul_smul, hf i hi, zero_smul]
  rw [h, add_zero]
end Formalism.L2.SG.Pf.LatDictZ.Z5
