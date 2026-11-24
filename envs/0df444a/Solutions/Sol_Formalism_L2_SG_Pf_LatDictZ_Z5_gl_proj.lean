-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.gl_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:51:53.549252+00:00
-- url     : https://prove2.me/submissions/2a09b383-f0ce-47d0-93d3-3c22feb3381e

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
theorem _root_.solution {s : Finset ι} {e : ι → R} (he : Orth s e) (M : Matrix n n R) (A : ι → Matrix n n R)
    (y : n → R) {j : ι} (hj : j ∈ s) : e j • (gl s e M A *ᵥ y) = e j • (A j *ᵥ y) := by
  rw [gl_mulVec, smul_add, Finset.smul_sum]
  have h : ∑ i ∈ s, e j • e i • ((A i - M) *ᵥ y) = e j • ((A j - M) *ᵥ y) := by
    rw [Finset.sum_eq_single j]
    · rw [smul_smul, he j hj j hj, if_pos rfl]
    · intro b hb hbj
      rw [smul_smul, he j hj b hb, if_neg (Ne.symm hbj), zero_smul]
    · intro h
      exact absurd hj h
  rw [h, ← smul_add, Matrix.sub_mulVec]
  congr 1
  abel
end Formalism.L2.SG.Pf.LatDictZ.Z5
