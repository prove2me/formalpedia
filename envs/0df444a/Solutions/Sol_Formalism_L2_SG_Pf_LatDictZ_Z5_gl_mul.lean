-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.gl_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:39:38.333981+00:00
-- url     : https://prove2.me/submissions/348f7b20-0a57-4c2f-89f6-b387fc3feefc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA

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
theorem _root_.solution {s : Finset ι} {e : ι → R} (he : Orth s e) (M N : Matrix n n R) (A B : ι → Matrix n n R) :
    gl s e M A * gl s e N B = gl s e (M * N) (fun i => A i * B i) := by
  unfold gl
  have h1 : (∑ i ∈ s, e i • (A i - M)) * (∑ j ∈ s, e j • (B j - N)) =
      ∑ i ∈ s, e i • ((A i - M) * (B i - N)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, he i hi i hi, if_pos rfl]
    · intro b hb hbi
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, he i hi b hb, if_neg (Ne.symm hbi), zero_smul]
    · intro h
      exact absurd hi h
  rw [add_mul, mul_add, mul_add, h1, Finset.mul_sum, Finset.sum_mul, add_assoc, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add, ← smul_add]
  congr 1
  noncomm_ring
end Formalism.L2.SG.Pf.LatDictZ.Z5
