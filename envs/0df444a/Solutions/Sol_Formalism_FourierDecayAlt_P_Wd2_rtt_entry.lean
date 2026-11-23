-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd2.rtt_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:50.542853+00:00
-- url     : https://prove2.me/submissions/b0cff9d9-fcb1-40d9-8ce9-f3ea278bb8c0

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_kronecker_E1_E2_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_kronecker_embed_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_Pf_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_mul_Pf_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd2
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K B : Type} [CommRing K] [Ring B] [Algebra K B]
namespace Formalism.FourierDecayAlt.P.Wd2
theorem _root_.solution (M N : Matrix (Fin 2) (Fin 2) B) (D : K)
    (H : (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) * E1 M * E2 N =
      E2 N * E1 M * (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B))
    (i j k l : Fin 2) :
    D • (M i j * N k l) - M k j * N i l = D • (N k l * M i j) - N k j * M i l := by
  have h := congrFun (congrFun H (i, k)) (j, l)
  rw [mul_assoc, sub_mul, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one] at h
  simp only [Matrix.sub_apply, Matrix.smul_apply, Pf_mul_apply, mul_Pf_apply, kronecker_E1_E2_apply,
    kronecker_embed_mul_apply] at h
  exact h
end Formalism.FourierDecayAlt.P.Wd2
