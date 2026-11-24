-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd3.rtt_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:15.374052+00:00
-- url     : https://prove2.me/submissions/a85af104-a98f-4a1c-968b-a24ddcccac1a

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_firstEmbed_mul_secondEmbed_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_secondEmbed_mul_firstEmbed_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_Pf_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_mul_Pf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd3
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd3
theorem _root_.solution {B : Type} [Ring B] [Algebra K B] (M N : M2 B) (D : K)
    (h : (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) * E1 M * E2 N =
      E2 N * E1 M * (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B))
    (i r j s : Fin 2) :
    D • (M i j * N r s) - M r j * N i s = D • (N r s * M i j) - N r j * M i s := by
  have h' := congrFun (congrFun h (i, r)) (j, s)
  rw [mul_assoc, sub_mul, Matrix.smul_mul, Matrix.one_mul, mul_sub, Matrix.mul_smul, Matrix.mul_one] at h'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Pf_mul, mul_Pf, firstEmbed_mul_secondEmbed_apply, secondEmbed_mul_firstEmbed_apply] at h'
  exact h'
end Formalism.FourierDecayAlt.P.Wd3
