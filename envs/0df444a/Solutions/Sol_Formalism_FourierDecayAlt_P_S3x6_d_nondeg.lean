-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.d_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:23.220024+00:00
-- url     : https://prove2.me/submissions/d88aa1ed-c64a-4b76-bd6d-688b8d8f9a5e

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_hJ_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
open Matrix Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution {n : ℕ} (J : Matrix (Fin n) (Fin n) K) (hJu : IsUnit J.det) : Nondeg (hJ σ J) := by
  intro u hu
  have h1 : (fun i => σ (u i)) ᵥ* J = 0 := by
    ext j
    have := hu (Pi.single j 1)
    rw [hJ_apply] at this
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at this
    simpa [Matrix.vecMul, dotProduct] using this
  have h2 := Matrix.eq_zero_of_vecMul_eq_zero hJu.ne_zero h1
  ext i
  have := congrFun h2 i
  simpa using this
end Formalism.FourierDecayAlt.P.S3x6
