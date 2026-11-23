-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.card_pm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:57:56.535276+00:00
-- url     : https://prove2.me/submissions/d7f0d13c-d82d-4299-ad36-7dd7c4e1dcb4

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_card_root_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Polynomial Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {q : ℕ} (hq : 2 ≤ q) (e : K) : Nat.card {x : K // x ^ q + e * x = 0} ≤ q := by
  have hdeg : (C e * X : K[X]).degree < (q : ℕ) := by
    calc (C e * X : K[X]).degree ≤ 1 := by
          refine (Polynomial.degree_C_mul_X_le e)
      _ < (q : ℕ) := by exact_mod_cast (by omega : 1 < q)
  have hm : (X ^ q + C e * X : K[X]).Monic := Polynomial.monic_X_pow_add hdeg
  have hn : (X ^ q + C e * X : K[X]).natDegree = q := by
    have : (X ^ q + C e * X : K[X]).degree = (q : ℕ) := by
      rw [Polynomial.degree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
        Polynomial.degree_X_pow]
    exact Polynomial.natDegree_eq_of_degree_eq_some this
  have := card_root_le _ hm.ne_zero
  rw [hn] at this
  simpa using this
end Formalism.FourierDecayAlt.P.S3x5
