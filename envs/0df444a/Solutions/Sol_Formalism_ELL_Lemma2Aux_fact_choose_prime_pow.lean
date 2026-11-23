-- Prove2me | solution 1 for Formalism.ELL.Lemma2Aux.fact_choose_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:56.937623+00:00
-- url     : https://prove2.me/submissions/cb0d2210-3b74-401c-907f-23be799ddde7

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionWeights
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CoefficientWeightsLemmaTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open Formalism Formalism.ELL Formalism.ELL.Lemma2Aux
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.Lemma2Aux
theorem _root_.solution {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k) :
    ((p ^ k).choose (p ^ (k - 1))).factorization p = 1 := by
  rw [Nat.factorization_choose_prime_pow hp (Nat.pow_le_pow_right hp.pos (by omega))
    (pow_ne_zero _ hp.ne_zero)]
  rw [hp.factorization_pow]
  simp
  omega
end Formalism.ELL.Lemma2Aux
