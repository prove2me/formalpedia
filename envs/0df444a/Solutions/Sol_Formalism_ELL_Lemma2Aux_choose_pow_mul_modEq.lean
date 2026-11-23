-- Prove2me | solution 1 for Formalism.ELL.Lemma2Aux.choose_pow_mul_modEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:21:53.481578+00:00
-- url     : https://prove2.me/submissions/4b2c72a2-f741-4d13-907d-47c804fde88b

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (k m : ℕ) :
    (p ^ k * m).choose (p ^ k) ≡ m [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  induction k with
  | zero => simp [Nat.ModEq.refl]
  | succ k ih =>
    have h := Choose.choose_mul_mul_modEq_choose_nat (p := p) (a := p ^ k * m) (b := p ^ k)
    rw [pow_succ', mul_assoc]
    exact h.trans ih
end Formalism.ELL.Lemma2Aux
