-- Prove2me | solution 1 for Formalism.L2.Th1.F.sgStarThree_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:26:10.48152+00:00
-- url     : https://prove2.me/submissions/2fb4615e-d93f-4855-bc25-06286db0cb76

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution (h : SigmaThree) : SgStarThree := by
  intro L a b c ha hb hc
  have h0 := h L a b c ha hb hc
  have hexp : (Complex.exp (-(s2 L) * a ^ 2 / 2) * Complex.exp (-(s2 L) * b ^ 2 / 2)
        * Complex.exp (-(s2 L) * c ^ 2 / 2)) ^ 3
      = Complex.exp (-(s2 L) * (a + b + c) ^ 2 / 2) * Complex.exp (-(s2 L) * (a - b) ^ 2 / 2)
        * Complex.exp (-(s2 L) * (b - c) ^ 2 / 2) * Complex.exp (-(s2 L) * (c - a) ^ 2 / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_nat_mul, ← Complex.exp_add,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  unfold sgStar
  generalize Matrix.det !![1, L.weierstrassP a, L.derivWeierstrassP a;
                   1, L.weierstrassP b, L.derivWeierstrassP b;
                   1, L.weierstrassP c, L.derivWeierstrassP c] = D at h0 ⊢
  linear_combination (Complex.exp (-(s2 L) * a ^ 2 / 2) * Complex.exp (-(s2 L) * b ^ 2 / 2)
        * Complex.exp (-(s2 L) * c ^ 2 / 2)) ^ 3 * h0
    + (2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a)) * hexp
end Formalism.L2.Th1.F
