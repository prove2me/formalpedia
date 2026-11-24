-- Prove2me | solution 1 for Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.qp_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:25:00.707807+00:00
-- url     : https://prove2.me/submissions/6c41a34a-f25e-4cf5-90f7-a3aa4fe8ec51

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaQuasi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
namespace Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
theorem _root_.solution (L : PeriodPair) {ω c : ℂ} (h : QP L ω c) (hc : c ^ 2 = 1) : QP L (2 * ω) 1 := by
  unfold QP at h ⊢
  intro z
  rw [two_mul, map_add, show z + (ω + ω) = z + ω + ω by ring, h (z + ω), h z]
  have hE : Complex.exp (Formalism.L2.Th1.F.wEta L ω * (z + ω + ω / 2)) * Complex.exp (Formalism.L2.Th1.F.wEta L ω * (z + ω / 2))
      = Complex.exp ((Formalism.L2.Th1.F.wEta L ω + Formalism.L2.Th1.F.wEta L ω) * (z + (ω + ω) / 2)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  linear_combination (Complex.exp (Formalism.L2.Th1.F.wEta L ω * (z + ω + ω / 2))
      * Complex.exp (Formalism.L2.Th1.F.wEta L ω * (z + ω / 2)) * Formalism.L2.Th1.F.wSigma L z) * hc
    + Formalism.L2.Th1.F.wSigma L z * hE
end Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
