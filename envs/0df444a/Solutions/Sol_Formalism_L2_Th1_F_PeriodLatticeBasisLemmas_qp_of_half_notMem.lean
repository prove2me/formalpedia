-- Prove2me | solution 1 for Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.qp_of_half_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:59:10.672482+00:00
-- url     : https://prove2.me/submissions/1ac654a0-3ccc-4d40-8ffd-d2101123820d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaQuasi
import Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_exists_const

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
theorem _root_.solution (hq : ZetaQuasi) (hl : SigmaLogDeriv) (ho : SigmaOdd) (hz : SigmaZero)
    (L : PeriodPair) {ω : ℂ} (hω : ω ∈ L.lattice) (hω2 : ω / 2 ∉ L.lattice) : QP L ω (-1) := by
  obtain ⟨c, hc⟩ := exists_const hq hl hz L hω
  have hs : Formalism.L2.Th1.F.wSigma L (ω / 2) ≠ 0 := (hz L _).not.mpr hω2
  have key := hc (-(ω / 2))
  rw [show -(ω / 2) + ω = ω / 2 by ring, ho L] at key
  have hce : c * Complex.exp (Formalism.L2.Th1.F.wEta L ω * -(ω / 2)) = -1 := by
    apply mul_right_cancel₀ hs
    linear_combination key
  have hE : Complex.exp (Formalism.L2.Th1.F.wEta L ω * -(ω / 2)) * Complex.exp (Formalism.L2.Th1.F.wEta L ω * (ω / 2)) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  unfold QP
  intro z
  rw [hc z, mul_add, Complex.exp_add]
  linear_combination (-(Complex.exp (Formalism.L2.Th1.F.wEta L ω * z) * Formalism.L2.Th1.F.wSigma L z * c)) * hE
    + (Complex.exp (Formalism.L2.Th1.F.wEta L ω * z) * Formalism.L2.Th1.F.wSigma L z
        * Complex.exp (Formalism.L2.Th1.F.wEta L ω * (ω / 2))) * hce
end Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
