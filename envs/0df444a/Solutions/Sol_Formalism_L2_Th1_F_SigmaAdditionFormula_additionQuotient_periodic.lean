-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaAdditionFormula.additionQuotient_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:46.003454+00:00
-- url     : https://prove2.me/submissions/a4e6c47c-761b-47e3-aad0-d5b9084b872f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaAdd
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_semiChar_sq

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
open Formalism.L2.Th1.F.SigmaAdditionFormula
variable (L : PeriodPair) (w : ℂ)
namespace Formalism.L2.Th1.F.SigmaAdditionFormula
theorem _root_.solution (hq : SigmaQuasi) : IsPeriodic L (additionQuotient L w) := by
  intro ω hω z
  have h1 := hq L ω (z + w) hω
  have h2 := hq L ω (z - w) hω
  have h0 := hq L ω z hω
  have hP : L.weierstrassP (z + ω) = L.weierstrassP z := L.weierstrassP_add_coe z ⟨ω, hω⟩
  have hs := semiChar_sq L ω
  have he : Complex.exp (wEta L ω * (z + w + ω / 2)) * Complex.exp (wEta L ω * (z - w + ω / 2))
      = Complex.exp (wEta L ω * (z + ω / 2)) ^ 2 := by
    rw [← Complex.exp_add, sq, ← Complex.exp_add]
    congr 1
    ring
  have hne : Complex.exp (wEta L ω * (z + ω / 2)) ^ 2 ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  unfold additionQuotient
  rw [show z + ω + w = (z + w) + ω by ring, show z + ω - w = (z - w) + ω by ring, h1, h2, h0, hP]
  congr 1
  calc _ = (semiChar L ω ^ 2 * (Complex.exp (wEta L ω * (z + w + ω / 2))
          * Complex.exp (wEta L ω * (z - w + ω / 2)))) * (wSigma L (z + w) * wSigma L (z - w))
          / ((semiChar L ω ^ 2 * Complex.exp (wEta L ω * (z + ω / 2)) ^ 2) * wSigma L z ^ 2) := by
        ring
    _ = _ := by rw [hs, he, one_mul, mul_div_mul_left _ _ hne]
end Formalism.L2.Th1.F.SigmaAdditionFormula
