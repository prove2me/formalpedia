-- Prove2me | solution 1 for Formalism.L2.Th1.F.PeriodAreaSignLemmas.det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:35.702576+00:00
-- url     : https://prove2.me/submissions/202e2e2d-e3b0-4ef1-8e1a-2b1875069d96

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstUniqueOf
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_det_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.PeriodAreaSignLemmas
namespace Formalism.L2.Th1.F.PeriodAreaSignLemmas
theorem _root_.solution (L : PeriodPair) : det L ≠ 0 := by
  intro h
  rw [det_eq] at h
  have key := LinearIndependent.pair_iff.mp L.indep
  have h1 := key L.ω₂.im (-L.ω₁.im) (by
    apply Complex.ext
    · simp; linarith
    · simp; ring)
  have h2 := key L.ω₂.re (-L.ω₁.re) (by
    apply Complex.ext
    · simp; ring
    · simp; linarith)
  have h3 : L.ω₁ = 0 := by
    apply Complex.ext
    · simpa using h2.2
    · simpa using h1.2
  have h4 := key 1 0 (by simp [h3])
  exact one_ne_zero h4.1
end Formalism.L2.Th1.F.PeriodAreaSignLemmas
