-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.summatory_rpow_integrableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:17:18.727884+00:00
-- url     : https://prove2.me/submissions/8ea4edad-ee90-46f9-a242-4969606802d0

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
import Theorems.Thm_Formalism_mellinSgen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1 * Λ n) {w : ℂ} (hw : 1 < w.re) :
    IntegrableOn (fun x : ℝ => (Formalism.Sa a x : ℂ) * (x : ℂ) ^ (-w - 1)) (Ioi 1) := by
  obtain ⟨hm, hI, -⟩ := Formalism.mellinSgen a 1 ha
  refine Integrable.mono' (hI w.re hw) ?_ ?_
  · exact ((Complex.measurable_ofReal.comp hm).mul
      (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs]
    simp
end Formalism.ZeroFreeDirichlet
