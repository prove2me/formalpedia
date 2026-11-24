-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.summatory_function_continuousAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:00:23.670664+00:00
-- url     : https://prove2.me/submissions/9a99aea1-9826-42ce-b6bd-902710de3e0c

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
import Theorems.Thm_Formalism_ZeroFreeDirichlet_summatory_eq_sum_range
import Theorems.Thm_Formalism_ZF_perron_continuous_mxS


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
theorem _root_.solution {a : ℕ → ℝ} (ha0 : a 0 = 0) (y : ℝ) :
    ContinuousAt (fun x => (Formalism.Sa a x : ℂ)) y := by
  obtain ⟨N, hN⟩ := exists_nat_gt y
  have hev : (fun x => ((∑ n ∈ Finset.range N, a n * Formalism.mxS n x : ℝ) : ℂ)) =ᶠ[𝓝 y]
      (fun x => (Formalism.Sa a x : ℂ)) := by
    filter_upwards [eventually_lt_nhds hN] with x hx
    rw [summatory_eq_sum_range ha0 hx]
  refine ContinuousAt.congr ?_ hev
  exact (Complex.continuous_ofReal.comp (continuous_finsetSum _
    (fun n _ => continuous_const.mul (Formalism.ZF.perron_continuous_mxS n)))).continuousAt
end Formalism.ZeroFreeDirichlet
