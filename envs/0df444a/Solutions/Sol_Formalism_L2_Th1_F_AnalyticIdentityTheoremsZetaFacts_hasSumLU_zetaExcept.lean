-- Prove2me | solution 1 for Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts.hasSumLU_zetaExcept
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:00.534829+00:00
-- url     : https://prove2.me/submissions/88102bf5-70c4-4bc4-a9b5-0333408d4a8f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
import Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_term_bound

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
open Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts
namespace Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts
theorem _root_.solution (L : PeriodPair) (l₀ : ℂ) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) ↦
        if l.1 = l₀ then 0 else (1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2))
      (zetaExcept L l₀) := by
  have hs3 : Summable fun l : L.lattice => ‖(l : ℂ)‖ ^ (-3 : ℝ) :=
    ZLattice.summable_norm_rpow L.lattice (-3) (by rw [L.finrank_lattice]; norm_num)
  refine L.hasSumLocallyUniformly_aux _ (fun r l => 2 * r ^ 2 * ‖(l : ℂ)‖ ^ (-3 : ℝ))
    (fun r _ => hs3.mul_left (2 * r ^ 2)) fun r hr => ?_
  filter_upwards [Filter.eventually_ge_atTop (2 * r)] with R hR x hx l hl
  split_ifs
  · rw [norm_zero]
    positivity
  · exact term_bound r hr x hx l (by rw [hl]; exact hR)
end Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts
