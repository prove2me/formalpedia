-- Prove2me | solution 1 for Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts.hasSumLU_wZeta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:00.538983+00:00
-- url     : https://prove2.me/submissions/4a9666f7-d90f-4e81-94ae-a1a2b424af16

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
theorem _root_.solution (L : PeriodPair) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) ↦ 1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)
      (wZeta L) := by
  have hs3 : Summable fun l : L.lattice => ‖(l : ℂ)‖ ^ (-3 : ℝ) :=
    ZLattice.summable_norm_rpow L.lattice (-3) (by rw [L.finrank_lattice]; norm_num)
  refine L.hasSumLocallyUniformly_aux _ (fun r l => 2 * r ^ 2 * ‖(l : ℂ)‖ ^ (-3 : ℝ))
    (fun r _ => hs3.mul_left (2 * r ^ 2)) fun r hr => ?_
  filter_upwards [Filter.eventually_ge_atTop (2 * r)] with R hR x hx l hl
  exact term_bound r hr x hx l (by rw [hl]; exact hR)
end Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts
