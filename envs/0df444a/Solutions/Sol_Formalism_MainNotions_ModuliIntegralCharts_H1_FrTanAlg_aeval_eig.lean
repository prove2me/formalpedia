-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg.aeval_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:06:56.015092+00:00
-- url     : https://prove2.me/submissions/a5e2e24f-caf2-4ea8-97f4-7178abf8c66a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanAlg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanAlg_pow_apply_eig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
open Polynomial NumberField
variable {S M : Type} [Field S] [AddCommGroup M] [Module S M]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
theorem _root_.solution (f : Module.End S M) (μ : S) (x : M) (hx : f x = μ • x) (p : S[X]) :
    aeval f p x = p.eval μ • x := by
  refine Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · simp [hp, hq, add_smul]
  · simp [pow_apply_eig f μ x hx, smul_smul, mul_comm]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
