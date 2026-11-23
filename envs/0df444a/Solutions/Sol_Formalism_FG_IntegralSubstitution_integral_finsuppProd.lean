-- Prove2me | solution 1 for Formalism.FG.IntegralSubstitution.integral_finsuppProd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:56.634066+00:00
-- url     : https://prove2.me/submissions/d1825944-50c1-42e8-967c-187ae049a913

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.IntegralSubstitution
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}
namespace Formalism.FG.IntegralSubstitution
theorem _root_.solution {ι : Type v} (a : ι → MvPowerSeries τ K) (ha : ∀ i, IntegralMv (a i))
    (n : ι →₀ ℕ) : IntegralMv (n.prod fun s e => (a s) ^ e) := by
  classical
  unfold Finsupp.prod
  exact Finset.prod_induction _ (fun x => IntegralMv x) (fun _ _ hx hy => integral_mul hx hy)
    integral_one (fun i _ => integral_pow (ha i) _)
end Formalism.FG.IntegralSubstitution
