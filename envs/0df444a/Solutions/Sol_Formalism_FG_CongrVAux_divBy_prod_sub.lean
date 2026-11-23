-- Prove2me | solution 1 for Formalism.FG.CongrVAux.divBy_prod_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:04.0931+00:00
-- url     : https://prove2.me/submissions/0ab552ac-f800-4b68-8582-7572e845bded

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Theorems.Thm_Formalism_FG_CongrVAux_divBy_mul_sub
import Theorems.Thm_Formalism_FG_CongrVAux_integral_prod
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
open Formalism Formalism.FG Formalism.FG.CongrVAux
open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.SolveVAux
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}
namespace Formalism.FG.CongrVAux
theorem _root_.solution {ι : Type v} {c : K} {a b : ι → MvPowerSeries τ K}
    (ha : ∀ i, IntegralMv (a i)) (hb : ∀ i, IntegralMv (b i)) (n : ι → ℕ)
    (h : ∀ i, DivByMv c (a i ^ n i - b i ^ n i)) (s : Finset ι) :
    DivByMv c (∏ i ∈ s, a i ^ n i - ∏ i ∈ s, b i ^ n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro d; simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact divBy_mul_sub (IntegralSubstitution.integral_pow (hb i) _)
      (integral_prod s _ fun j => IntegralSubstitution.integral_pow (ha j) _) (h i) ih
end Formalism.FG.CongrVAux
