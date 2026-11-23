-- Prove2me | solution 1 for Formalism.FG.CongrVAux.coeff_subst_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:45.750096+00:00
-- url     : https://prove2.me/submissions/9a1df834-eb12-4b93-b82a-876d3ec42d7a

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Theorems.Thm_Formalism_FG_CongrVAux_prod_pow_sub_of_forall_sub

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
variable {R : Type u} [CommRing R] {τ : Type w}
namespace Formalism.FG.CongrVAux
theorem _root_.solution {ι : Type v} [Finite ι] {d : τ →₀ ℕ} {k k' : ι → MvPowerSeries τ R}
    (hk : ∀ i, constantCoeff (k i) = 0) (hk' : ∀ i, constantCoeff (k' i) = 0)
    (hkk : ∀ i, ∀ e ≤ d, coeff e (k i) = coeff e (k' i)) (g : MvPowerSeries ι R) :
    coeff d (subst k g) = coeff d (subst k' g) := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero hk), coeff_subst (hasSubst_of_constantCoeff_zero hk')]
  refine finsum_congr fun e => ?_
  congr 1
  have hz : ∀ i, Zd d (k i - k' i) := fun i e he => by rw [map_sub, hkk i e he, sub_self]
  have := prod_pow_sub_of_forall_sub hz e d le_rfl
  rw [map_sub, sub_eq_zero] at this
  simpa only [P] using this
end Formalism.FG.CongrVAux
