-- Prove2me | solution 1 for Formalism.FG.IntegralSubstitution.integralSubstV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:57.685568+00:00
-- url     : https://prove2.me/submissions/b184ab9d-fe62-4bf0-ae9d-d24160870e43

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_finsuppProd

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
theorem _root_.solution {ι : Type v} [Finite ι] (g : MvPowerSeries ι K)
    (a : ι → MvPowerSeries τ K) (hg : IntegralMv g)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha : ∀ i, IntegralMv (a i)) :
    IntegralMv (MvPowerSeries.subst a g) := by
  intro d
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  rw [MvPowerSeries.coeff_subst hs g d]
  have hfin := MvPowerSeries.coeff_subst_finite hs g d
  rw [finsum_eq_sum _ hfin]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun n _ => ?_
  rw [smul_eq_mul, norm_mul]
  exact mul_le_one₀ (hg n) (norm_nonneg _) (integral_finsuppProd a ha n d)
end Formalism.FG.IntegralSubstitution
