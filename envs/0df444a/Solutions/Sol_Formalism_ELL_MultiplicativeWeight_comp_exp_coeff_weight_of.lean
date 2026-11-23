-- Prove2me | solution 1 for Formalism.ELL.MultiplicativeWeight.comp_exp_coeff_weight_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:53.234451+00:00
-- url     : https://prove2.me/submissions/10bd2aa5-6c7e-4ee7-a6b0-6b9c3b965427

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_CompExpWeight
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp
import Theorems.Thm_Formalism_ELL_MultiplicativeWeight_W_E
import Theorems.Thm_Formalism_ELL_MultiplicativeWeight_W_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries IsUltrametricDist
universe u
open Formalism Formalism.ELL Formalism.ELL.MultiplicativeWeight
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type} (c : ℝ)
variable {c}
namespace Formalism.ELL.MultiplicativeWeight
theorem _root_.solution : CompExpWeight.{u} := by
  intro K _ _ σ _ c hc hc1 E hE hb G hG α
  classical
  have ha := MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := σ) (S := K)
    (a := fun i : σ => E.subst (MvPowerSeries.X i : MvPowerSeries σ K))
    fun i => PowerSeries.constantCoeff_subst_eq_zero (by simp) E hE
  rw [MvPowerSeries.coeff_subst ha]
  have hfin := MvPowerSeries.coeff_subst_finite ha G α
  rw [finsum_eq_sum _ hfin]
  refine norm_sum_le_of_forall_le_of_nonneg (by positivity) fun d _ => ?_
  rw [smul_eq_mul, norm_mul]
  have h1 := W_prod hc hc1 _ (W_E E hE hb hc) d α
  calc ‖MvPowerSeries.coeff d G‖ * ‖MvPowerSeries.coeff α
          (d.prod fun s e => (E.subst (MvPowerSeries.X s : MvPowerSeries σ K)) ^ e)‖
      ≤ 1 * c ^ ((d.degree : ℤ) - (α.degree : ℤ)) :=
        mul_le_mul (hG d) h1 (norm_nonneg _) zero_le_one
    _ ≤ c ^ (-(α.degree : ℤ)) := by
        rw [one_mul]; exact zpow_le_zpow_right_of_le_one₀ hc hc1 (by omega)
end Formalism.ELL.MultiplicativeWeight
