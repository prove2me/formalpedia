-- Prove2me | solution 1 for Formalism.LT.LTL.divBy_subst_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:35:55.261097+00:00
-- url     : https://prove2.me/submissions/0be0c502-81c1-44a6-af84-c9f4f37d2440

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_P2M_Formalism_LT_LTL_norm_finsum_le__8658a123f7be
import Theorems.Thm_Formalism_LT_LTL_cong_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
namespace Formalism.LT.LTL
theorem _root_.solution [Finite ι] {τ : Type*} {c : K} {a b : ι → MvPowerSeries τ K}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
    (hab : ∀ i, Cong c (a i) (b i)) {δ : MvPowerSeries ι K} (hδ : IntegralMv δ) :
    DivByMv c (MvPowerSeries.subst a δ - MvPowerSeries.subst b δ) := by
  intro d
  have ha' : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hb' : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  rw [map_sub, MvPowerSeries.coeff_subst ha', MvPowerSeries.coeff_subst hb',
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite ha' δ d)
      (MvPowerSeries.coeff_subst_finite hb' δ d)]
  refine norm_finsum_le' (norm_nonneg _) fun m => ?_
  rw [← smul_sub, smul_eq_mul, norm_mul, ← map_sub]
  calc _ ≤ 1 * ‖c‖ := mul_le_mul (hδ m) ((cong_monomial hab m).2.2 d) (norm_nonneg _) zero_le_one
    _ = ‖c‖ := one_mul _
end Formalism.LT.LTL
