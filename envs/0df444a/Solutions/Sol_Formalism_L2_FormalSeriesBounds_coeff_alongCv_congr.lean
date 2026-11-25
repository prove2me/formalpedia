-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_alongCv_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:34:58.929185+00:00
-- url     : https://prove2.me/submissions/6ddedcc5-d406-4e74-a2fe-3a820b5e79e9

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {σ : Type} [Finite σ] {a a' : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (ha' : ∀ i, PowerSeries.constantCoeff (a' i) = 0) {k : ℕ}
    (h : ∀ i, ∀ m < k, PowerSeries.coeff m (a i) = PowerSeries.coeff m (a' i)) (f : MvPowerSeries σ C) :
    ∀ m < k, PowerSeries.coeff m (alongCv a f) = PowerSeries.coeff m (alongCv a' f) := by
  intro m hm
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hA' : MvPowerSeries.HasSubst a' := MvPowerSeries.hasSubst_of_constantCoeff_zero ha'
  have hdiff : ∀ i, a i - a' i ∈ Ideal.span {(PowerSeries.X : PowerSeries C) ^ k} := by
    intro i
    rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro n hn
    rw [map_sub, h i n hn, sub_self]
  have hprod : ∀ e : σ →₀ ℕ, PowerSeries.coeff m (e.prod fun s n => a s ^ n) =
      PowerSeries.coeff m (e.prod fun s n => a' s ^ n) := by
    intro e
    have hq : Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ k}) (e.prod fun s n => a s ^ n) =
        Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ k}) (e.prod fun s n => a' s ^ n) := by
      simp only [Finsupp.prod, map_prod, map_pow]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [Ideal.Quotient.eq.2 (hdiff s)]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hq
    have hm' := hq m hm
    rwa [map_sub, sub_eq_zero] at hm'
  simp only [alongCv]
  change MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst a f) =
    MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst a' f)
  rw [MvPowerSeries.coeff_subst hA, MvPowerSeries.coeff_subst hA']
  refine finsum_congr fun e => ?_
  congr 1
  exact hprod e
end Formalism.L2.FormalSeriesBounds
