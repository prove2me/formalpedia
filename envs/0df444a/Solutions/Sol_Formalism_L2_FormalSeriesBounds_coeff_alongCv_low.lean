-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_alongCv_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:08.04884+00:00
-- url     : https://prove2.me/submissions/83eff42b-e4ec-4cdf-847f-6f0c6fd88edb

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValNonnegLeadingCoeffOfMemTySet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_finsupp_deg_one
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod


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
theorem _root_.solution {σ : Type} [Fintype σ] {γ : σ → PowerSeries C} {n : ℕ} (hn : 1 ≤ n)
    (hγ : ∀ i, ∀ m < n, PowerSeries.coeff m (γ i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff n (alongCv γ f) =
      ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f * PowerSeries.coeff n (γ i) := by
  have hγ0 : ∀ i, MvPowerSeries.constantCoeff (γ i) = 0 := fun i => by
    have := hγ i 0 (by omega)
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
  unfold alongCv
  show MvPowerSeries.coeff (Finsupp.single () n) _ = _
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0),
    finsum_eq_sum_of_support_subset (s := Finset.univ.image fun i : σ => Finsupp.single i 1)]
  · rw [Finset.sum_image (fun a _ b _ h => Finsupp.single_left_injective one_ne_zero h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp : (Finsupp.single i 1 : σ →₀ ℕ).prod (fun s e => γ s ^ e) = γ i := by
      rw [Finsupp.prod_single_index (h := fun s e => γ s ^ e) (pow_zero _), pow_one]
    show MvPowerSeries.coeff (Finsupp.single i 1) f •
      MvPowerSeries.coeff (Finsupp.single () n) ((Finsupp.single i 1 : σ →₀ ℕ).prod fun s e => γ s ^ e) = _
    rw [hp, smul_eq_mul]
    rfl
  · intro e he
    rw [Function.mem_support] at he
    rw [Finset.coe_image, Set.mem_image]
    by_contra hc
    apply he
    have hdeg : e.degree ≠ 1 := fun h => by
      obtain ⟨i, hi⟩ := finsupp_deg_one e h
      exact hc ⟨i, by simp, hi.symm⟩
    by_cases h0 : e.degree = 0
    · rw [Finsupp.degree_eq_zero_iff] at h0
      rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
    · have h2 : 2 ≤ e.degree := by omega
      have hdvd : (PowerSeries.X : PowerSeries C) ^ (n * e.degree) ∣ e.prod fun s m => γ s ^ m := by
        unfold Finsupp.prod
        rw [Finsupp.degree_apply, pow_mul, ← Finset.prod_pow_eq_pow_sum]
        apply Finset.prod_dvd_prod_of_dvd
        intro i _
        exact pow_dvd_pow_of_dvd (PowerSeries.X_pow_dvd_iff.2 (hγ i)) _
      have hz : PowerSeries.coeff n (e.prod fun s m => γ s ^ m) = 0 :=
        PowerSeries.X_pow_dvd_iff.1 hdvd n (by nlinarith)
      show MvPowerSeries.coeff e f • PowerSeries.coeff n (e.prod fun s m => γ s ^ m) = 0
      rw [hz, smul_zero]
end Formalism.L2.FormalSeriesBounds
