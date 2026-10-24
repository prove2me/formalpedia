-- Prove2me | solution 1 for GVRPricing.FixedPrice.deterministic_solution
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T21:05:11.845148+00:00
-- url     : https://prove2.me/submissions/0d7c59c3-0174-4843-893d-36548de82fe4

import Init
import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_Model
import Definitions.Def_GVRPricing_FixedPrice_Deterministic

open MeasureTheory Set Function Classical
noncomputable section
namespace Pricing
open GVRPricing.FixedPrice
lemma star_mem (M : Model) : M.lstar ∈ M.Λ := M.isLeast_lstar.1.1
lemma star_nonneg (M : Model) : 0 ≤ M.lstar := M.nonneg _ (star_mem M)
lemma r_nonneg (M : Model) {l : ℝ} (hl : l ∈ M.Λ) : 0 ≤ M.r l := by
  by_cases he : l=0
  · simp [he,Model.r]
  · exact mul_nonneg (M.nonneg _ hl) (M.price_nonneg _ hl he)
lemma r_le_star (M : Model) {l : ℝ} (hl : l ∈ M.Λ) : M.r l ≤ M.rstar := M.isLeast_lstar.1.2 l hl
lemma interval_mem (M : Model) : Icc 0 M.lstar ⊆ M.Λ :=
  M.ordConnected.out M.zero_mem (star_mem M)
lemma chosen_mem (M : Model) (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    min M.lstar (x/t) ∈ Icc 0 M.lstar :=
  ⟨le_min (star_nonneg M) (div_nonneg hx ht.le),min_le_left _ _⟩
lemma r_monotone (M : Model) : MonotoneOn M.r (Icc 0 M.lstar) := by
  intro a ha b hb hab
  rcases hab.eq_or_lt with rfl|hab
  · rfl
  by_cases he : b=M.lstar
  · simpa [he,Model.rstar] using r_le_star M (interval_mem M ha)
  have hbs : b<M.lstar := lt_of_le_of_ne hb.2 he
  have hsl := M.concaveOn.slope_anti_adjacent (interval_mem M ha) (star_mem M) hab hbs
  have hn : 0 ≤ (M.r M.lstar-M.r b)/(M.lstar-b) :=
    div_nonneg (sub_nonneg.mpr (r_le_star M (interval_mem M hb))) (sub_pos.mpr hbs).le
  have := hn.trans hsl
  have : 0 ≤ (M.r b-M.r a) := by simpa [Model.r] using (le_div_iff₀ (sub_pos.mpr hab)).mp this
  linarith
lemma constant_feasible (M : Model) (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    IsFeasiblePath M x t (fun _ => min M.lstar (x/t)) := by
  refine ⟨⟨measurable_const,fun s hs => interval_mem M (chosen_mem M x t hx ht),intervalIntegrable_const⟩,?_⟩
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  calc t * min M.lstar (x/t) ≤ t*(x/t) := mul_le_mul_of_nonneg_left (min_le_right _ _) ht.le
       _ = x := mul_div_cancel₀ x ht.ne'
end Pricing

open MeasureTheory Set Function Classical
noncomputable section
namespace Pricing
open GVRPricing.FixedPrice

lemma revenue_integrable (M : Model) (t : ℝ) (ℓ : ℝ → ℝ) (hℓ : IsRatePath M t ℓ) :
    IntegrableOn (fun s => M.r (ℓ s)) (Ioc 0 t) := by
  let R : ℝ → ℝ := M.Λ.piecewise M.r (fun _ => 0)
  have hm : Measurable R := M.continuousOn.measurable_piecewise continuousOn_const M.ordConnected.measurableSet
  have hmeas : AEStronglyMeasurable (fun s => M.r (ℓ s)) (volume.restrict (Ioc 0 t)) := by
    apply (hm.comp hℓ.1).aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp [R,Set.piecewise,hℓ.2.1 s ⟨hs.1.le,hs.2⟩]
  apply (integrable_const M.rstar).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.norm_eq_abs,abs_of_nonneg (r_nonneg M (hℓ.2.1 s ⟨hs.1.le,hs.2⟩))]
  exact r_le_star M (hℓ.2.1 s ⟨hs.1.le,hs.2⟩)

lemma clipped_rate_pos (M : Model) (t : ℝ) (ht : 0 ≤ t) (ℓ : ℝ → ℝ) (hℓ : IsRatePath M t ℓ) :
    IsRatePath M t (fun s => min M.lstar (ℓ s)) := by
  have hm : Measurable (fun s => min M.lstar (ℓ s)) := measurable_const.min hℓ.1
  have hs (s : ℝ) (ht : s ∈ Icc 0 t) : min M.lstar (ℓ s) ∈ Icc 0 M.lstar :=
    ⟨le_min (star_nonneg M) (M.nonneg _ (hℓ.2.1 s ht)),min_le_left _ _⟩
  refine ⟨hm,fun s ht => interval_mem M (hs s ht),?_⟩
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr
  apply (integrable_const M.lstar).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s ht
  rw [Real.norm_eq_abs,abs_of_nonneg (hs s ⟨ht.1.le,ht.2⟩).1]
  exact (hs s ⟨ht.1.le,ht.2⟩).2

lemma cap_improves (M : Model) {l : ℝ} (hl : l ∈ M.Λ) : M.r l ≤ M.r (min M.lstar l) := by
  rcases le_total M.lstar l with h|h
  · simpa [min_eq_left h,Model.rstar] using r_le_star M hl
  · rw [min_eq_right h]
end Pricing

open MeasureTheory Set Function Classical
noncomputable section
namespace Pricing
open GVRPricing.FixedPrice

theorem revenue_optimal (M : Model) (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t)
    (ℓ : ℝ → ℝ) (hℓ : IsFeasiblePath M x t ℓ) :
    (∫ s in (0 : ℝ)..t, M.r (ℓ s)) ≤ t*M.r (min M.lstar (x/t)) := by
  let k : ℝ → ℝ := fun s => min M.lstar (ℓ s)
  have hk : IsRatePath M t k := clipped_rate_pos M t ht.le ℓ hℓ.1
  have hki : IntegrableOn k (Ioc 0 t) := hk.2.2.1
  have hkri := revenue_integrable M t k hk
  have hlri := revenue_integrable M t ℓ hℓ.1
  have hkmem : ∀ᵐ s ∂volume.restrict (Ioc 0 t), k s ∈ Icc 0 M.lstar := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact ⟨le_min (star_nonneg M) (M.nonneg _ (hℓ.1.2.1 s ⟨hs.1.le,hs.2⟩)),min_le_left _ _⟩
  have hj := (M.concaveOn.subset (interval_mem M) (convex_Icc _ _)).set_average_mem_hypograph
    (M.continuousOn.mono (interval_mem M)) isClosed_Icc
    (show volume (Ioc (0:ℝ) t) ≠ 0 by simp [Real.volume_Ioc,ht.ne',not_le.mpr ht])
    (show volume (Ioc (0:ℝ) t) ≠ ⊤ by simp [Real.volume_Ioc]) hkmem hki hkri
  change (⨍ s in Ioc (0:ℝ) t,k s) ∈ Icc 0 M.lstar ∧
    (⨍ s in Ioc (0:ℝ) t,M.r (k s)) ≤ M.r (⨍ s in Ioc (0:ℝ) t,k s) at hj
  have havg (f : ℝ → ℝ) : (⨍ s in Ioc (0:ℝ) t, f s) = (∫ s in Ioc (0:ℝ) t,f s)/t := by
    simp [setAverage_eq,measureReal_def,Real.volume_Ioc,ht.le,smul_eq_mul,div_eq_inv_mul]
  have hcons : (∫ s in Ioc (0:ℝ) t,k s) ≤ x := by
    calc _ ≤ ∫ s in Ioc (0:ℝ) t,ℓ s := integral_mono_ae hki hℓ.1.2.2.1
            (Filter.Eventually.of_forall fun s => min_le_right _ _)
         _ ≤ x := by simpa [intervalIntegral.integral_of_le ht.le] using hℓ.2
  have havle : (⨍ s in Ioc (0:ℝ) t,k s) ≤ min M.lstar (x/t) := by
    refine le_min hj.1.2 ?_
    rw [havg]
    exact div_le_div_of_nonneg_right hcons ht.le
  have hm := r_monotone M hj.1 (chosen_mem M x t hx ht) havle
  have hj' : (∫ s in Ioc (0:ℝ) t,M.r (k s)) ≤ t*M.r (min M.lstar (x/t)) := by
    have hh := hj.2.trans hm
    rw [havg] at hh
    have hh := (div_le_iff₀ ht).mp hh
    simpa [mul_comm] using hh
  rw [intervalIntegral.integral_of_le ht.le]
  apply le_trans (integral_mono_ae hlri hkri ?_) hj'
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact cap_improves M (hℓ.1.2.1 s ⟨hs.1.le,hs.2⟩)
#print axioms revenue_optimal
end Pricing

open MeasureTheory Set Function Classical
noncomputable section
namespace Pricing
open GVRPricing.FixedPrice

theorem value_eq (M : Model) (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    detValue M x t = t*M.r (min M.lstar (x/t)) := by
  let V : Set ℝ := (fun ℓ : ℝ → ℝ => ∫ s in (0:ℝ)..t,M.r (ℓ s)) '' {ℓ | IsFeasiblePath M x t ℓ}
  have hc : t*M.r (min M.lstar (x/t)) ∈ V := by
    refine ⟨fun _ => min M.lstar (x/t),constant_feasible M x t hx ht,?_⟩
    simp
  have hb : ∀ y ∈ V, y ≤ t*M.r (min M.lstar (x/t)) := by
    rintro y ⟨ℓ,hℓ,rfl⟩
    exact revenue_optimal M x t hx ht ℓ hℓ
  exact le_antisymm (csSup_le ⟨_,hc⟩ hb) (le_csSup ⟨_,hb⟩ hc)

theorem pricing_price (M : Model) (x t : ℝ) (ht : 0 < t)
    (hs : 0 < M.lstar) (hx : 0 < x) (hΛ : x/t ∈ M.Λ) :
    M.p (min M.lstar (x/t)) = max M.pstar (M.p (x/t)) := by
  unfold Model.pstar
  have hstar : M.lstar ∈ M.Λ \ {0} := ⟨star_mem M,by simpa using hs.ne'⟩
  have hrun : x/t ∈ M.Λ \ {0} := ⟨hΛ,by simpa using (div_pos hx ht).ne'⟩
  rcases le_total M.lstar (x/t) with h|h
  · rw [min_eq_left h,max_eq_left (M.strictAntiOn.antitoneOn hstar hrun h)]
  · rw [min_eq_right h,max_eq_right (M.strictAntiOn.antitoneOn hrun hstar h)]

end Pricing

theorem solution (M : GVRPricing.FixedPrice.Model) (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    GVRPricing.FixedPrice.IsFeasiblePath M x t (fun _ => min M.lstar (x / t)) ∧
    (∀ ℓ : ℝ → ℝ, GVRPricing.FixedPrice.IsFeasiblePath M x t ℓ →
      ∫ s in (0 : ℝ)..t, M.r (ℓ s) ≤ ∫ s in (0 : ℝ)..t, M.r (min M.lstar (x / t))) ∧
    GVRPricing.FixedPrice.detValue M x t = t * M.r (min M.lstar (x / t)) ∧
    (x ≤ M.lstar * t → GVRPricing.FixedPrice.detValue M x t = t * min M.rstar (M.r (x / t))) ∧
    (M.lstar * t ≤ x → GVRPricing.FixedPrice.detValue M x t = t * M.rstar) ∧
    (0 < M.lstar → 0 < x → x / t ∈ M.Λ →
      M.p (min M.lstar (x / t)) = max M.pstar (M.p (x / t))) := by
  refine ⟨Pricing.constant_feasible M x t hx ht,?_,Pricing.value_eq M x t hx ht,?_,?_,
    Pricing.pricing_price M x t ht⟩
  · intro ℓ hℓ
    simpa using Pricing.revenue_optimal M x t hx ht ℓ hℓ
  · intro h
    have hr : x/t≤M.lstar := (div_le_iff₀ ht).mpr h
    have hm : x/t∈M.Λ := Pricing.interval_mem M ⟨div_nonneg hx ht.le,hr⟩
    rw [Pricing.value_eq M x t hx ht,min_eq_right hr,min_eq_right (Pricing.r_le_star M hm)]
  · intro h
    have hr : M.lstar≤x/t := (le_div_iff₀ ht).mpr h
    rw [Pricing.value_eq M x t hx ht,min_eq_left hr]
    rfl
#print axioms solution
