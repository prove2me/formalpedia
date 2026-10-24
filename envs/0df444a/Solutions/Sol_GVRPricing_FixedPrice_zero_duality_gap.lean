-- Prove2me | solution 1 for GVRPricing.FixedPrice.zero_duality_gap
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T21:07:21.943269+00:00
-- url     : https://prove2.me/submissions/10941c69-4769-406f-a5b5-5f20511d6702

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

theorem prior_deterministic (M : GVRPricing.FixedPrice.Model) (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
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
#print axioms prior_deterministic

open MeasureTheory Set Function Classical
noncomputable section
namespace Pricing
open GVRPricing.FixedPrice

theorem supporting_price (M : Model) (q : ℝ) (hq : 0 < q) (hqs : q < M.lstar) :
    ∃ μ : ℝ, 0 ≤ μ ∧ ∀ l ∈ M.Λ, M.r l ≤ M.r q + μ*(l-q) := by
  have hqΛ : q ∈ M.Λ := interval_mem M ⟨hq.le,hqs.le⟩
  let slopes : Set ℝ := (fun z : ℝ => (M.r z-M.r q)/(z-q)) '' {z | z ∈ M.Λ ∧ q<z}
  have hstar : (M.r M.lstar-M.r q)/(M.lstar-q) ∈ slopes :=
    ⟨M.lstar,⟨star_mem M,hqs⟩,rfl⟩
  have hne : slopes.Nonempty := ⟨_,hstar⟩
  have hbound : BddAbove slopes := by
    refine ⟨(M.r q-M.r 0)/(q-0),?_⟩
    rintro z ⟨l,hl,rfl⟩
    exact M.concaveOn.slope_anti_adjacent M.zero_mem hl.1 hq hl.2
  refine ⟨sSup slopes,?_,?_⟩
  · exact (div_nonneg (sub_nonneg.mpr (r_le_star M hqΛ)) (sub_pos.mpr hqs).le).trans (le_csSup hbound hstar)
  · intro l hl
    rcases lt_trichotomy l q with h|rfl|h
    · have hsup : sSup slopes ≤ (M.r q-M.r l)/(q-l) := by
        apply csSup_le hne
        rintro z ⟨z,hz,rfl⟩
        exact M.concaveOn.slope_anti_adjacent hl hz.1 h hz.2
      have hh := (le_div_iff₀ (sub_pos.mpr h)).mp hsup
      nlinarith
    · simp
    · have hh : (M.r l-M.r q)/(l-q) ≤ sSup slopes := le_csSup hbound ⟨l,⟨hl,h⟩,rfl⟩
      have hh := (div_le_iff₀ (sub_pos.mpr h)).mp hh
      nlinarith
#print axioms supporting_price
end Pricing

open MeasureTheory Set Function Classical
noncomputable section
namespace Pricing
open GVRPricing.FixedPrice

def augSet (M : Model) (t μ : ℝ) : Set ℝ :=
  (fun ℓ : ℝ → ℝ => ∫ s in (0:ℝ)..t,(M.r (ℓ s)-μ*ℓ s)) '' {ℓ | IsRatePath M t ℓ}

lemma constant_rate (M : Model) (t q : ℝ) (hq : q ∈ M.Λ) : IsRatePath M t (fun _ => q) :=
  ⟨measurable_const,fun s hs => hq,intervalIntegrable_const⟩
lemma aug_integrable (M : Model) (t μ : ℝ) (ht : 0 ≤ t) (ℓ : ℝ → ℝ) (hℓ : IsRatePath M t ℓ) :
    IntervalIntegrable (fun s => M.r (ℓ s)-μ*ℓ s) volume 0 t := by
  have hr : IntervalIntegrable (fun s => M.r (ℓ s)) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr (revenue_integrable M t ℓ hℓ)
  exact hr.sub (hℓ.2.2.const_mul μ)
lemma aug_nonempty (M : Model) (t μ : ℝ) : (augSet M t μ).Nonempty :=
  ⟨_,⟨fun _ => 0,constant_rate M t 0 M.zero_mem,rfl⟩⟩
lemma aug_bounded (M : Model) (t μ : ℝ) (ht : 0 ≤ t) (hμ : 0 ≤ μ) : BddAbove (augSet M t μ) := by
  refine ⟨t*M.rstar,?_⟩
  rintro y ⟨ℓ,hℓ,rfl⟩
  have hi := intervalIntegral.integral_mono_on ht (aug_integrable M t μ ht ℓ hℓ)
    (intervalIntegrable_const (c := M.rstar)) (fun s hs =>
      (sub_le_self _ (mul_nonneg hμ (M.nonneg _ (hℓ.2.1 s hs)))).trans (r_le_star M (hℓ.2.1 s hs)))
  simpa using hi

lemma constant_aug_le (M : Model) (x t μ q : ℝ) (ht : 0 ≤ t) (hμ : 0 ≤ μ) (hq : q ∈ M.Λ) :
    t*(M.r q-μ*q)+x*μ ≤ detAugValue M x t μ := by
  have hmem : t*(M.r q-μ*q) ∈ augSet M t μ := by
    refine ⟨fun _ => q,constant_rate M t q hq,?_⟩
    simp <;> ring
  change t*(M.r q-μ*q)+x*μ ≤ sSup (augSet M t μ)+x*μ
  linarith [le_csSup (aug_bounded M t μ ht hμ) hmem]

theorem weak_duality (M : Model) (x t μ : ℝ) (hx : 0 ≤ x) (ht : 0 < t) (hμ : 0 ≤ μ) :
    detValue M x t ≤ detAugValue M x t μ := by
  let q := min M.lstar (x/t)
  have hq := interval_mem M (chosen_mem M x t hx ht)
  have hc := constant_aug_le M x t μ q ht.le hμ hq
  rw [value_eq M x t hx ht]
  have hqx : t*q≤x := by
    calc _ ≤ t*(x/t) := mul_le_mul_of_nonneg_left (min_le_right _ _) ht.le
         _ = x := mul_div_cancel₀ x ht.ne'
  have := mul_nonneg hμ (sub_nonneg.mpr hqx)
  nlinarith

lemma aug_support_upper (M : Model) (x t μ q : ℝ) (ht : 0 ≤ t)
    (hs : ∀ l ∈ M.Λ,M.r l ≤ M.r q+μ*(l-q)) :
    detAugValue M x t μ ≤ t*(M.r q-μ*q)+x*μ := by
  have hb : sSup (augSet M t μ) ≤ t*(M.r q-μ*q) := by
    apply csSup_le (aug_nonempty M t μ)
    rintro y ⟨ℓ,hℓ,rfl⟩
    have hpoint (s : ℝ) (hs' : s ∈ Icc 0 t) : M.r (ℓ s)-μ*ℓ s ≤ M.r q-μ*q := by
      have := hs (ℓ s) (hℓ.2.1 s hs')
      linarith
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] using intervalIntegral.integral_mono_on ht (aug_integrable M t μ ht ℓ hℓ)
      intervalIntegrable_const hpoint
  change sSup (augSet M t μ)+x*μ ≤ t*(M.r q-μ*q)+x*μ
  linarith

theorem dual_attained (M : Model) (x t : ℝ) (hx : 0 < x) (ht : 0 < t) :
    ∃ μ : ℝ, 0 ≤ μ ∧ detAugValue M x t μ = detValue M x t := by
  by_cases hs : M.lstar ≤ x/t
  · refine ⟨0,le_rfl,le_antisymm ?_ (weak_duality M x t 0 hx.le ht le_rfl)⟩
    have hu := aug_support_upper M x t 0 M.lstar ht.le (fun l hl => by simpa [Model.rstar] using r_le_star M hl)
    simpa [value_eq M x t hx.le ht,min_eq_left hs] using hu
  · have hq : x/t<M.lstar := lt_of_not_ge hs
    obtain ⟨μ,hμ,hsl⟩ := supporting_price M (x/t) (div_pos hx ht) hq
    refine ⟨μ,hμ,le_antisymm ?_ (weak_duality M x t μ hx.le ht hμ)⟩
    have hu := aug_support_upper M x t μ (x/t) ht.le hsl
    rw [value_eq M x t hx.le ht,min_eq_right hq.le]
    have he : t*(M.r (x/t)-μ*(x/t))+x*μ = t*M.r (x/t) := by
      field_simp
      <;> ring
    exact hu.trans_eq he
end Pricing

open MeasureTheory Set
noncomputable section

theorem solution (M : GVRPricing.FixedPrice.Model) (n : ℕ) (t : ℝ) (hn : 0 < n) (ht : 0 < t) :
    IsLeast ((fun μ => GVRPricing.FixedPrice.detAugValue M n t μ) '' Ici 0)
      (GVRPricing.FixedPrice.detValue M n t) := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  constructor
  · obtain ⟨μ,hμ,he⟩ := Pricing.dual_attained M n t hn' ht
    exact ⟨μ,hμ,he⟩
  · rintro y ⟨μ,hμ,rfl⟩
    exact Pricing.weak_duality M n t μ hn'.le ht hμ
#print axioms solution
