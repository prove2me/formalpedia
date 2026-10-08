-- Prove2me | solution 1 for ChatterjeeSamuelson.LinkedODE.linked_differential_equations
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-06T04:15:32.131267+00:00
-- url     : https://prove2.me/submissions/0fb58c18-a5b5-4f6b-b90a-a446ebcdaf83

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_RegularBelief
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_ClassA
import Definitions.Def_ChatterjeeSamuelson_Shared_IsEquilibrium

set_option autoImplicit false

/- Complete checked body: AttributedBargaining -/
section
-- Prove2me | solution 1 for ChatterjeeSamuelson.LinkedODE.offer_cdf_eq_value_cdf
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:48:04.510037+00:00
-- url     : https://prove2.me/submissions/f7ccbf71-097f-45fd-bcde-be18ec83aa62


open MeasureTheory ProbabilityTheory Set

namespace ChatterjeeSamuelson.LinkedODE

/-- Under a regular belief, almost every value lies in `[lo, hi]`. -/
theorem aux_ocdf_ae_mem (μb : Measure ℝ) (loS hiS : ℝ) (fb : ℝ → ℝ)
    (hμb : RegularBelief μb loS hiS fb) : ∀ᵐ x ∂μb, x ∈ Icc loS hiS := by
  obtain ⟨hP, -, hlo, hhi, -, -⟩ := hμb
  have := hP
  have h1 : μb (Iic loS) = 0 := by
    rw [← ofReal_cdf, hlo, ENNReal.ofReal_zero]
  have h2 : μb (Iic hiS) = 1 := by
    rw [← ofReal_cdf, hhi, ENNReal.ofReal_one]
  have h3 : μb (Ioi hiS) = 0 := by
    rw [← compl_Iic, prob_compl_eq_zero_iff measurableSet_Iic]
    exact h2
  have hIio : μb (Iio loS) = 0 := measure_mono_null Iio_subset_Iic_self h1
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_union_null hIio h3)
  intro x hx
  simp only [mem_ofPred_eq, mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr hx

end ChatterjeeSamuelson.LinkedODE

open ChatterjeeSamuelson.LinkedODE

theorem checked_offer_cdf_eq_value_cdf (μb : Measure ℝ) (loS hiS : ℝ) (fb S : ℝ → ℝ)
    (hμb : RegularBelief μb loS hiS fb) (hS : ClassA S loS hiS)
    (a c y : ℝ) (ha : loS ≤ a) (hc : c ≤ hiS) (hy : y ∈ Ioo a c)
    (hmono : StrictMonoOn S (Ioo a c)) :
    (μb {vs | S vs ≤ S y}).toReal = cdf μb y := by
  have hP : IsProbabilityMeasure μb := hμb.1
  obtain ⟨hbddA, hbddB, hmon, hflat, -⟩ := hS
  have hyI : y ∈ Icc loS hiS := ⟨ha.trans hy.1.le, hy.2.le.trans hc⟩
  -- points of `(a, c)` on both sides of `y`
  obtain ⟨y1, hy1a, hy1y⟩ := exists_between hy.1
  obtain ⟨y2, hy2y, hy2c⟩ := exists_between hy.2
  have hy1 : y1 ∈ Ioo a c := ⟨hy1a, hy1y.trans hy.2⟩
  have hy2 : y2 ∈ Ioo a c := ⟨hy.1.trans hy2y, hy2c⟩
  have hy1I : y1 ∈ Icc loS hiS := ⟨ha.trans hy1a.le, (hy1.2.le).trans hc⟩
  have hy2I : y2 ∈ Icc loS hiS := ⟨ha.trans hy2.1.le, hy2c.le.trans hc⟩
  have hS1 : S y1 < S y := hmono hy1 hy hy1y
  have hS2 : S y < S y2 := hmono hy hy2 hy2y
  have hinf : sInf (S '' Icc loS hiS) < S y :=
    lt_of_le_of_lt (csInf_le hbddB (mem_image_of_mem S hy1I)) hS1
  have hsup : S y < sSup (S '' Icc loS hiS) :=
    lt_of_lt_of_le hS2 (le_csSup hbddA (mem_image_of_mem S hy2I))
  -- the two sets agree on `[loS, hiS]`
  have key : ∀ x ∈ Icc loS hiS, (S x ≤ S y ↔ x ≤ y) := by
    intro x hx
    constructor
    · intro h
      by_contra hxy
      rw [not_le] at hxy
      have hge : S y ≤ S x := hmon hyI hx hxy.le
      have heq : S y = S x := le_antisymm hge h
      rcases hflat y hyI x hx (ne_of_lt hxy) heq with h' | h'
      · exact absurd h' (ne_of_gt hinf)
      · exact absurd h' (ne_of_lt hsup)
    · intro h
      exact hmon hx hyI h
  have hae : {vs | S vs ≤ S y} =ᵐ[μb] Iic y := by
    filter_upwards [aux_ocdf_ae_mem μb loS hiS fb hμb] with x hx
    change (S x ≤ S y) = (x ≤ y)
    exact propext (key x hx)
  rw [measure_congr hae, cdf_eq_real, measureReal_def]

end

/- Complete checked body: StrategyRegularity -/
section

open MeasureTheory ProbabilityTheory Set Filter Topology
open ChatterjeeSamuelson.LinkedODE

namespace ChatterjeeSamuelson.LinkedODEProof

noncomputable def clippedStrategy (S : ℝ → ℝ) (lo hi t : ℝ) : ℝ := S (max lo (min hi t))

theorem clip_mem {lo hi : ℝ} (h : lo ≤ hi) (t : ℝ) :
    max lo (min hi t) ∈ Icc lo hi :=
  ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

theorem clippedStrategy_eq {S : ℝ → ℝ} {lo hi t : ℝ} (ht : t ∈ Icc lo hi) :
    clippedStrategy S lo hi t = S t := by
  simp only [clippedStrategy, min_eq_right ht.2, max_eq_right ht.1]

theorem clippedStrategy_monotone (S : ℝ → ℝ) (lo hi : ℝ) (h : lo ≤ hi)
    (hS : ClassA S lo hi) : Monotone (clippedStrategy S lo hi) := by
  intro x y hxy
  exact hS.2.2.1 (clip_mem h x) (clip_mem h y)
    (max_le_max le_rfl (min_le_min le_rfl hxy))

theorem clippedStrategy_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (S : ℝ → ℝ) (lo hi : ℝ) (h : lo ≤ hi) (hS : ClassA S lo hi) :
    Integrable (clippedStrategy S lo hi) μ := by
  obtain ⟨U,hU⟩ := hS.1
  obtain ⟨L,hL⟩ := hS.2.1
  apply Integrable.of_bound (clippedStrategy_monotone S lo hi h hS).measurable.aestronglyMeasurable
    (max |L| |U|)
  apply Eventually.of_forall
  intro t
  have hl := hL (mem_image_of_mem S (clip_mem h t))
  have hu := hU (mem_image_of_mem S (clip_mem h t))
  rw [Real.norm_eq_abs, abs_le]
  change -max |L| |U| ≤ S (max lo (min hi t)) ∧ S (max lo (min hi t)) ≤ max |L| |U|
  constructor
  · have := le_max_left |L| |U|
    have := neg_abs_le L
    linarith
  · exact hu.trans ((le_abs_self U).trans (le_max_right _ _))

theorem clippedStrategy_ae (μ : Measure ℝ) (lo hi : ℝ) (f S : ℝ → ℝ)
    (hμ : RegularBelief μ lo hi f) : clippedStrategy S lo hi =ᵐ[μ] S := by
  filter_upwards [aux_ocdf_ae_mem μ lo hi f hμ] with t ht
  exact clippedStrategy_eq ht

theorem strategy_local_facts (S : ℝ → ℝ) (lo hi : ℝ) (hS : ClassA S lo hi)
    (a c y : ℝ) (ha : lo ≤ a) (hc : c ≤ hi) (hy : y ∈ Ioo a c)
    (hstrict : StrictMonoOn S (Ioo a c)) :
    HasDerivAt S (deriv S y) y ∧
      (∀ u ∈ Icc lo hi, (S u ≤ S y ↔ u ≤ y) ∧ (S y ≤ S u ↔ y ≤ u)) := by
  have hyI : y ∈ Icc lo hi := ⟨ha.trans hy.1.le,hy.2.le.trans hc⟩
  obtain ⟨y1,hy1a,hy1y⟩ := exists_between hy.1
  obtain ⟨y2,hy2y,hy2c⟩ := exists_between hy.2
  have hy1 : y1 ∈ Ioo a c := ⟨hy1a,hy1y.trans hy.2⟩
  have hy2 : y2 ∈ Ioo a c := ⟨hy.1.trans hy2y,hy2c⟩
  have hy1I : y1 ∈ Icc lo hi := ⟨ha.trans hy1a.le,hy1.2.le.trans hc⟩
  have hy2I : y2 ∈ Icc lo hi := ⟨ha.trans hy2.1.le,hy2c.le.trans hc⟩
  have hlow : sInf (S '' Icc lo hi) < S y :=
    (csInf_le hS.2.1 (mem_image_of_mem S hy1I)).trans_lt (hstrict hy1 hy hy1y)
  have hupp : S y < sSup (S '' Icc lo hi) :=
    (hstrict hy hy2 hy2y).trans_le (le_csSup hS.1 (mem_image_of_mem S hy2I))
  have huniq : ∀ u ∈ Icc lo hi, S u = S y → u=y := by
    intro u hu he
    by_contra hne
    rcases hS.2.2.2.1 y hyI u hu (Ne.symm hne) he.symm with h | h
    · exact (ne_of_gt hlow) h
    · exact (ne_of_lt hupp) h
  refine ⟨(hS.2.2.2.2 y ⟨ha.trans_lt hy.1,hy.2.trans_le hc⟩ hlow hupp).hasDerivAt, ?_⟩
  intro u hu
  constructor
  · constructor
    · intro hs
      by_contra! hlt
      have he := le_antisymm hs (hS.2.2.1 hyI hu hlt.le)
      exact (ne_of_gt hlt) (huniq u hu he)
    · exact fun hu' => hS.2.2.1 hu hyI hu'
  · constructor
    · intro hs
      by_contra! hlt
      have he := le_antisymm (hS.2.2.1 hu hyI hlt.le) hs
      exact (ne_of_lt hlt) (huniq u hu he)
    · exact fun hu' => hS.2.2.1 hyI hu hu'

theorem clippedStrategy_continuousAt (S : ℝ → ℝ) (lo hi y : ℝ)
    (hy : y ∈ Ioo lo hi) (hS : ContinuousAt S y) :
    ContinuousAt (clippedStrategy S lo hi) y := by
  apply hS.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hy.1 hy.2] with t ht
  exact clippedStrategy_eq ⟨ht.1.le,ht.2.le⟩

theorem regular_cdf_deriv (μ : Measure ℝ) (lo hi : ℝ) (f : ℝ → ℝ)
    (hμ : RegularBelief μ lo hi f) {y : ℝ} (hy : y ∈ Ioo lo hi) :
    HasDerivAt (fun t => cdf μ t) (f y) y :=
  (hμ.2.2.2.2.2 y ⟨hy.1.le,hy.2.le⟩).hasDerivAt (Icc_mem_nhds hy.1 hy.2)

theorem regular_no_atom (μ : Measure ℝ) (lo hi : ℝ) (f : ℝ → ℝ)
    (hμ : RegularBelief μ lo hi f) {y : ℝ} (hy : y ∈ Ioo lo hi) : μ {y}=0 := by
  have := hμ.1
  have h := (regular_cdf_deriv μ lo hi f hμ hy).continuousAt.continuousWithinAt.leftLim_eq
  rw [← measure_cdf μ, StieltjesFunction.measure_singleton, h, sub_self, ENNReal.ofReal_zero]

end ChatterjeeSamuelson.LinkedODEProof

end

/- Complete checked body: ProfitRepresentation -/
section

open MeasureTheory ProbabilityTheory Set Filter Topology
open ChatterjeeSamuelson.LinkedODE

namespace ChatterjeeSamuelson.LinkedODEProof

theorem strategy_trade_events (μ : Measure ℝ) (lo hi : ℝ) (f S : ℝ → ℝ)
    (hμ : RegularBelief μ lo hi f) (hS : ClassA S lo hi)
    (a c t : ℝ) (ha : lo ≤ a) (hc : c ≤ hi) (ht : t ∈ Ioo a c)
    (hstrict : StrictMonoOn S (Ioo a c)) :
    ∀ᵐ u ∂μ, (S u ≤ S t ↔ u ≤ t) ∧ (S t ≤ S u ↔ t ≤ u) := by
  filter_upwards [aux_ocdf_ae_mem μ lo hi f hμ] with u hu
  exact (strategy_local_facts S lo hi hS a c t ha hc ht hstrict).2 u hu

theorem buyer_profit_eq (μ : Measure ℝ) (lo hi : ℝ) (f S : ℝ → ℝ)
    (hμ : RegularBelief μ lo hi f) (hS : ClassA S lo hi)
    (a c t : ℝ) (ha : lo ≤ a) (hc : c ≤ hi) (ht : t ∈ Ioo a c)
    (hstrict : StrictMonoOn S (Ioo a c)) (k x : ℝ) :
    ChatterjeeSamuelson.Shared.buyerProfit k μ S (S t) x =
      (x-k*S t)*cdf μ t-(1-k)*(∫ u in Iic t, clippedStrategy S lo hi u ∂μ) := by
  have := hμ.1
  have hg := clippedStrategy_integrable μ S lo hi hμ.2.1.le hS
  have he : (fun u => if S u ≤ S t then x-(k*S t+(1-k)*S u) else 0) =ᵐ[μ]
      (Iic t).indicator (fun u => (x-k*S t)-(1-k)*clippedStrategy S lo hi u) := by
    filter_upwards [strategy_trade_events μ lo hi f S hμ hS a c t ha hc ht hstrict,
      clippedStrategy_ae μ lo hi f S hμ] with u hu heq
    by_cases hut : u ≤ t
    · rw [if_pos (hu.1.mpr hut), indicator_of_mem (show u ∈ Iic t from hut), heq]
      ring
    · rw [if_neg (fun h => hut (hu.1.mp h)), indicator_of_notMem (show u ∉ Iic t from hut)]
  unfold ChatterjeeSamuelson.Shared.buyerProfit
  rw [integral_congr_ae he, integral_indicator measurableSet_Iic]
  have hconst : IntegrableOn (fun _ : ℝ => x-k*S t) (Iic t) μ := integrable_const _
  rw [integral_sub hconst (hg.integrableOn.const_mul (1-k)), integral_const_mul, setIntegral_const]
  rw [← cdf_eq_real, smul_eq_mul]
  ring

theorem seller_profit_eq (μ : Measure ℝ) (lo hi : ℝ) (f B : ℝ → ℝ)
    (hμ : RegularBelief μ lo hi f) (hB : ClassA B lo hi)
    (a c t : ℝ) (ha : lo ≤ a) (hc : c ≤ hi) (ht : t ∈ Ioo a c)
    (hstrict : StrictMonoOn B (Ioo a c)) (k y : ℝ) :
    ChatterjeeSamuelson.Shared.sellerProfit k μ B (B t) y =
      k*((∫ u, clippedStrategy B lo hi u ∂μ)-(∫ u in Iic t, clippedStrategy B lo hi u ∂μ))+
        ((1-k)*B t-y)*(1-cdf μ t) := by
  have := hμ.1
  have hg := clippedStrategy_integrable μ B lo hi hμ.2.1.le hB
  have hatom := regular_no_atom μ lo hi f hμ ⟨ha.trans_lt ht.1,ht.2.trans_le hc⟩
  have hne : ∀ᵐ u ∂μ, u ≠ t := by
    simpa [ae_iff] using hatom
  have he : (fun u => if B t ≤ B u then k*B u+(1-k)*B t-y else 0) =ᵐ[μ]
      (Ioi t).indicator (fun u => k*clippedStrategy B lo hi u+((1-k)*B t-y)) := by
    filter_upwards [strategy_trade_events μ lo hi f B hμ hB a c t ha hc ht hstrict,
      clippedStrategy_ae μ lo hi f B hμ, hne] with u hu heq hne
    have hcut : B t ≤ B u ↔ t < u := hu.2.trans (le_iff_lt_or_eq.trans
      (or_iff_left (Ne.symm hne)))
    by_cases hut : t < u
    · rw [if_pos (hcut.mpr hut), indicator_of_mem (show u ∈ Ioi t from hut), heq]
      ring
    · rw [if_neg (fun h => hut (hcut.mp h)), indicator_of_notMem (show u ∉ Ioi t from hut)]
  unfold ChatterjeeSamuelson.Shared.sellerProfit
  rw [integral_congr_ae he, integral_indicator measurableSet_Ioi]
  have hconst : IntegrableOn (fun _ : ℝ => (1-k)*B t-y) (Ioi t) μ := integrable_const _
  rw [integral_add (hg.integrableOn.const_mul k) hconst, integral_const_mul, setIntegral_const]
  have hint : (∫ u in Ioi t, clippedStrategy B lo hi u ∂μ) =
      (∫ u, clippedStrategy B lo hi u ∂μ)-(∫ u in Iic t, clippedStrategy B lo hi u ∂μ) := by
    simpa only [compl_Iic] using setIntegral_compl measurableSet_Iic hg
  have hmass : μ.real (Ioi t) = 1-cdf μ t := by
    rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, ← cdf_eq_real]
  rw [hint, hmass, smul_eq_mul]
  ring

end ChatterjeeSamuelson.LinkedODEProof

end

/- Complete checked body: StieltjesDerivative -/
section

open MeasureTheory ProbabilityTheory Filter Topology Set Asymptotics

namespace ChatterjeeSamuelson.LinkedODEProof

theorem measure_singleton_eq_zero_of_cdf_continuous (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {t : ℝ} (hc : ContinuousAt (fun s => cdf μ s) t) :
    μ {t} = 0 := by
  rw [← measure_cdf μ, StieltjesFunction.measure_singleton,
    hc.continuousWithinAt.leftLim_eq, sub_self, ENNReal.ofReal_zero]

/-- A local derivative of a Stieltjes primitive requires the CDF derivative only at the
evaluation point; no continuous-density or absolute-continuity premise is used. -/
theorem hasDerivAt_cdf_primitive (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : ℝ → ℝ) (hg : Integrable g μ) {t f : ℝ}
    (hc : ContinuousAt g t) (hf : HasDerivAt (fun s => cdf μ s) f t) :
    HasDerivAt (fun s => ∫ u in Iic s, g u ∂μ) (g t * f) t := by
  let A : ℝ → ℝ := fun s => ∫ u in Iic s, g u ∂μ
  have hint : ∀ s, (∫ u in t..s, g u ∂μ) = A s-A t := by
    intro s
    exact (intervalIntegral.integral_Iic_sub_Iic hg.integrableOn hg.integrableOn).symm
  have hFTC := intervalIntegral.measure_integral_sub_linear_isLittleO_of_tendsto_ae
    (a:=t) (l:=𝓝 t) (l':=𝓝 t) (lt:=𝓝 t) (μ:=μ)
    (u:=fun _ : ℝ => t) (v:=fun s : ℝ => s)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter
    (hc.tendsto.mono_left inf_le_left) tendsto_const_nhds tendsto_id
  have ho : (fun s => (A s-A t)-(cdf μ s-cdf μ t)*g t) =o[𝓝 t]
      (fun s => cdf μ s-cdf μ t) := by
    simpa only [hint, intervalIntegral.integral_const_of_cdf, ← cdf_eq_real,
      smul_eq_mul, mul_one] using hFTC
  have herror := (ho.trans_isBigO hf.isBigO_sub).add ((hf.const_mul (g t)).isLittleO)
  rw [hasDerivAt_iff_isLittleO]
  apply herror.congr_left
  intro s
  simp only [smul_eq_mul, A]
  ring

end ChatterjeeSamuelson.LinkedODEProof

end

/- Complete checked body: ComposedDerivatives -/
section

namespace ChatterjeeSamuelson.LinkedODEProof

theorem buyer_composed_derivative {S F A : ℝ → ℝ} {t s f : ℝ}
    (hS : HasDerivAt S s t) (hF : HasDerivAt F f t)
    (hA : HasDerivAt A (S t * f) t) (k x : ℝ) :
    HasDerivAt (fun u => (x-k*S u)*F u-(1-k)*A u)
      ((x-S t)*f-k*F t*s) t := by
  exact ((((hS.const_mul k).const_sub x).mul hF).sub (hA.const_mul (1-k))).congr_deriv (by ring)

theorem seller_composed_derivative {B F A : ℝ → ℝ} {t b f : ℝ}
    (hB : HasDerivAt B b t) (hF : HasDerivAt F f t)
    (hA : HasDerivAt A (B t * f) t) (k y total : ℝ) :
    HasDerivAt (fun u => k*(total-A u)+((1-k)*B u-y)*(1-F u))
      ((y-B t)*f+(1-k)*(1-F t)*b) t := by
  exact (((hA.const_sub total).const_mul k).add
    (((hB.const_mul (1-k)).sub_const y).mul (hF.const_sub 1))).congr_deriv (by ring)

theorem derivative_eq_zero_of_global_max {g : ℝ → ℝ} {t d : ℝ}
    (hd : HasDerivAt g d t) (hmax : ∀ u, g u ≤ g t) : d = 0 := by
  have hm : IsLocalMax g t := Filter.Eventually.of_forall hmax
  exact hm.hasDerivAt_eq_zero hd

end ChatterjeeSamuelson.LinkedODEProof

end

/- Complete checked body: BestResponseEquations -/
section

open MeasureTheory ProbabilityTheory Set Filter Topology
open ChatterjeeSamuelson.LinkedODE

namespace ChatterjeeSamuelson.LinkedODEProof

theorem buyer_best_response_equation (μ : Measure ℝ) (lo hi : ℝ) (f S : ℝ → ℝ)
    (hμ : RegularBelief μ lo hi f) (hS : ClassA S lo hi)
    (a c t : ℝ) (ha : lo ≤ a) (hc : c ≤ hi) (ht : t ∈ Ioo a c)
    (hstrict : StrictMonoOn S (Ioo a c)) (k x : ℝ)
    (hopt : ∀ b, ChatterjeeSamuelson.Shared.buyerProfit k μ S b x ≤
      ChatterjeeSamuelson.Shared.buyerProfit k μ S (S t) x) :
    k*cdf μ t*deriv S t+f t*S t=x*f t := by
  have := hμ.1
  have htI : t ∈ Ioo lo hi := ⟨ha.trans_lt ht.1,ht.2.trans_le hc⟩
  have hs := (strategy_local_facts S lo hi hS a c t ha hc ht hstrict).1
  have hf := regular_cdf_deriv μ lo hi f hμ htI
  have hA := hasDerivAt_cdf_primitive μ (clippedStrategy S lo hi)
    (clippedStrategy_integrable μ S lo hi hμ.2.1.le hS)
    (clippedStrategy_continuousAt S lo hi t htI hs.continuousAt) hf
  rw [clippedStrategy_eq ⟨htI.1.le,htI.2.le⟩] at hA
  have hd := buyer_composed_derivative hs hf hA k x
  have he : (fun u => ChatterjeeSamuelson.Shared.buyerProfit k μ S (S u) x) =ᶠ[𝓝 t]
      (fun u => (x-k*S u)*cdf μ u-(1-k)*(∫ v in Iic u, clippedStrategy S lo hi v ∂μ)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact buyer_profit_eq μ lo hi f S hμ hS a c u ha hc hu hstrict k x
  have hzero := derivative_eq_zero_of_global_max (hd.congr_of_eventuallyEq he)
    (fun u => hopt (S u))
  nlinarith

theorem seller_best_response_equation (μ : Measure ℝ) (lo hi : ℝ) (f B : ℝ → ℝ)
    (hμ : RegularBelief μ lo hi f) (hB : ClassA B lo hi)
    (a c t : ℝ) (ha : lo ≤ a) (hc : c ≤ hi) (ht : t ∈ Ioo a c)
    (hstrict : StrictMonoOn B (Ioo a c)) (k y : ℝ)
    (hopt : ∀ s, ChatterjeeSamuelson.Shared.sellerProfit k μ B s y ≤
      ChatterjeeSamuelson.Shared.sellerProfit k μ B (B t) y) :
    (1-k)*(1-cdf μ t)*deriv B t-f t*B t= -(y*f t) := by
  have := hμ.1
  have htI : t ∈ Ioo lo hi := ⟨ha.trans_lt ht.1,ht.2.trans_le hc⟩
  have hb := (strategy_local_facts B lo hi hB a c t ha hc ht hstrict).1
  have hf := regular_cdf_deriv μ lo hi f hμ htI
  have hA := hasDerivAt_cdf_primitive μ (clippedStrategy B lo hi)
    (clippedStrategy_integrable μ B lo hi hμ.2.1.le hB)
    (clippedStrategy_continuousAt B lo hi t htI hb.continuousAt) hf
  rw [clippedStrategy_eq ⟨htI.1.le,htI.2.le⟩] at hA
  have hd := seller_composed_derivative hb hf hA k y
    (∫ u, clippedStrategy B lo hi u ∂μ)
  have he : (fun u => ChatterjeeSamuelson.Shared.sellerProfit k μ B (B u) y) =ᶠ[𝓝 t]
      (fun u => k*((∫ v, clippedStrategy B lo hi v ∂μ)-
        (∫ v in Iic u, clippedStrategy B lo hi v ∂μ))+((1-k)*B u-y)*(1-cdf μ u)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact seller_profit_eq μ lo hi f B hμ hB a c u ha hc hu hstrict k y
  have hzero := derivative_eq_zero_of_global_max (hd.congr_of_eventuallyEq he)
    (fun u => hopt (B u))
  nlinarith

end ChatterjeeSamuelson.LinkedODEProof

end

/- Complete checked body: BargainingRoot -/
section

open MeasureTheory ProbabilityTheory Set

namespace ChatterjeeSamuelson.LinkedODE

/-- **Theorem 2** (Chatterjee & Samuelson, *Bargaining under Incomplete Information*,
Oper. Res. 31(5) 1983, §2, p. 840 [PDF 6]): "In a class A equilibrium, over intervals of
reservation prices for which the offer strategies are strictly increasing, S( ) and B( )
must satisfy the linked differential equations
  kF_b(y)S′(y) + f_b(y)S(y) = B⁻¹(S(y))f_b(y)   (3a)
  (1 − k)(1 − F_s(x))B′(x) − f_s(x)B(x) = −S⁻¹(B(x))f_s(x).   (3b)"

Setting: `0 ≤ k ≤ 1`; seller values in `[loS, hiS]`, buyer values in `[loB, hiB]`; the
buyer's belief `μb` about `v_s` is regular on `[loS, hiS]` with CDF `F_b = cdf μb` and
density `fb`; the seller's belief `μs` about `v_b` is regular on `[loB, hiB]` with
`F_s = cdf μs` and density `fs`; `(S, B)` is an equilibrium and both strategies are of
class `A`. Then
* (3a) holds at every seller value `y` interior to an open interval `(a, c) ⊆ [loS, hiS]`
  on which `S` is strictly increasing, for every buyer value `x ∈ [loB, hiB]` with
  `B x = S y` (the paper's `B⁻¹(S(y))`);
* (3b) holds at every buyer value `x` interior to an open interval `(a, c) ⊆ [loB, hiB]`
  on which `B` is strictly increasing, for every seller value `y ∈ [loS, hiS]` with
  `S y = B x` (the paper's `S⁻¹(B(x))`).

*Formalization Note.* `S′(y)` is `deriv S y`; class `A` makes `S` differentiable there.
No sign condition on `S′(y)` is assumed. `B⁻¹` and `S⁻¹` are not introduced as functions:
the inverse image is a bound variable, so the equations are asserted exactly where the
paper's inverse is defined. -/
theorem linked_differential_equations (k : ℝ) (_hk0 : 0 ≤ k) (_hk1 : k ≤ 1)
    (μb μs : Measure ℝ) (loS hiS loB hiB : ℝ) (fb fs S B : ℝ → ℝ)
    (hμb : RegularBelief μb loS hiS fb) (hμs : RegularBelief μs loB hiB fs)
    (hEq : Shared.IsEquilibrium k μb μs loS hiS loB hiB S B)
    (hS : ClassA S loS hiS) (hB : ClassA B loB hiB) :
    (∀ a c y : ℝ, loS ≤ a → c ≤ hiS → y ∈ Ioo a c → StrictMonoOn S (Ioo a c) →
      ∀ x ∈ Icc loB hiB, B x = S y →
        k * cdf μb y * deriv S y + fb y * S y = x * fb y) ∧
    (∀ a c x : ℝ, loB ≤ a → c ≤ hiB → x ∈ Ioo a c → StrictMonoOn B (Ioo a c) →
      ∀ y ∈ Icc loS hiS, S y = B x →
        (1 - k) * (1 - cdf μs x) * deriv B x - fs x * B x = -(y * fs x)) := by
  constructor
  · intro a c y ha hc hy hstrict x hx hmatch
    apply ChatterjeeSamuelson.LinkedODEProof.buyer_best_response_equation
      μb loS hiS fb S hμb hS a c y ha hc hy hstrict k x
    intro b
    simpa only [hmatch] using hEq.1 x hx b
  · intro a c x ha hc hx hstrict y hy hmatch
    apply ChatterjeeSamuelson.LinkedODEProof.seller_best_response_equation
      μs loB hiB fs B hμs hB a c x ha hc hx hstrict k y
    intro s
    simpa only [hmatch] using hEq.2 y hy s

end ChatterjeeSamuelson.LinkedODE

end

open ChatterjeeSamuelson ChatterjeeSamuelson.LinkedODE
open MeasureTheory ProbabilityTheory Set


theorem solution (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (μb μs : Measure ℝ) (loS hiS loB hiB : ℝ) (fb fs S B : ℝ → ℝ)
    (hμb : RegularBelief μb loS hiS fb) (hμs : RegularBelief μs loB hiB fs)
    (hEq : Shared.IsEquilibrium k μb μs loS hiS loB hiB S B)
    (hS : ClassA S loS hiS) (hB : ClassA B loB hiB) :
    (∀ a c y : ℝ, loS ≤ a → c ≤ hiS → y ∈ Ioo a c → StrictMonoOn S (Ioo a c) →
      ∀ x ∈ Icc loB hiB, B x = S y →
        k * cdf μb y * deriv S y + fb y * S y = x * fb y) ∧
    (∀ a c x : ℝ, loB ≤ a → c ≤ hiB → x ∈ Ioo a c → StrictMonoOn B (Ioo a c) →
      ∀ y ∈ Icc loS hiS, S y = B x →
        (1 - k) * (1 - cdf μs x) * deriv B x - fs x * B x = -(y * fs x)) := by
  exact ChatterjeeSamuelson.LinkedODE.linked_differential_equations k hk0 hk1 μb μs loS hiS loB hiB fb fs S B hμb hμs hEq hS hB

#print axioms ChatterjeeSamuelson.LinkedODE.linked_differential_equations
#print axioms solution
