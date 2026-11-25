-- Prove2me | solution 1 for CorrelatedRounding.display_p12
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-25T20:24:30.168895+00:00
-- url     : https://prove2.me/submissions/f315c7b3-3780-4a82-bef9-9416408d39c9

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_y
import Definitions.Def_CorrelatedRounding_clock
import Definitions.Def_CorrelatedRounding_IsAlg1Output
import Definitions.Def_CorrelatedRounding_IsAlg1Draw
import Theorems.Thm_CorrelatedRounding_dilation_claim
import Theorems.Thm_CorrelatedRounding_integral_p12

open MeasureTheory ProbabilityTheory

namespace CRDisplayP12

open CorrelatedRounding

lemma exp_Iic {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    expMeasure r (Set.Iic x) = ENNReal.ofReal (1 - Real.exp (-(r * x))) := by
  have := isProbabilityMeasure_expMeasure hr
  rw [← ofReal_cdf, cdf_expMeasure_eq hr, if_pos hx]

lemma exp_Ici_le {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    expMeasure r (Set.Ici x) ≤ ENNReal.ofReal (Real.exp (-(r * x))) := by
  have := isProbabilityMeasure_expMeasure hr
  have hsing : expMeasure r {x} = 0 := by
    unfold expMeasure gammaMeasure
    exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)
  have he : Real.exp (-(r * x)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  rw [← Set.Ioi_union_left]
  refine (measure_union_le _ _).trans ?_
  rw [hsing, add_zero, ← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, exp_Iic hr hx]
  rw [tsub_le_iff_right, ← ENNReal.ofReal_add (Real.exp_pos _).le (by linarith)]
  simp

lemma lintegral_tail {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ x, (Set.Ioi t).indicator (fun x => ENNReal.ofReal (Real.exp (-((1 - r) * x)))) x
        ∂(expMeasure r) = ENNReal.ofReal (r * Real.exp (-t)) := by
  rw [lintegral_indicator measurableSet_Ioi]
  unfold expMeasure gammaMeasure
  rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _ (f := gammaPDF 1 r)
    (by exact (measurable_gammaPDFReal 1 r).ennreal_ofReal) _ measurableSet_Ioi
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun x => ENNReal.ofReal (r * Real.exp (-x)))]
  · rw [← ofReal_integral_eq_lintegral_ofReal, integral_const_mul, integral_exp_neg_Ioi]
    · simpa using (exp_neg_integrableOn_Ioi t one_pos).const_mul r
    · exact ae_of_all _ fun x => by positivity
  · intro x hx
    have hx0 : 0 ≤ x := ht.trans (le_of_lt hx)
    simp only [Pi.mul_apply]
    change exponentialPDF r x * _ = _
    rw [exponentialPDF_of_nonneg hx0, ← ENNReal.ofReal_mul (by positivity), mul_assoc,
      ← Real.exp_add]
    congr 3; ring

lemma argmin {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (W : ι → Ω → ℝ) (r : ι → ℝ)
    (hW : iIndepFun W μ) (hlaw : ∀ κ, HasLaw (W κ) (expMeasure (r κ)) μ)
    (hr : ∀ κ, 0 < r κ) (hsum : ∑ κ, r κ = 1) (kk : ι) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < W kk ω ∧ ∀ κ, κ ≠ kk → W kk ω ≤ W κ ω} ≤
      ENNReal.ofReal (r kk * Real.exp (-t)) := by
  set T : Finset ι := Finset.univ.erase kk with hT
  have hind := hW.indepFun_finset₀ {kk} T (by simp [hT]) (fun κ => (hlaw κ).aemeasurable)
  let V : Ω → (T → ℝ) := fun ω κ => W κ ω
  have hind2 : IndepFun (W kk) V μ :=
    hind.comp (φ := fun g : ({kk} : Finset ι) → ℝ => g ⟨kk, by simp⟩) (ψ := id)
      (measurable_pi_apply _) measurable_id
  have hVm : AEMeasurable V μ := aemeasurable_pi_lambda _ (fun κ => (hlaw κ).aemeasurable)
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map (hlaw kk).aemeasurable hVm).1 hind2
  set C : Set (ℝ × (T → ℝ)) := {p | t < p.1 ∧ ∀ κ, p.1 ≤ p.2 κ} with hCdef
  have hC : MeasurableSet C := by
    have : C = {p | t < p.1} ∩ ⋂ κ, {p | p.1 ≤ p.2 κ} := by ext; simp [hCdef]
    rw [this]
    refine (measurableSet_lt measurable_const measurable_fst).inter ?_
    exact MeasurableSet.iInter fun κ =>
      measurableSet_le measurable_fst ((measurable_pi_apply κ).comp measurable_snd)
  have hset : {ω | t < W kk ω ∧ ∀ κ, κ ≠ kk → W kk ω ≤ W κ ω} =
      (fun ω => (W kk ω, V ω)) ⁻¹' C := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hCdef, V, Subtype.forall, hT,
      Finset.mem_erase, Finset.mem_univ, and_true]
  rw [hset, ← Measure.map_apply_of_aemeasurable ((hlaw kk).aemeasurable.prodMk hVm) hC, hmap,
    (hlaw kk).map_eq, Measure.prod_apply hC]
  have hinner : ∀ x, (μ.map V) (Prod.mk x ⁻¹' C) ≤
      (Set.Ioi t).indicator (fun x => ENNReal.ofReal (Real.exp (-((1 - r kk) * x)))) x := by
    intro x
    by_cases hx : t < x
    · rw [Set.indicator_of_mem (show x ∈ Set.Ioi t from hx)]
      have hx0 : 0 ≤ x := ht.trans hx.le
      have hpre : Prod.mk x ⁻¹' C = Set.univ.pi (fun _ : T => Set.Ici x) := by
        ext v
        simp only [hCdef, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Ici, hx,
          true_and]
      rw [hpre, Measure.map_apply_of_aemeasurable hVm (MeasurableSet.univ_pi fun _ => measurableSet_Ici)]
      have h1 : V ⁻¹' Set.univ.pi (fun _ : T => Set.Ici x) = ⋂ κ ∈ T, W κ ⁻¹' Set.Ici x := by
        ext ω
        simp only [V, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ici, Set.mem_iInter,
          Subtype.forall]
      rw [h1, hW.measure_inter_preimage_eq_mul T (fun _ _ => measurableSet_Ici)]
      calc ∏ κ ∈ T, μ (W κ ⁻¹' Set.Ici x)
          ≤ ∏ κ ∈ T, ENNReal.ofReal (Real.exp (-(r κ * x))) := by
            refine Finset.prod_le_prod' fun κ _ => ?_
            have := (hlaw κ).measure_eq (p := fun z => x ≤ z) measurableSet_Ici
            rw [show W κ ⁻¹' Set.Ici x = {ω | x ≤ W κ ω} from rfl, this]
            exact exp_Ici_le (hr κ) hx0
        _ = ENNReal.ofReal (Real.exp (-((1 - r kk) * x))) := by
            rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum]
            congr 2
            have : ∑ κ ∈ T, r κ = 1 - r kk := by
              rw [← hsum, hT, ← Finset.add_sum_erase _ _ (Finset.mem_univ kk)]; ring
            rw [Finset.sum_neg_distrib, ← Finset.sum_mul, this]
    · have hpre : Prod.mk x ⁻¹' C = ∅ := by ext v; simp [hCdef, hx]
      rw [hpre, measure_empty]; exact bot_le
  exact (lintegral_mono hinner).trans (lintegral_tail (hr kk) ht).le

end CRDisplayP12

open CorrelatedRounding in
theorem solution {q K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {u : Fin K → Fin q → ℝ} (hu : IsInstance u) {E : Fin K → Ω → ℝ}
    (hE : IsAlg1Draw u μ E) (k : Fin K) (hk : 0 < y u k) (G : ℕ → Ω → ℝ)
    (hG : ∀ j, HasLaw (G j) (expMeasure (y u k)) μ) (hind : iIndepFun (Sum.elim E G) μ)
    (S : ℕ → Ω → ℝ) (hS0 : ∀ ω, S 0 ω = E k ω) (hS : ∀ j ω, S (j + 1) ω = S j ω + G j ω) :
    μ (⋃ i ∈ {i | 0 < u k i}, ⋃ j, {ω |
        (∀ k', k' ≠ k →
          ((y u k / u k i * S j ω : ℝ) : EReal) ≤ clock u (fun k'' => E k'' ω) k' i) ∧
        ∀ j' < j, y u k / u k i * S j ω ≤ y u k / u k i * S j' ω}) ≤
      ENNReal.ofReal (y u k * ∫ t in Set.Ioi (0 : ℝ), min ((q : ℝ) * Real.exp (-t)) 1) := by
  classical
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have : (⋃ i ∈ {i : Fin 0 | 0 < u k i}, ⋃ j, {ω |
        (∀ k', k' ≠ k →
          ((y u k / u k i * S j ω : ℝ) : EReal) ≤ clock u (fun k'' => E k'' ω) k' i) ∧
        ∀ j' < j, y u k / u k i * S j ω ≤ y u k / u k i * S j' ω}) = ∅ := by
      ext ω; simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
      rintro ⟨i, _⟩; exact i.elim0
    rw [this, measure_empty]; exact bot_le
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hint := CorrelatedRounding.integral_p12 q hq
  rw [hint.1.trans (hint.2.1.trans hint.2.2)]
  set s0 := Real.log q with hs0
  have hs0nn : 0 ≤ s0 := Real.log_nonneg hq1
  set N := ⋃ m, {ω | G m ω ≤ 0} with hN
  set B := {ω | E k ω ≤ s0} with hB
  set A : Fin q → Set Ω := fun i => {ω | 0 < u k i ∧ s0 < E k ω ∧
    ∀ k', k' ≠ k → ((y u k / u k i * E k ω : ℝ) : EReal) ≤ clock u (fun k'' => E k'' ω) k' i}
    with hA
  have hsub : (⋃ i ∈ {i | 0 < u k i}, ⋃ j, {ω |
        (∀ k', k' ≠ k →
          ((y u k / u k i * S j ω : ℝ) : EReal) ≤ clock u (fun k'' => E k'' ω) k' i) ∧
        ∀ j' < j, y u k / u k i * S j ω ≤ y u k / u k i * S j' ω}) ⊆ N ∪ B ∪ ⋃ i, A i := by
    intro ω hω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hω
    obtain ⟨i, hi, j, h1, h2⟩ := hω
    rcases j with _ | j
    · by_cases hb : E k ω ≤ s0
      · exact Or.inl (Or.inr hb)
      · refine Or.inr (Set.mem_iUnion.2 ⟨i, hi, lt_of_not_ge hb, ?_⟩)
        intro k' hk'; have := h1 k' hk'; rwa [hS0] at this
    · by_contra hn
      have hpos : ∀ m, 0 < G m ω := by
        intro m; by_contra hm
        exact hn (Or.inl (Or.inl (Set.mem_iUnion.2 ⟨m, le_of_not_gt hm⟩)))
      have hmono : ∀ n, S 0 ω < S (n + 1) ω := by
        intro n; induction n with
        | zero => rw [hS]; linarith [hpos 0]
        | succ n ih => rw [hS]; linarith [hpos (n + 1)]
      have hc : 0 < y u k / u k i := div_pos hk hi
      have := h2 0 (Nat.succ_pos _)
      have := le_of_mul_le_mul_left this hc
      linarith [hmono j]
  have hNnull : μ N = 0 := by
    refine measure_iUnion_null (fun m => ?_)
    rw [(hG m).measure_eq measurableSet_Iic]
    change expMeasure _ (Set.Iic 0) = 0
    rw [CRDisplayP12.exp_Iic hk le_rfl]
    simp
  have hBle : μ B ≤ ENNReal.ofReal (y u k * s0) := by
    rw [(hE.2 k hk).measure_eq measurableSet_Iic]
    change expMeasure _ (Set.Iic s0) ≤ _
    rw [CRDisplayP12.exp_Iic hk hs0nn]
    apply ENNReal.ofReal_le_ofReal
    linarith [Real.add_one_le_exp (-(y u k * s0))]
  have hAle : ∀ i, μ (A i) ≤ ENNReal.ofReal (y u k * Real.exp (-s0)) := by
    intro i
    by_cases hi : 0 < u k i
    · obtain ⟨hWi, hWl⟩ := CorrelatedRounding.dilation_claim hu hE i
      set c := y u k / u k i with hc
      have hcpos : 0 < c := div_pos hk hi
      have huy : u k i ≤ y u k := le_ciSup (Set.finite_range (u k)).bddAbove i
      have hc1 : 1 ≤ c := by rw [hc, le_div_iff₀ hi]; linarith
      have hsum : ∑ κ : {k' : Fin K // 0 < u k' i}, u κ.1 i = 1 := by
        rw [← hu.2 i, ← Finset.sum_subtype (Finset.univ.filter (fun k' => 0 < u k' i))
          (p := fun k' => 0 < u k' i) (by simp) (fun k' => u k' i)]
        exact Finset.sum_filter_of_ne (fun k' _ h => lt_of_le_of_ne (hu.1 k' i) (Ne.symm h))
      have key := CRDisplayP12.argmin
        (fun (κ : {k' : Fin K // 0 < u k' i}) ω => y u κ / u κ i * E κ ω)
        (fun κ => u κ.1 i) hWi hWl (fun κ => κ.2) hsum ⟨k, hi⟩
        (mul_nonneg hcpos.le hs0nn)
      refine le_trans (measure_mono ?_) (key.trans ?_)
      · intro ω hω
        obtain ⟨_, h1, h2⟩ := hω
        refine ⟨mul_lt_mul_of_pos_left h1 hcpos, fun κ hκ => ?_⟩
        have hne : κ.1 ≠ k := fun h => hκ (Subtype.ext h)
        have := h2 κ.1 hne
        simp only [clock, if_neg (ne_of_gt κ.2)] at this
        exact EReal.coe_le_coe_iff.1 this
      · apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul huy _ (Real.exp_pos _).le hk.le
        apply Real.exp_le_exp.2
        nlinarith
    · have : A i = ∅ := by
        ext ω; simp only [hA, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hi h.1
      rw [this, measure_empty]; exact bot_le
  calc _ ≤ μ (N ∪ B ∪ ⋃ i, A i) := measure_mono hsub
    _ ≤ μ N + μ B + μ (⋃ i, A i) := by
        refine (measure_union_le _ _).trans ?_
        gcongr; exact measure_union_le _ _
    _ ≤ 0 + ENNReal.ofReal (y u k * s0) + ∑ i, ENNReal.ofReal (y u k * Real.exp (-s0)) := by
        rw [hNnull]; gcongr
        exact (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ => hAle i)
    _ = ENNReal.ofReal (y u k * (1 + s0)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, zero_add, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [hs0, Real.exp_neg, Real.exp_log (by linarith)]
        field_simp
        ring
