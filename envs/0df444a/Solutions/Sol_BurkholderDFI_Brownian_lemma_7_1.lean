-- Prove2me | solution 1 for BurkholderDFI.Brownian.lemma_7_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:16:12.750928+00:00
-- url     : https://prove2.me/submissions/6463fe5c-1686-4e34-a637-cc561473c8c5

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Topology

namespace BurkholderDFI.Brownian

open BurkholderDFI.SquareFnLp

/-! ### Finiteness of `Φ` on finite arguments -/

lemma isPhi_ne_top {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} (hΦ : IsPhi Φ c) {x : ℝ≥0∞}
    (hx : x ≠ ⊤) : Φ x ≠ ⊤ := by
  have h0 : Tendsto Φ (𝓝 0) (𝓝 0) := by
    have := hΦ.cont.tendsto 0
    rwa [hΦ.zero] at this
  rw [ENNReal.tendsto_nhds_zero] at h0
  have h1 := h0 1 one_pos
  rw [ENNReal.nhds_zero_basis.eventually_iff] at h1
  obtain ⟨δ, hδ, hδ'⟩ := h1
  obtain ⟨d, hd0, hdδ⟩ := exists_between hδ
  have hΦd : Φ d ≤ 1 := hδ' hdδ
  have hdtop : d ≠ ⊤ := (hdδ.trans_le le_top).ne
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_lt_top hx hd0.ne').ne
  have hxle : x ≤ 2 ^ n * d := by
    calc x = x / d * d := (ENNReal.div_mul_cancel hd0.ne' hdtop).symm
      _ ≤ (n : ℝ≥0∞) * d := mul_le_mul_left hn.le _
      _ ≤ 2 ^ n * d := by
        gcongr
        exact_mod_cast n.lt_two_pow_self.le
  have key : ∀ k : ℕ, Φ (2 ^ k * d) ≤ (c : ℝ≥0∞) ^ k * Φ d := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc Φ (2 ^ (k + 1) * d) = Φ (2 * (2 ^ k * d)) := by ring_nf
        _ ≤ c * Φ (2 ^ k * d) := hΦ.growth _
        _ ≤ c * ((c : ℝ≥0∞) ^ k * Φ d) := mul_le_mul_right ih _
        _ = (c : ℝ≥0∞) ^ (k + 1) * Φ d := by ring
  refine ne_top_of_le_ne_top ?_ ((hΦ.mono hxle).trans (key n))
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    (ne_top_of_le_ne_top ENNReal.one_ne_top hΦd)

/-! ### Pointwise scaling inequalities extend from positive reals to `[0, ∞]` -/

lemma scale_le {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} (hΦ : IsPhi Φ c) {a : ℝ} (ha : 0 < a) {k : ℝ≥0}
    (h : ∀ l : ℝ, 0 < l → Φ (ENNReal.ofReal (a * l)) ≤ k * Φ (ENNReal.ofReal l)) (x : ℝ≥0∞) :
    Φ (ENNReal.ofReal a * x) ≤ k * Φ x := by
  rcases eq_or_ne x ⊤ with hx | hx
  · subst hx
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 ha).ne']
    have h1 : Tendsto (fun n : ℕ => Φ (ENNReal.ofReal a * n)) atTop (𝓝 (Φ ⊤)) := by
      have : Tendsto (fun n : ℕ => ENNReal.ofReal a * (n : ℝ≥0∞)) atTop (𝓝 (ENNReal.ofReal a * ⊤)) :=
        ENNReal.Tendsto.const_mul ENNReal.tendsto_nat_nhds_top (Or.inl ENNReal.top_ne_zero)
      rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 ha).ne'] at this
      exact (hΦ.cont.tendsto _).comp this
    have h2 : Tendsto (fun n : ℕ => (k : ℝ≥0∞) * Φ n) atTop (𝓝 (k * Φ ⊤)) :=
      ENNReal.Tendsto.const_mul ((hΦ.cont.tendsto _).comp ENNReal.tendsto_nat_nhds_top)
        (Or.inr ENNReal.coe_ne_top)
    refine le_of_tendsto_of_tendsto' h1 h2 fun n => ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [hΦ.zero]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have := h n hn'
      rwa [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_natCast] at this
  rcases eq_or_ne x 0 with hx0 | hx0
  · subst hx0; simp [hΦ.zero]
  have hxr : x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hx).symm
  have hpos : 0 < x.toReal := ENNReal.toReal_pos hx0 hx
  rw [hxr, ← ENNReal.ofReal_mul ha.le]
  exact h _ hpos

/-! ### Layer-cake formula for `[0, ∞]`-valued functions -/

lemma layer_cake {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : Ω → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ ω, F ω ∂P = ∫⁻ t in Set.Ioi (0 : ℝ), P {ω | ENNReal.ofReal t < F ω} := by
  by_cases hae : ∀ᵐ ω ∂P, F ω ≠ ⊤
  · have h1 : ∫⁻ ω, F ω ∂P = ∫⁻ ω, ENNReal.ofReal (F ω).toReal ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with ω hω
      rw [ENNReal.ofReal_toReal hω]
    rw [h1, lintegral_eq_lintegral_meas_lt P (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      hF.ennreal_toReal.aemeasurable]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    refine measure_congr ?_
    filter_upwards [hae] with ω hω
    change (t < (F ω).toReal) = (ENNReal.ofReal t < F ω)
    rw [eq_iff_iff, ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) hω]
  · have hS : MeasurableSet {ω | F ω = ⊤} := hF (measurableSet_singleton ⊤)
    have hpos : P {ω | F ω = ⊤} ≠ 0 := by
      intro h0
      apply hae
      rw [ae_iff]
      simpa using h0
    have hL : ∫⁻ ω, F ω ∂P = ⊤ := by
      refine eq_top_iff.2 ?_
      calc (⊤ : ℝ≥0∞) = ∫⁻ ω, {ω | F ω = ⊤}.indicator (fun _ => (⊤ : ℝ≥0∞)) ω ∂P := by
            rw [lintegral_indicator_const hS, ENNReal.top_mul hpos]
        _ ≤ ∫⁻ ω, F ω ∂P := by
            refine lintegral_mono fun ω => ?_
            by_cases hω : F ω = ⊤
            · simp [hω]
            · simp [Set.indicator, hω]
    have hR : ∫⁻ t in Set.Ioi (0 : ℝ), P {ω | ENNReal.ofReal t < F ω} = ⊤ := by
      refine eq_top_iff.2 ?_
      calc (⊤ : ℝ≥0∞) = ∫⁻ t in Set.Ioi (0 : ℝ), P {ω | F ω = ⊤} := by
            rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top hpos]
        _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), P {ω | ENNReal.ofReal t < F ω} := by
            refine lintegral_mono fun t => ?_
            refine measure_mono fun ω hω => ?_
            simp only [Set.mem_ofPred_eq] at hω ⊢
            rw [hω]; exact ENNReal.ofReal_lt_top
    rw [hL, hR]

/-! ### The generalized inverse of `Φ` -/

lemma phi_lt_iff {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} (hΦ : IsPhi Φ c) (s : ℝ≥0∞) (x : ℝ≥0∞) :
    s < Φ x ↔ sSup {y | Φ y ≤ s} < x := by
  set S := {y | Φ y ≤ s} with hS
  have hSne : S.Nonempty := ⟨0, by simp [hS, hΦ.zero]⟩
  have hSc : IsClosed S := isClosed_Iic.preimage hΦ.cont
  have hmem : sSup S ∈ S := hSc.sSup_mem hSne
  constructor
  · intro h
    exact hΦ.mono.reflect_lt (lt_of_le_of_lt hmem h)
  · intro h
    by_contra h'
    push Not at h'
    exact (not_le.2 h) (le_sSup (show x ∈ S from h'))

lemma inv_ne_zero {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} (hΦ : IsPhi Φ c) {s : ℝ≥0∞} (hs : 0 < s) :
    sSup {y | Φ y ≤ s} ≠ 0 := by
  intro h0
  have h0' : Tendsto Φ (𝓝 0) (𝓝 0) := by
    have := hΦ.cont.tendsto 0
    rwa [hΦ.zero] at this
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ≥0∞), Φ x < s :=
    (h0'.eventually_lt_const hs).filter_mono nhdsWithin_le_nhds
  obtain ⟨x, hx1, hx2⟩ := (hev.and self_mem_nhdsWithin).exists
  have : s < Φ x := by
    rw [phi_lt_iff hΦ, h0]
    exact hx2
  exact absurd hx1 (not_lt.2 this.le)

/-- `ofReal l < ofReal b⁻¹ * x ↔ ofReal (b * l) < x` for `b > 0`. -/
lemma lt_inv_mul_iff {b l : ℝ} (hb : 0 < b) (x : ℝ≥0∞) :
    ENNReal.ofReal l < ENNReal.ofReal b⁻¹ * x ↔ ENNReal.ofReal (b * l) < x := by
  rw [ENNReal.ofReal_inv_of_pos hb, ← ENNReal.div_eq_inv_mul,
    ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_pos.2 hb).ne') (Or.inl ENNReal.ofReal_ne_top),
    ENNReal.ofReal_mul hb.le, mul_comm]

lemma measurable_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : Ω → ℝ≥0∞) :
    Measurable fun t : ℝ => P {ω | ENNReal.ofReal t < F ω} :=
  Antitone.measurable fun s t hst => measure_mono fun ω hω =>
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) hω

/-! ### The main estimate at fixed truncation level -/

lemma good_lambda_trunc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) (hΦ : IsPhi Φ c)
    (f g : Ω → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (β δ ε : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hε : 0 < ε)
    (h71 : ∀ l : ℝ, 0 < l →
      P {ω | ENNReal.ofReal (β * l) < g ω ∧ f ω ≤ ENNReal.ofReal (δ * l)}
        ≤ ENNReal.ofReal ε * P {ω | ENNReal.ofReal l < g ω})
    (N : ℕ) :
    ∫⁻ ω, Φ (ENNReal.ofReal β⁻¹ * min (g ω) N) ∂P
      ≤ ENNReal.ofReal ε * ∫⁻ ω, Φ (min (g ω) N) ∂P
        + ∫⁻ ω, Φ (ENNReal.ofReal δ⁻¹ * f ω) ∂P := by
  have hΦm : Measurable Φ := hΦ.cont.measurable
  have hgN : Measurable fun ω => min (g ω) (N : ℝ≥0∞) := hg.min measurable_const
  have hβ0 : 0 < β := by linarith
  rw [layer_cake P (fun ω => Φ (ENNReal.ofReal β⁻¹ * min (g ω) N))
      (hΦm.comp (measurable_const.mul hgN)),
    layer_cake P (fun ω => Φ (min (g ω) N)) (hΦm.comp hgN),
    layer_cake P (fun ω => Φ (ENNReal.ofReal δ⁻¹ * f ω)) (hΦm.comp (measurable_const.mul hf)),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left']
  · refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ≥0∞) < ENNReal.ofReal t := ENNReal.ofReal_pos.2 ht
    set a := sSup {y | Φ y ≤ ENNReal.ofReal t} with ha
    have hiff := phi_lt_iff hΦ (ENNReal.ofReal t)
    simp only [← ha] at hiff
    have ha0 : a ≠ 0 := inv_ne_zero hΦ ht'
    simp only [hiff]
    rcases eq_or_ne a ⊤ with hatop | hatop
    · have : {ω | a < ENNReal.ofReal β⁻¹ * min (g ω) N} = ∅ := by
        ext ω; simp [hatop]
      rw [this, measure_empty]; exact zero_le'
    set l := a.toReal with hl
    have hal : a = ENNReal.ofReal l := (ENNReal.ofReal_toReal hatop).symm
    have hlpos : 0 < l := ENNReal.toReal_pos ha0 hatop
    rw [hal]
    simp only [lt_inv_mul_iff hβ0, lt_inv_mul_iff hδ]
    have hsub : {ω | ENNReal.ofReal (β * l) < min (g ω) N} ⊆
        {ω | ENNReal.ofReal (β * l) < min (g ω) N ∧ f ω ≤ ENNReal.ofReal (δ * l)} ∪
        {ω | ENNReal.ofReal (δ * l) < f ω} := by
      intro ω hω
      by_cases hfω : f ω ≤ ENNReal.ofReal (δ * l)
      · exact Or.inl ⟨hω, hfω⟩
      · exact Or.inr (not_le.1 hfω)
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    gcongr
    by_cases hN : ENNReal.ofReal (β * l) < N
    · have e1 : {ω | ENNReal.ofReal (β * l) < min (g ω) N ∧ f ω ≤ ENNReal.ofReal (δ * l)} =
          {ω | ENNReal.ofReal (β * l) < g ω ∧ f ω ≤ ENNReal.ofReal (δ * l)} := by
        ext ω; simp [hN]
      have hlN : ENNReal.ofReal l < N := by
        refine lt_of_lt_of_le ?_ hN.le
        rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        nlinarith
      have e2 : {ω | ENNReal.ofReal l < min (g ω) N} = {ω | ENNReal.ofReal l < g ω} := by
        ext ω; simp [hlN]
      rw [e1, e2]
      exact h71 l hlpos
    · have e1 : {ω | ENNReal.ofReal (β * l) < min (g ω) N ∧ f ω ≤ ENNReal.ofReal (δ * l)} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro h _
        exact hN (lt_of_lt_of_le h (min_le_right _ _))
      rw [e1, measure_empty]; exact zero_le'
  · exact (measurable_const.mul (measurable_tail P _)).aemeasurable


/-! ### Arithmetic -/

lemma key_arith (I J : ℝ≥0∞) (γ η : ℝ≥0) (ε : ℝ) (hε : 0 < ε) (hγε : (γ : ℝ) * ε < 1)
    (hI : I ≠ ⊤) (h : I ≤ γ * (ENNReal.ofReal ε * I + η * J)) :
    I ≤ ENNReal.ofReal (γ * η / (1 - γ * ε)) * J := by
  have h1 : (0 : ℝ) < 1 - γ * ε := by linarith
  by_cases hJ : J = ⊤
  · subst hJ
    by_cases hγη : (γ : ℝ) * η = 0
    · rcases mul_eq_zero.1 hγη with hγ | hη
      · have hγ' : γ = 0 := by exact_mod_cast hγ
        subst hγ'
        simp at h
        simp [h]
      · have hη' : η = 0 := by exact_mod_cast hη
        subst hη'
        simp only [ENNReal.coe_zero, zero_mul, add_zero] at h
        have hreal : I.toReal ≤ γ * (ε * I.toReal) := by
          have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI)) h
          rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
            ENNReal.toReal_ofReal hε.le] at this
        have hI0 : I.toReal = 0 := by
          have hnn : 0 ≤ I.toReal := ENNReal.toReal_nonneg
          nlinarith
        rw [ENNReal.toReal_eq_zero_iff] at hI0
        rcases hI0 with hI0 | hI0
        · simp [hI0]
        · exact absurd hI0 hI
    · have hpos : 0 < (γ : ℝ) * η / (1 - γ * ε) := by
        have : 0 < (γ : ℝ) * η := lt_of_le_of_ne (by positivity) (Ne.symm hγη)
        positivity
      rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
      exact le_top
  · have hreal : I.toReal ≤ γ * (ε * I.toReal + η * J.toReal) := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI,
          ENNReal.mul_ne_top ENNReal.coe_ne_top hJ⟩)) h
      rwa [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI)
        (ENNReal.mul_ne_top ENNReal.coe_ne_top hJ), ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.coe_toReal, ENNReal.coe_toReal, ENNReal.toReal_ofReal hε.le] at this
    have hfin : I.toReal ≤ γ * η / (1 - γ * ε) * J.toReal := by
      rw [div_mul_eq_mul_div, le_div_iff₀ h1]
      nlinarith
    calc I = ENNReal.ofReal I.toReal := (ENNReal.ofReal_toReal hI).symm
      _ ≤ ENNReal.ofReal (γ * η / (1 - γ * ε) * J.toReal) := ENNReal.ofReal_le_ofReal hfin
      _ = ENNReal.ofReal (γ * η / (1 - γ * ε)) * ENNReal.ofReal J.toReal := by
          rw [ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (γ * η / (1 - γ * ε)) * J := by rw [ENNReal.ofReal_toReal hJ]

/-! ### Lemma 7.1 -/

theorem lemma_7_1_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c)
    (f g : Ω → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (β δ ε : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hε : 0 < ε)
    (h71 : ∀ l : ℝ, 0 < l →
      P {ω | ENNReal.ofReal (β * l) < g ω ∧ f ω ≤ ENNReal.ofReal (δ * l)}
        ≤ ENNReal.ofReal ε * P {ω | ENNReal.ofReal l < g ω})
    (γ η : ℝ≥0)
    (h72 : ∀ l : ℝ, 0 < l →
      Φ (ENNReal.ofReal (β * l)) ≤ γ * Φ (ENNReal.ofReal l) ∧
      Φ (ENNReal.ofReal (δ⁻¹ * l)) ≤ η * Φ (ENNReal.ofReal l))
    (hγε : (γ : ℝ) * ε < 1) :
    ∫⁻ ω, Φ (g ω) ∂P ≤ ENNReal.ofReal (γ * η / (1 - γ * ε)) * ∫⁻ ω, Φ (f ω) ∂P := by
  have hΦm : Measurable Φ := hΦ.cont.measurable
  have hβ0 : 0 < β := by linarith
  -- the truncated estimate
  have hN : ∀ N : ℕ, ∫⁻ ω, Φ (min (g ω) N) ∂P
      ≤ ENNReal.ofReal (γ * η / (1 - γ * ε)) * ∫⁻ ω, Φ (f ω) ∂P := by
    intro N
    have hgN : Measurable fun ω => min (g ω) (N : ℝ≥0∞) := hg.min measurable_const
    have hfin : ∫⁻ ω, Φ (min (g ω) N) ∂P ≠ ⊤ := by
      refine ne_top_of_le_ne_top (isPhi_ne_top hΦ (ENNReal.natCast_ne_top N)) ?_
      calc ∫⁻ ω, Φ (min (g ω) N) ∂P ≤ ∫⁻ _, Φ N ∂P :=
            lintegral_mono fun ω => hΦ.mono (min_le_right _ _)
        _ = Φ N := by simp
    refine key_arith _ _ γ η ε hε hγε hfin ?_
    calc ∫⁻ ω, Φ (min (g ω) N) ∂P
        ≤ ∫⁻ ω, γ * Φ (ENNReal.ofReal β⁻¹ * min (g ω) N) ∂P := by
          refine lintegral_mono fun ω => ?_
          have := scale_le hΦ hβ0 (fun l hl => (h72 l hl).1) (ENNReal.ofReal β⁻¹ * min (g ω) N)
          rwa [← mul_assoc, ← ENNReal.ofReal_mul hβ0.le, mul_inv_cancel₀ hβ0.ne',
            ENNReal.ofReal_one, one_mul] at this
      _ = γ * ∫⁻ ω, Φ (ENNReal.ofReal β⁻¹ * min (g ω) N) ∂P :=
          lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ ≤ γ * (ENNReal.ofReal ε * ∫⁻ ω, Φ (min (g ω) N) ∂P
            + ∫⁻ ω, Φ (ENNReal.ofReal δ⁻¹ * f ω) ∂P) := by
          gcongr
          exact good_lambda_trunc P Φ c hΦ f g hf hg β δ ε hβ hδ hε h71 N
      _ ≤ γ * (ENNReal.ofReal ε * ∫⁻ ω, Φ (min (g ω) N) ∂P + η * ∫⁻ ω, Φ (f ω) ∂P) := by
          gcongr
          rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
          exact lintegral_mono fun ω =>
            scale_le hΦ (inv_pos.2 hδ) (fun l hl => (h72 l hl).2) (f ω)
  -- pass to the limit `N → ∞`
  have hlim : Tendsto (fun N : ℕ => ∫⁻ ω, Φ (min (g ω) N) ∂P) atTop (𝓝 (∫⁻ ω, Φ (g ω) ∂P)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun N => (hΦm.comp (hg.min measurable_const)).aemeasurable)
      (Eventually.of_forall fun ω N M hNM => hΦ.mono (min_le_min_left _ (by exact_mod_cast hNM)))
      (Eventually.of_forall fun ω => ?_)
    have : Tendsto (fun N : ℕ => min (g ω) (N : ℝ≥0∞)) atTop (𝓝 (min (g ω) ⊤)) :=
      tendsto_const_nhds.min ENNReal.tendsto_nat_nhds_top
    rw [min_eq_left le_top] at this
    exact (hΦ.cont.tendsto _).comp this
  exact le_of_tendsto' hlim hN

end BurkholderDFI.Brownian

open BurkholderDFI.Brownian


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c)
    (f g : Ω → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (β δ ε : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hε : 0 < ε)
    (h71 : ∀ l : ℝ, 0 < l →
      P {ω | ENNReal.ofReal (β * l) < g ω ∧ f ω ≤ ENNReal.ofReal (δ * l)}
        ≤ ENNReal.ofReal ε * P {ω | ENNReal.ofReal l < g ω})
    (γ η : ℝ≥0)
    (h72 : ∀ l : ℝ, 0 < l →
      Φ (ENNReal.ofReal (β * l)) ≤ γ * Φ (ENNReal.ofReal l) ∧
      Φ (ENNReal.ofReal (δ⁻¹ * l)) ≤ η * Φ (ENNReal.ofReal l))
    (hγε : (γ : ℝ) * ε < 1) :
    ∫⁻ ω, Φ (g ω) ∂P ≤ ENNReal.ofReal (γ * η / (1 - γ * ε)) * ∫⁻ ω, Φ (f ω) ∂P := by
  exact lemma_7_1_core P Φ c hΦ f g hf hg β δ ε hβ hδ hε h71 γ η h72 hγε
