-- Prove2me | solution 1 for BurkholderDFI.CondSquare.theorem_21_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:11:29.815297+00:00
-- url     : https://prove2.me/submissions/42785982-3640-42f5-b402-cdeee1d0ce4d

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal


namespace BurkholderDFI.CondSquare

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


variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {ℱ : Filtration ℕ mΩ}
  {g : ℕ → Ω → ℝ} {f : ℕ → Ω → ℝ}

/-- `((x ^ (1/p)) ^ p = x`. -/
lemma rpow_one_div_rpow (x : ℝ≥0∞) {p : ℝ} (hp : p ≠ 0) : (x ^ (1 / p)) ^ p = x := by
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp, ENNReal.rpow_one]

/-- Hölder step: from `l * m ≤ a` and `a ≤ b^(1/p) m^(1/q)` deduce `l^p m ≤ b`. -/
lemma holder_step {p q : ℝ} (hpq : p.HolderConjugate q) {l : ℝ} (hl : 0 < l)
    {a b m : ℝ≥0∞} (hm : m ≠ ⊤) (h1 : ENNReal.ofReal l * m ≤ a)
    (h2 : a ≤ b ^ (1 / p) * m ^ (1 / q)) :
    ENNReal.ofReal (l ^ p) * m ≤ b := by
  rcases eq_or_ne m 0 with hm0 | hm0
  · simp [hm0]
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have hpq' : 1 / q * p = p - 1 := by
    have h := hpq.inv_add_inv_eq_one
    field_simp
    field_simp at h
    linarith
  have h3 : (ENNReal.ofReal l * m) ^ p ≤ (b ^ (1 / p) * m ^ (1 / q)) ^ p :=
    ENNReal.rpow_le_rpow (h1.trans h2) hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
    rpow_one_div_rpow _ hp0.ne', ← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_nonneg hl.le hp0.le,
    hpq'] at h3
  have hsplit : m ^ p = m * m ^ (p - 1) := by
    conv_lhs => rw [show p = 1 + (p - 1) by ring]
    rw [ENNReal.rpow_add _ _ hm0 hm, ENNReal.rpow_one]
  rw [hsplit, ← mul_assoc] at h3
  have hp1 : 0 ≤ p - 1 := by linarith [hpq.lt]
  refine (ENNReal.mul_le_mul_iff_left ?_ (ENNReal.rpow_ne_top_of_nonneg hp1 hm)).1 h3
  intro h0
  rw [ENNReal.rpow_eq_zero_iff] at h0
  rcases h0 with ⟨h, _⟩ | ⟨h, _⟩
  · exact hm0 h
  · exact hm h

/-- Doob's inequality in `L^p` form at a fixed time, for a nonnegative submartingale. -/
lemma doob_fixed [IsProbabilityMeasure P] (hg : Submartingale g ℱ P) (hnn : 0 ≤ g)
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) (n : ℕ) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < maxFnN g n ω}
      ≤ ∫⁻ ω, ENNReal.ofReal (g n ω) ^ p ∂P := by
  set ε : ℝ≥0 := Real.toNNReal l with hε
  have hεl : (ε : ℝ) = l := Real.coe_toNNReal _ hl.le
  have hεl' : (ε : ℝ≥0∞) = ENNReal.ofReal l := rfl
  set A := {ω | (ε : ℝ) ≤
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => g k ω} with hA
  have hsub : {ω | ENNReal.ofReal l < maxFnN g n ω} ⊆ A := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, maxFnN, lt_iSup_iff] at hω
    obtain ⟨k, hk, hlt⟩ := hω
    have hk' : k ∈ Finset.range (n + 1) := by
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_range]; omega
    have hnn' : 0 ≤ g k ω := hnn k ω
    have hlt' : l < g k ω := by
      have := (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1
      rwa [abs_of_nonneg hnn'] at this
    simp only [hA, Set.mem_ofPred_eq, hεl]
    exact hlt'.le.trans (Finset.le_sup' (fun k => g k ω) hk')
  have hmax := maximal_ineq hg hnn (ε := ε) n
  rw [← hA, ofReal_integral_eq_lintegral_ofReal (hg.integrable n).integrableOn
    (Eventually.of_forall fun ω => hnn n ω), hεl'] at hmax
  have hb : ∫⁻ ω in A, ENNReal.ofReal (g n ω) ^ p ∂P ≤ ∫⁻ ω, ENNReal.ofReal (g n ω) ^ p ∂P :=
    setLIntegral_le_lintegral _ _
  refine le_trans ?_ hb
  have hmono : P {ω | ENNReal.ofReal l < maxFnN g n ω} ≤ P A := measure_mono hsub
  refine le_trans (mul_le_mul' le_rfl hmono) ?_
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · subst hp1
    simpa using hmax
  · have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp1
    have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (g n ω)) (P.restrict A) :=
      ((hg.stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl).ennreal_ofReal.aemeasurable
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (P.restrict A) hpq hmeas
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul,
      Measure.restrict_apply_univ] at hH
    exact holder_step hpq hl (measure_ne_top P A) hmax hH

/-- The maximal set is the increasing union of the finite-time maximal sets. -/
lemma measure_maxFn_eq_iSup (P : Measure Ω) (g : ℕ → Ω → ℝ) (l : ℝ) :
    P {ω | ENNReal.ofReal l < maxFn g ω} = ⨆ n, P {ω | ENNReal.ofReal l < maxFnN g n ω} := by
  have hU : {ω | ENNReal.ofReal l < maxFn g ω} = ⋃ n, {ω | ENNReal.ofReal l < maxFnN g n ω} := by
    ext ω; simp [maxFn, lt_iSup_iff]
  rw [hU]
  refine Monotone.measure_iUnion fun n m hnm ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine lt_of_lt_of_le hω ?_
  simp only [maxFnN]
  exact biSup_mono fun k hk => by
    simp only [Finset.mem_Icc] at hk ⊢; omega

/-- (1.5) for a nonnegative submartingale `g` (nonnegative everywhere). -/
lemma eq_1_5_nonneg [IsProbabilityMeasure P] (hg : Submartingale g ℱ P) (hnn : 0 ≤ g)
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < maxFn g ω} ≤ pNorm P p g ^ p := by
  rw [measure_maxFn_eq_iSup, ENNReal.mul_iSup]
  refine iSup_le fun n => ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : {ω | ENNReal.ofReal l < maxFnN g 0 ω} = ∅ := by
      ext ω; simp [maxFnN]
    rw [this, measure_empty, mul_zero]; exact zero_le
  refine (doob_fixed hg hnn p hp l hl n).trans ?_
  have hp0 : 0 ≤ p := by linarith
  have h1 : ∫⁻ ω, ENNReal.ofReal (g n ω) ^ p ∂P
      = lpNormE P p (fun ω => ENNReal.ofReal |g n ω|) ^ p := by
    simp only [lpNormE]
    rw [rpow_one_div_rpow _ (by linarith)]
    congr 1
    funext ω
    rw [abs_of_nonneg (hnn n ω)]
  rw [h1]
  refine ENNReal.rpow_le_rpow ?_ hp0
  exact le_iSup₂ (f := fun n (_ : n ∈ Set.Ici (1 : ℕ)) =>
    lpNormE P p (fun ω => ENNReal.ofReal |g n ω|)) n hn

/-- (1.5). -/
theorem eq_1_5_core [IsProbabilityMeasure P] {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < maxFn f ω} ≤ pNorm P p f ^ p := by
  rcases hf with hf | ⟨hf, hnn⟩
  · -- martingale case: `|f|` is a nonnegative submartingale
    have hsub : Submartingale (f⁺ + (-f)⁺) ℱ P :=
      hf.submartingale.pos.add hf.neg.submartingale.pos
    have heq : (f⁺ + (-f)⁺) = fun n ω => |f n ω| := by
      funext n ω
      simp only [Pi.add_apply, Pi.posPart_apply, Pi.neg_apply]
      rw [posPart_neg, posPart_add_negPart]
    rw [heq] at hsub
    have hnn : (0 : ℕ → Ω → ℝ) ≤ fun n ω => |f n ω| := fun n ω => abs_nonneg _
    have h := eq_1_5_nonneg hsub hnn p hp l hl
    have e1 : maxFn (fun n ω => |f n ω|) = maxFn f := by
      funext ω; simp [maxFn, maxFnN, abs_abs]
    have e2 : pNorm P p (fun n ω => |f n ω|) = pNorm P p f := by
      simp [pNorm, abs_abs]
    rwa [e1, e2] at h
  · -- nonnegative submartingale case: `f⁺` is a nonnegative submartingale a.e. equal to `f`
    have hsub : Submartingale (f⁺) ℱ P := hf.pos
    have hnn' : (0 : ℕ → Ω → ℝ) ≤ f⁺ := fun n ω => by
      simp only [Pi.posPart_apply, Pi.zero_apply]
      exact posPart_nonneg _
    have h := eq_1_5_nonneg hsub hnn' p hp l hl
    have hae : ∀ᵐ ω ∂P, ∀ n, 1 ≤ n → |(f⁺) n ω| = |f n ω| := by
      rw [ae_all_iff]
      intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · filter_upwards [hnn n hn] with ω hω
        intro _
        simp only [Pi.posPart_apply]
        rw [posPart_eq_self.2 hω]
    have e1 : P {ω | ENNReal.ofReal l < maxFn (f⁺) ω} = P {ω | ENNReal.ofReal l < maxFn f ω} := by
      refine measure_congr ?_
      filter_upwards [hae] with ω hω
      have : maxFn (f⁺) ω = maxFn f ω := by
        simp only [maxFn, maxFnN]
        refine iSup_congr fun n => iSup_congr fun k => iSup_congr fun hk => ?_
        simp only [Finset.mem_Icc] at hk
        rw [hω k hk.1]
      change (ENNReal.ofReal l < maxFn (f⁺) ω) = (ENNReal.ofReal l < maxFn f ω)
      rw [this]
    have e2 : pNorm P p (f⁺) = pNorm P p f := by
      simp only [pNorm]
      refine iSup_congr fun n => iSup_congr fun hn => ?_
      simp only [lpNormE]
      congr 1
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with ω hω
      rw [hω n hn]
    rwa [e1, e2] at h


/-! ### Measurability of the maximal function -/

lemma measurable_maxFnN_filt (hf : Martingale f ℱ P) (k : ℕ) : Measurable[ℱ k] (maxFnN f k) := by
  unfold maxFnN
  refine Measurable.iSup fun n => Measurable.iSup fun hn => ?_
  have hnk : n ≤ k := (Finset.mem_Icc.1 hn).2
  exact (continuous_abs.measurable.comp
    ((hf.stronglyMeasurable n).measurable.mono (ℱ.mono hnk) le_rfl)).ennreal_ofReal

lemma measurable_maxFnN (hf : Martingale f ℱ P) (k : ℕ) : Measurable (maxFnN f k) :=
  (measurable_maxFnN_filt hf k).mono (ℱ.le k) le_rfl

lemma measurable_maxFn (hf : Martingale f ℱ P) : Measurable (maxFn f) :=
  Measurable.iSup fun k => measurable_maxFnN hf k

/-! ### The conditional square function summands -/

/-- `Z_{j+1} = E(d_{j+1}^2 | 𝒜_j)`. -/
noncomputable def Zc (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (j : ℕ) : Ω → ℝ≥0∞ :=
  condLExp (ℱ j) P (fun x => ENNReal.ofReal (dseq f (j + 1) x ^ 2))

lemma measurable_Zc_filt (j : ℕ) : Measurable[ℱ j] (Zc ℱ P f j) :=
  measurable_condLExp _ _ _

lemma measurable_Zc (j : ℕ) : Measurable (Zc ℱ P f j) :=
  measurable_condLExp' _ _ _

lemma condSqFn_eq (ω : Ω) : condSqFn ℱ P f ω = (∑' k, Zc ℱ P f k ω) ^ (1 / 2 : ℝ) := rfl

/-! ### The stopping sets and the transform -/

/-- `{μ ≤ k}`: the maximal function up to time `k` exceeds `l`. -/
def Mset (f : ℕ → Ω → ℝ) (l : ℝ) (k : ℕ) : Set Ω := {ω | ENNReal.ofReal l < maxFnN f k ω}

/-- `{s_{k+1} ≤ δλ}` in squared form: the first `k+1` conditional summands sum to at most `c`. -/
def Sset (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (c : ℝ≥0∞) (k : ℕ) : Set Ω :=
  {ω | ∑ j ∈ Finset.range (k + 1), Zc ℱ P f j ω ≤ c}

def Aset (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (l : ℝ) (c : ℝ≥0∞) (k : ℕ) :
    Set Ω := Mset f l k ∩ Sset ℱ P f c k

lemma measurableSet_Mset (hf : Martingale f ℱ P) (l : ℝ) (k : ℕ) :
    MeasurableSet[ℱ k] (Mset f l k) :=
  measurableSet_lt measurable_const (measurable_maxFnN_filt hf k)

lemma measurableSet_Sset (c : ℝ≥0∞) (k : ℕ) : MeasurableSet[ℱ k] (Sset ℱ P f c k) := by
  refine measurableSet_le ?_ measurable_const
  refine Finset.measurable_sum _ fun j hj => ?_
  have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using hj
  exact (measurable_Zc_filt j).mono (ℱ.mono hjk) le_rfl

lemma measurableSet_Aset (hf : Martingale f ℱ P) (l : ℝ) (c : ℝ≥0∞) (k : ℕ) :
    MeasurableSet[ℱ k] (Aset ℱ P f l c k) :=
  (measurableSet_Mset hf l k).inter (measurableSet_Sset c k)

lemma Mset_zero (f : ℕ → Ω → ℝ) (l : ℝ) : Mset f l 0 = ∅ := by
  ext ω; simp [Mset, maxFnN]

/-- The difference `D_k = f_{k+1} - f_k`. -/
def Dk (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ := f (k + 1) ω - f k ω

lemma Dk_eq_dseq (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : Dk f (k + 1) ω = dseq f (k + 2) ω := by
  simp [Dk, dseq]

/-- The transform increments `h_k = 1_{A_k} D_k`. -/
noncomputable def hk (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (l : ℝ) (c : ℝ≥0∞)
    (k : ℕ) : Ω → ℝ := (Aset ℱ P f l c k).indicator (Dk f k)

/-- The transform `g_n = Σ_{k<n} h_k`. -/
noncomputable def gtr (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (l : ℝ) (c : ℝ≥0∞)
    (n : ℕ) (ω : Ω) : ℝ := ∑ k ∈ Finset.range n, hk ℱ P f l c k ω

/-- The indicator weights. -/
noncomputable def xi (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (l : ℝ) (c : ℝ≥0∞)
    (k : ℕ) : Ω → ℝ := (Aset ℱ P f l c k).indicator (fun _ => (1 : ℝ))

lemma gtr_eq (l : ℝ) (c : ℝ≥0∞) :
    gtr ℱ P f l c = fun n => ∑ k ∈ Finset.range n, xi ℱ P f l c k * (f (k + 1) - f k) := by
  funext n ω
  simp only [gtr, hk, xi, Finset.sum_apply, Pi.mul_apply, Pi.sub_apply, Set.indicator, Dk]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

lemma gtr_martingale [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (l : ℝ) (c : ℝ≥0∞) :
    Martingale (gtr ℱ P f l c) ℱ P := by
  have hξ : StronglyAdapted ℱ (xi ℱ P f l c) := fun k =>
    stronglyMeasurable_const.indicator (measurableSet_Aset hf l c k)
  have hbdd : ∀ n ω, xi ℱ P f l c n ω ≤ 1 := fun n ω => by
    simp only [xi, Set.indicator]; split_ifs <;> norm_num
  have hnn : ∀ n ω, 0 ≤ xi ℱ P f l c n ω := fun n ω => by
    simp only [xi, Set.indicator]; split_ifs <;> norm_num
  have h1 := hf.submartingale.sum_mul_sub hξ hbdd hnn
  have h2 := hf.neg.submartingale.sum_mul_sub hξ hbdd hnn
  rw [gtr_eq, martingale_iff]
  refine ⟨?_, h1⟩
  have := h2.neg
  convert this using 1
  funext n ω
  simp only [Pi.neg_apply, Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### Integrability and the conditional second moments -/

lemma integrable_hk [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (l : ℝ) (c : ℝ≥0∞) (k : ℕ) :
    Integrable (hk ℱ P f l c k) P :=
  ((hf.integrable (k + 1)).sub (hf.integrable k)).indicator (ℱ.le k _ (measurableSet_Aset hf l c k))

lemma hk_sq (l : ℝ) (c : ℝ≥0∞) (k : ℕ) (ω : Ω) :
    ENNReal.ofReal (hk ℱ P f l c k ω ^ 2)
      = (Aset ℱ P f l c k).indicator (fun ω => ENNReal.ofReal (Dk f k ω ^ 2)) ω := by
  simp only [hk, Set.indicator]
  split_ifs <;> simp

/-- The key identity: `E[h_k^2] = ∫_{A_k} Z_{k+1}`. -/
lemma lintegral_hk_sq [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (l : ℝ) (c : ℝ≥0∞) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (hk ℱ P f l c k ω ^ 2) ∂P
      = ∫⁻ ω, (Aset ℱ P f l c k).indicator (Zc ℱ P f k) ω ∂P := by
  simp_rw [hk_sq]
  rw [lintegral_indicator (ℱ.le k _ (measurableSet_Aset hf l c k)),
    lintegral_indicator (ℱ.le k _ (measurableSet_Aset hf l c k))]
  rcases k with _ | k
  · have : Aset ℱ P f l c 0 = ∅ := by
      simp [Aset, Mset_zero]
    simp [this]
  · simp_rw [Dk_eq_dseq]
    rw [Zc, setLIntegral_condLExp (ℱ.le (k + 1)) P _ (measurableSet_Aset hf l c (k + 1))]

/-- On `A_k`, `Z_{k+1} ≤ c`. -/
lemma indicator_Zc_le (l : ℝ) (c : ℝ≥0∞) (k : ℕ) (ω : Ω) :
    (Aset ℱ P f l c k).indicator (Zc ℱ P f k) ω ≤ c := by
  simp only [Set.indicator]
  split_ifs with h
  · refine le_trans ?_ h.2
    exact Finset.single_le_sum (f := fun j => Zc ℱ P f j ω) (fun _ _ => zero_le)
      (Finset.self_mem_range_succ k)
  · exact zero_le

lemma integrable_hk_sq [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (l : ℝ) {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (k : ℕ) : Integrable (fun ω => hk ℱ P f l c k ω ^ 2) P := by
  refine ⟨((integrable_hk hf l c k).aestronglyMeasurable.mul
    (integrable_hk hf l c k).aestronglyMeasurable).congr (Eventually.of_forall fun ω => by
      simp [sq]), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _),
    lintegral_hk_sq hf l c k]
  calc ∫⁻ ω, (Aset ℱ P f l c k).indicator (Zc ℱ P f k) ω ∂P ≤ ∫⁻ _, c ∂P :=
        lintegral_mono fun ω => indicator_Zc_le l c k ω
    _ = c := by simp
    _ < ⊤ := hc.lt_top

lemma integrable_mul_of_sq {a b : Ω → ℝ} (ha : AEStronglyMeasurable a P)
    (hb : AEStronglyMeasurable b P) (ha2 : Integrable (fun ω => a ω ^ 2) P)
    (hb2 : Integrable (fun ω => b ω ^ 2) P) : Integrable (fun ω => a ω * b ω) P := by
  refine Integrable.mono' ((ha2.add hb2).div_const 2) (ha.mul hb)
    (Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|a ω| - |b ω|), sq_abs (a ω), sq_abs (b ω), abs_nonneg (a ω),
    abs_nonneg (b ω)]

lemma stronglyMeasurable_hk_filt (hf : Martingale f ℱ P) (l : ℝ) (c : ℝ≥0∞) (k : ℕ) :
    StronglyMeasurable[ℱ (k + 1)] (hk ℱ P f l c k) := by
  refine StronglyMeasurable.indicator ?_ ((ℱ.mono (Nat.le_succ k)) _ (measurableSet_Aset hf l c k))
  exact (hf.stronglyMeasurable (k + 1)).sub
    ((hf.stronglyMeasurable k).mono (ℱ.mono (Nat.le_succ k)))

lemma condExp_Dk [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (k : ℕ) :
    P[Dk f k | ℱ k] =ᵐ[P] 0 := by
  have h1 : P[Dk f k | ℱ k] =ᵐ[P] P[f (k + 1) | ℱ k] - P[f k | ℱ k] :=
    condExp_sub (hf.integrable (k + 1)) (hf.integrable k) _
  have h2 : P[f (k + 1) | ℱ k] =ᵐ[P] f k := hf.condExp_ae_eq (Nat.le_succ k)
  have h3 : P[f k | ℱ k] = f k :=
    condExp_of_stronglyMeasurable (ℱ.le k) (hf.stronglyMeasurable k) (hf.integrable k)
  filter_upwards [h1, h2] with ω hω1 hω2
  rw [hω1, Pi.sub_apply, hω2, h3, Pi.zero_apply, sub_self]

/-- Orthogonality of the increments. -/
lemma integral_hk_mul [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (l : ℝ) {c : ℝ≥0∞}
    (hc : c ≠ ⊤) {j k : ℕ} (hjk : j < k) :
    ∫ ω, hk ℱ P f l c j ω * hk ℱ P f l c k ω ∂P = 0 := by
  set Y : Ω → ℝ := fun ω => hk ℱ P f l c j ω * (Aset ℱ P f l c k).indicator (fun _ => (1 : ℝ)) ω
    with hY
  have hYm : StronglyMeasurable[ℱ k] Y :=
    ((stronglyMeasurable_hk_filt hf l c j).mono (ℱ.mono hjk)).mul
      (stronglyMeasurable_const.indicator (measurableSet_Aset hf l c k))
  have heq : (fun ω => hk ℱ P f l c j ω * hk ℱ P f l c k ω) = Y * Dk f k := by
    funext ω
    simp only [hY, Pi.mul_apply, hk, Set.indicator]
    split_ifs <;> simp
  have hint : Integrable (Y * Dk f k) P := by
    rw [← heq]
    exact integrable_mul_of_sq (integrable_hk hf l c j).aestronglyMeasurable
      (integrable_hk hf l c k).aestronglyMeasurable (integrable_hk_sq hf l hc j)
      (integrable_hk_sq hf l hc k)
  have hD : Integrable (Dk f k) P := (hf.integrable (k + 1)).sub (hf.integrable k)
  rw [heq, ← integral_condExp (ℱ.le k)]
  have h1 := condExp_mul_of_stronglyMeasurable_left hYm hint hD
  have h2 := condExp_Dk hf k
  have h3 : P[Y * Dk f k | ℱ k] =ᵐ[P] 0 := by
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [hω1, Pi.mul_apply, hω2, Pi.zero_apply, mul_zero]
  rw [integral_congr_ae h3]
  simp

/-- `E[g_n^2] = Σ_{k<n} E[h_k^2]`. -/
lemma integral_gtr_sq [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (l : ℝ) {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (n : ℕ) :
    ∫ ω, gtr ℱ P f l c n ω ^ 2 ∂P = ∑ k ∈ Finset.range n, ∫ ω, hk ℱ P f l c k ω ^ 2 ∂P := by
  have hprod : ∀ j k, Integrable (fun ω => hk ℱ P f l c j ω * hk ℱ P f l c k ω) P := fun j k =>
    integrable_mul_of_sq (integrable_hk hf l c j).aestronglyMeasurable
      (integrable_hk hf l c k).aestronglyMeasurable (integrable_hk_sq hf l hc j)
      (integrable_hk_sq hf l hc k)
  have hexp : ∀ ω, gtr ℱ P f l c n ω ^ 2
      = ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, hk ℱ P f l c j ω * hk ℱ P f l c k ω := by
    intro ω
    simp only [gtr, sq, Finset.sum_mul_sum]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hprod j k]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_finsetSum _ fun k _ => hprod j k]
  have : ∀ k ∈ Finset.range n, ∫ ω, hk ℱ P f l c j ω * hk ℱ P f l c k ω ∂P
      = if j = k then ∫ ω, hk ℱ P f l c j ω ^ 2 ∂P else 0 := by
    intro k _
    rcases lt_trichotomy j k with h | h | h
    · rw [if_neg h.ne, integral_hk_mul hf l hc h]
    · subst h; simp [sq]
    · rw [if_neg h.ne', ← integral_hk_mul hf l hc h]
      congr 1; funext ω; ring
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos hj]

lemma integrable_gtr_sq [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (l : ℝ) {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (n : ℕ) : Integrable (fun ω => gtr ℱ P f l c n ω ^ 2) P := by
  have hprod : ∀ j k, Integrable (fun ω => hk ℱ P f l c j ω * hk ℱ P f l c k ω) P := fun j k =>
    integrable_mul_of_sq (integrable_hk hf l c j).aestronglyMeasurable
      (integrable_hk hf l c k).aestronglyMeasurable (integrable_hk_sq hf l hc j)
      (integrable_hk_sq hf l hc k)
  have hexp : (fun ω => gtr ℱ P f l c n ω ^ 2)
      = fun ω => ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
          hk ℱ P f l c j ω * hk ℱ P f l c k ω := by
    funext ω
    simp only [gtr, sq, Finset.sum_mul_sum]
  rw [hexp]
  exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hprod j k

/-- Pointwise bound on the stopped conditional sum. -/
lemma sum_indicator_Zc_le (l : ℝ) (c : ℝ≥0∞) (n : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.range n, (Aset ℱ P f l c k).indicator (Zc ℱ P f k) ω
      ≤ {ω | ENNReal.ofReal l < maxFn f ω}.indicator (fun _ => c) ω := by
  classical
  set K := (Finset.range n).filter (fun k => ω ∈ Aset ℱ P f l c k) with hK
  have hsum : ∑ k ∈ Finset.range n, (Aset ℱ P f l c k).indicator (Zc ℱ P f k) ω
      = ∑ k ∈ K, Zc ℱ P f k ω := by
    rw [hK, Finset.sum_filter]
    rfl
  rw [hsum]
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe, Finset.sum_empty]; exact zero_le
  set m := K.max' hKne with hm
  have hmK : m ∈ K := Finset.max'_mem K hKne
  have hmA : ω ∈ Aset ℱ P f l c m := (Finset.mem_filter.1 hmK).2
  have hsub : K ⊆ Finset.range (m + 1) := fun k hk => by
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_max' K k hk
  calc ∑ k ∈ K, Zc ℱ P f k ω ≤ ∑ k ∈ Finset.range (m + 1), Zc ℱ P f k ω :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => zero_le
    _ ≤ c := hmA.2
    _ = {ω | ENNReal.ofReal l < maxFn f ω}.indicator (fun _ => c) ω := by
        rw [Set.indicator_of_mem]
        show ENNReal.ofReal l < maxFn f ω
        exact lt_of_lt_of_le hmA.1 (le_iSup (fun n => maxFnN f n ω) m)

/-- The `L²` bound on the transform: `E g_n^2 ≤ c P(f^* > λ)`. -/
lemma lintegral_gtr_sq_le [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (l : ℝ) {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (gtr ℱ P f l c n ω ^ 2) ∂P
      ≤ c * P {ω | ENNReal.ofReal l < maxFn f ω} := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gtr_sq hf l hc n)
    (Eventually.of_forall fun ω => sq_nonneg _), integral_gtr_sq hf l hc n,
    ENNReal.ofReal_sum_of_nonneg fun k _ => integral_nonneg fun ω => sq_nonneg _]
  have h1 : ∀ k, ENNReal.ofReal (∫ ω, hk ℱ P f l c k ω ^ 2 ∂P)
      = ∫⁻ ω, (Aset ℱ P f l c k).indicator (Zc ℱ P f k) ω ∂P := fun k => by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_hk_sq hf l hc k)
      (Eventually.of_forall fun ω => sq_nonneg _), lintegral_hk_sq hf l c k]
  simp_rw [h1]
  rw [← lintegral_finsetSum _ fun k _ =>
    (measurable_Zc k).indicator (ℱ.le k _ (measurableSet_Aset hf l c k))]
  calc ∫⁻ ω, ∑ k ∈ Finset.range n, (Aset ℱ P f l c k).indicator (Zc ℱ P f k) ω ∂P
      ≤ ∫⁻ ω, {ω | ENNReal.ofReal l < maxFn f ω}.indicator (fun _ => c) ω ∂P :=
        lintegral_mono fun ω => sum_indicator_Zc_le l c n ω
    _ = c * P {ω | ENNReal.ofReal l < maxFn f ω} :=
        lintegral_indicator_const (measurableSet_lt measurable_const (measurable_maxFn hf)) c


/-! ### The event inclusion -/

lemma event_subset (f : ℕ → Ω → ℝ) (β δ l : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hδβ : δ < β - 1)
    (hl : 0 < l) :
    {ω | ENNReal.ofReal (β * l) < maxFn f ω ∧
        max (condSqFn ℱ P f ω) (maxFn (dseq f) ω) ≤ ENNReal.ofReal (δ * l)}
      ⊆ {ω | ENNReal.ofReal ((β - δ - 1) * l)
          < maxFn (gtr ℱ P f l (ENNReal.ofReal (δ * l) ^ 2)) ω} := by
  classical
  intro ω hω
  obtain ⟨h1, h2⟩ := hω
  set c := ENNReal.ofReal (δ * l) ^ 2 with hc
  have hs : ∀ k, ω ∈ Sset ℱ P f c k := by
    intro k
    have hcs : condSqFn ℱ P f ω ≤ ENNReal.ofReal (δ * l) := le_trans (le_max_left _ _) h2
    rw [condSqFn_eq] at hcs
    have : ∑' k, Zc ℱ P f k ω ≤ c := by
      have := ENNReal.rpow_le_rpow hcs (by norm_num : (0 : ℝ) ≤ 2)
      rwa [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
        ENNReal.rpow_two] at this
    exact le_trans (ENNReal.sum_le_tsum _) this
  have hd : ∀ k, 1 ≤ k → |dseq f k ω| ≤ δ * l := by
    intro k hk
    have hdm : maxFn (dseq f) ω ≤ ENNReal.ofReal (δ * l) := le_trans (le_max_right _ _) h2
    have : ENNReal.ofReal |dseq f k ω| ≤ maxFn (dseq f) ω := by
      refine le_trans ?_ (le_iSup (fun n => maxFnN (dseq f) n ω) k)
      exact le_iSup₂ (f := fun n (_ : n ∈ Finset.Icc 1 k) => ENNReal.ofReal |dseq f n ω|) k
        (Finset.mem_Icc.2 ⟨hk, le_rfl⟩)
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (this.trans hdm)
  obtain ⟨N, hN1, hN⟩ : ∃ N, 1 ≤ N ∧ β * l < |f N ω| := by
    simp only [maxFn, maxFnN, lt_iSup_iff] at h1
    obtain ⟨n, k, hk, hlt⟩ := h1
    exact ⟨k, (Finset.mem_Icc.1 hk).1, (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1⟩
  have hlN : l < |f N ω| := by nlinarith
  have hex : ∃ n, 1 ≤ n ∧ l < |f n ω| := ⟨N, hN1, hlN⟩
  obtain ⟨m, hm1, hmin⟩ : ∃ m, (1 ≤ m ∧ l < |f m ω|) ∧ ∀ n, n < m → ¬ (1 ≤ n ∧ l < |f n ω|) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun n hn => Nat.find_min hex hn⟩
  have hmN : m ≤ N := by
    by_contra h
    exact hmin N (not_le.1 h) ⟨hN1, hlN⟩
  have hM : ∀ k, ω ∈ Mset f l k ↔ m ≤ k := by
    intro k
    constructor
    · intro hk
      simp only [Mset, Set.mem_setOf_eq, maxFnN, lt_iSup_iff] at hk
      obtain ⟨n, hn, hlt⟩ := hk
      by_contra hcon
      push Not at hcon
      have hn1 := Finset.mem_Icc.1 hn
      exact hmin n (by omega) ⟨hn1.1, (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1⟩
    · intro hk
      show ENNReal.ofReal l < maxFnN f k ω
      refine lt_of_lt_of_le ?_ (le_iSup₂ (f := fun n (_ : n ∈ Finset.Icc 1 k) =>
        ENNReal.ofReal |f n ω|) m (Finset.mem_Icc.2 ⟨hm1.1, hk⟩))
      exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hm1.2, by linarith [hm1.2]⟩
  have hA : ∀ k, ω ∈ Aset ℱ P f l c k ↔ m ≤ k := fun k => by
    simp only [Aset, Set.mem_inter_iff, hM, hs, and_true]
  have hg : gtr ℱ P f l c N ω = f N ω - f m ω := by
    simp only [gtr, hk, Set.indicator]
    have : ∀ k, (if ω ∈ Aset ℱ P f l c k then Dk f k ω else 0)
        = if m ≤ k then Dk f k ω else 0 := fun k => by simp only [hA]
    simp_rw [this]
    rw [← Finset.sum_filter]
    have hfil : (Finset.range N).filter (fun k => m ≤ k) = Finset.Ico m N := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [hfil, Finset.sum_Ico_eq_sub _ hmN]
    simp only [Dk]
    rw [Finset.sum_range_sub (fun k => f k ω), Finset.sum_range_sub (fun k => f k ω)]
    ring
  have hfm : |f m ω| ≤ (1 + δ) * l := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rcases Nat.eq_zero_or_pos m' with hm' | hm'
    · subst hm'
      have := hd 1 le_rfl
      simp only [dseq, one_ne_zero, if_false, if_true] at this
      nlinarith
    · have h1 := hd (m' + 1) (by omega)
      have h2 : |f m' ω| ≤ l := by
        by_contra hcon
        exact hmin m' (Nat.lt_succ_self m') ⟨hm', not_le.1 hcon⟩
      have hd' : dseq f (m' + 1) ω = f (m' + 1) ω - f m' ω := by
        simp only [dseq, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        rw [if_neg (by omega)]
      rw [hd'] at h1
      calc |f (m' + 1) ω| = |f m' ω + (f (m' + 1) ω - f m' ω)| := by ring_nf
        _ ≤ |f m' ω| + |f (m' + 1) ω - f m' ω| := abs_add_le _ _
        _ ≤ l + δ * l := add_le_add h2 h1
        _ = (1 + δ) * l := by ring
  have hgN : (β - δ - 1) * l < |gtr ℱ P f l c N ω| := by
    rw [hg]
    have := abs_sub_abs_le_abs_sub (f N ω) (f m ω)
    nlinarith
  show ENNReal.ofReal ((β - δ - 1) * l) < maxFn (gtr ℱ P f l c) ω
  refine lt_of_lt_of_le (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hgN, ?_⟩) ?_
  · have : 0 < β - δ - 1 := by linarith
    exact lt_trans (mul_pos this hl) hgN
  · refine le_trans ?_ (le_iSup (fun n => maxFnN (gtr ℱ P f l c) n ω) N)
    exact le_iSup₂ (f := fun n (_ : n ∈ Finset.Icc 1 N) => ENNReal.ofReal |gtr ℱ P f l c n ω|) N
      (Finset.mem_Icc.2 ⟨hN1, le_rfl⟩)

/-! ### (21.2) -/

theorem eq_21_2_core [IsProbabilityMeasure P] (hf : Martingale f ℱ P)
    (β δ : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hδβ : δ < β - 1) (l : ℝ) (hl : 0 < l) :
    P {ω | ENNReal.ofReal (β * l) < maxFn f ω ∧
          max (condSqFn ℱ P f ω) (maxFn (dseq f) ω) ≤ ENNReal.ofReal (δ * l)}
      ≤ ENNReal.ofReal (δ ^ 2 / (β - δ - 1) ^ 2) * P {ω | ENNReal.ofReal l < maxFn f ω} := by
  set c := ENNReal.ofReal (δ * l) ^ 2 with hc
  have hcT : c ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  set κ := (β - δ - 1) * l with hκ
  have hκ0 : 0 < κ := mul_pos (by linarith) hl
  have hmart := gtr_martingale hf l c
  have h15 := eq_1_5_core (Or.inl hmart) 2 one_le_two κ hκ0
  have hsub := event_subset (ℱ := ℱ) (P := P) f β δ l hβ hδ hδβ hl
  have hnorm : pNorm P 2 (gtr ℱ P f l c) ^ (2 : ℝ)
      ≤ c * P {ω | ENNReal.ofReal l < maxFn f ω} := by
    have hle : pNorm P 2 (gtr ℱ P f l c)
        ≤ (c * P {ω | ENNReal.ofReal l < maxFn f ω}) ^ (1 / 2 : ℝ) := by
      refine iSup₂_le fun n _ => ?_
      simp only [lpNormE]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      have : ∀ ω, ENNReal.ofReal |gtr ℱ P f l c n ω| ^ (2 : ℝ)
          = ENNReal.ofReal (gtr ℱ P f l c n ω ^ 2) := fun ω => by
        rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two, sq_abs]
      simp_rw [this]
      exact lintegral_gtr_sq_le hf l hcT n
    calc pNorm P 2 (gtr ℱ P f l c) ^ (2 : ℝ)
        ≤ ((c * P {ω | ENNReal.ofReal l < maxFn f ω}) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hle (by norm_num)
      _ = c * P {ω | ENNReal.ofReal l < maxFn f ω} := rpow_one_div_rpow _ two_ne_zero
  have hκ2 : ENNReal.ofReal (κ ^ (2 : ℝ)) ≠ 0 := by
    rw [Real.rpow_two]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hκ2T : ENNReal.ofReal (κ ^ (2 : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc P {ω | ENNReal.ofReal (β * l) < maxFn f ω ∧
          max (condSqFn ℱ P f ω) (maxFn (dseq f) ω) ≤ ENNReal.ofReal (δ * l)}
      ≤ P {ω | ENNReal.ofReal κ < maxFn (gtr ℱ P f l c) ω} := measure_mono hsub
    _ ≤ (c * P {ω | ENNReal.ofReal l < maxFn f ω}) / ENNReal.ofReal (κ ^ (2 : ℝ)) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hκ2) (Or.inl hκ2T), mul_comm]
        exact h15.trans hnorm
    _ = ENNReal.ofReal (δ ^ 2 / (β - δ - 1) ^ 2) * P {ω | ENNReal.ofReal l < maxFn f ω} := by
        rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv, hc, Real.rpow_two,
          ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 2
        have : β - δ - 1 ≠ 0 := by intro h; linarith
        rw [hκ]
        field_simp


/-! ### Theorem 21.1 -/

lemma measurable_maxFn_of (h : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (h n)) : Measurable (maxFn h) := by
  unfold maxFn maxFnN
  refine Measurable.iSup fun k => Measurable.iSup fun n => Measurable.iSup fun _ => ?_
  exact (continuous_abs.measurable.comp (hm n)).ennreal_ofReal

lemma measurable_dseq (hf : Martingale f ℱ P) (k : ℕ) : Measurable (dseq f k) := by
  have hm : ∀ n, Measurable (f n) := fun n =>
    (hf.stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl
  unfold dseq
  split_ifs
  · exact measurable_const
  · exact hm 1
  · exact (hm k).sub (hm (k - 1))

lemma measurable_condSqFn (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) :
    Measurable (condSqFn ℱ P f) := by
  have : condSqFn ℱ P f = fun ω => (∑' k, Zc ℱ P f k ω) ^ (1 / 2 : ℝ) := by
    funext ω; exact condSqFn_eq ω
  rw [this]
  exact (Measurable.ennreal_tsum fun k => measurable_Zc k).pow_const _

lemma isPhi_pow_growth {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} (hΦ : IsPhi Φ c) (k : ℕ) (x : ℝ≥0∞) :
    Φ (2 ^ k * x) ≤ (c : ℝ≥0∞) ^ k * Φ x := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc Φ (2 ^ (k + 1) * x) = Φ (2 * (2 ^ k * x)) := by ring_nf
      _ ≤ c * Φ (2 ^ k * x) := hΦ.growth _
      _ ≤ c * ((c : ℝ≥0∞) ^ k * Φ x) := mul_le_mul_right ih _
      _ = (c : ℝ≥0∞) ^ (k + 1) * Φ x := by ring

theorem theorem_21_1_core (c : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ), Martingale f ℱ P →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, IsPhi Φ c →
          ∫⁻ ω, Φ (maxFn f ω) ∂P
            ≤ (C : ℝ≥0∞) * ∫⁻ ω, Φ (condSqFn ℱ P f ω) ∂P
              + (C : ℝ≥0∞) * ∫⁻ ω, Φ (maxFn (dseq f) ω) ∂P := by
  -- choice of the parameters
  set n : ℕ := ⌈(c : ℝ)⌉₊ with hn
  set q : ℝ := (2 : ℝ) ^ n with hq
  have hq1 : (1 : ℝ) ≤ q := one_le_pow₀ (by norm_num)
  have hq0 : 0 < q := by linarith
  set δ : ℝ := 1 / (2 * q) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := by
    rw [hδ, div_lt_one (by positivity)]; linarith
  set ε : ℝ := δ ^ 2 / (2 - δ - 1) ^ 2 with hε
  have hε' : ε = 1 / (2 * q - 1) ^ 2 := by
    have h2 : 2 - δ - 1 = (2 * q - 1) / (2 * q) := by
      rw [hδ]
      field_simp
      ring
    rw [hε, h2, hδ, div_pow, div_pow, one_pow, div_div_div_cancel_right₀ (by positivity)]
  have hε0 : 0 < ε := by
    rw [hε']
    have : 0 < 2 * q - 1 := by linarith
    positivity
  have hcq : (c : ℝ) < q ^ 2 := by
    have h1 : (c : ℝ) ≤ n := Nat.le_ceil _
    have h2 : (n : ℝ) < (4 : ℝ) ^ n := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 4)
    have h3 : (4 : ℝ) ^ n = q ^ 2 := by
      rw [hq, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]
    linarith
  have hγε : (c : ℝ) * ε < 1 := by
    rw [hε']
    have h1 : 0 < 2 * q - 1 := by linarith
    have h2 : q ^ 2 ≤ (2 * q - 1) ^ 2 := by nlinarith
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith
  set γ : ℝ≥0 := c with hγ
  set η : ℝ≥0 := c ^ (n + 1) with hη
  set C₀ : ℝ := γ * η / (1 - γ * ε) with hC₀
  refine ⟨Real.toNNReal C₀ + 1, by positivity, ?_⟩
  intro Ω mΩ P _ ℱ f hf Φ hΦ
  have hΦm : Measurable Φ := hΦ.cont.measurable
  -- the good-λ inequality
  have h71 : ∀ l : ℝ, 0 < l →
      P {ω | ENNReal.ofReal (2 * l) < maxFn f ω ∧
          (fun ω => max (condSqFn ℱ P f ω) (maxFn (dseq f) ω)) ω ≤ ENNReal.ofReal (δ * l)}
        ≤ ENNReal.ofReal ε * P {ω | ENNReal.ofReal l < maxFn f ω} := fun l hl =>
    eq_21_2_core hf 2 δ (by norm_num) hδ0 (by linarith) l hl
  -- the growth conditions
  have h72 : ∀ l : ℝ, 0 < l →
      Φ (ENNReal.ofReal (2 * l)) ≤ γ * Φ (ENNReal.ofReal l) ∧
      Φ (ENNReal.ofReal (δ⁻¹ * l)) ≤ η * Φ (ENNReal.ofReal l) := by
    intro l hl
    constructor
    · rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      exact hΦ.growth _
    · have hδinv : δ⁻¹ = (2 : ℝ) ^ (n + 1) := by
        rw [hδ, one_div, inv_inv, hq, pow_succ]; ring
      rw [hδinv, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat, hη, ENNReal.coe_pow]
      exact isPhi_pow_growth hΦ (n + 1) _
  have hF : Measurable fun ω => max (condSqFn ℱ P f ω) (maxFn (dseq f) ω) :=
    (measurable_condSqFn ℱ P f).max (measurable_maxFn_of _ (measurable_dseq hf))
  have hmain := lemma_7_1_core P Φ c hΦ _ (maxFn f) hF (measurable_maxFn hf) 2 δ ε (by norm_num)
    hδ0 hε0 h71 γ η h72 hγε
  -- split the right-hand side
  have hsplit : ∫⁻ ω, Φ (max (condSqFn ℱ P f ω) (maxFn (dseq f) ω)) ∂P
      ≤ ∫⁻ ω, Φ (condSqFn ℱ P f ω) ∂P + ∫⁻ ω, Φ (maxFn (dseq f) ω) ∂P := by
    rw [← lintegral_add_left (f := fun ω => Φ (condSqFn ℱ P f ω)) (hΦm.comp (measurable_condSqFn ℱ P f))]
    refine lintegral_mono fun ω => ?_
    rcases le_total (condSqFn ℱ P f ω) (maxFn (dseq f) ω) with h | h
    · rw [max_eq_right h]; exact le_add_left le_rfl
    · rw [max_eq_left h]; exact le_add_right le_rfl
  have hC : ENNReal.ofReal C₀ ≤ ((Real.toNNReal C₀ + 1 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_add, ENNReal.coe_one]
    exact le_add_right le_rfl
  calc ∫⁻ ω, Φ (maxFn f ω) ∂P
      ≤ ENNReal.ofReal C₀ * ∫⁻ ω, Φ (max (condSqFn ℱ P f ω) (maxFn (dseq f) ω)) ∂P := hmain
    _ ≤ ENNReal.ofReal C₀ * (∫⁻ ω, Φ (condSqFn ℱ P f ω) ∂P
          + ∫⁻ ω, Φ (maxFn (dseq f) ω) ∂P) := mul_le_mul' le_rfl hsplit
    _ ≤ ((Real.toNNReal C₀ + 1 : ℝ≥0) : ℝ≥0∞) * (∫⁻ ω, Φ (condSqFn ℱ P f ω) ∂P
          + ∫⁻ ω, Φ (maxFn (dseq f) ω) ∂P) := mul_le_mul' hC le_rfl
    _ = _ := mul_add _ _ _

end BurkholderDFI.CondSquare

open BurkholderDFI.CondSquare


theorem solution (c : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ), Martingale f ℱ P →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c →
          ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn f ω) ∂P
            ≤ (C : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.condSqFn ℱ P f ω) ∂P
              + (C : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn (BurkholderDFI.SquareFnLp.dseq f) ω) ∂P := by
  exact theorem_21_1_core c
