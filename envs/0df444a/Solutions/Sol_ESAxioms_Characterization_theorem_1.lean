-- Prove2me | solution 1 for ESAxioms.Characterization.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T07:02:11.605857+00:00
-- url     : https://prove2.me/submissions/aa3ef61f-73b5-4f47-b38b-eac4ccd62079

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting
import Theorems.Thm_ESAxioms_Characterization_proposition_1
import Theorems.Thm_ESAxioms_Characterization_proposition_4
import Theorems.Thm_ESAxioms_Characterization_lemma_A2

open MeasureTheory ProbabilityTheory Filter Topology

namespace ESAxT1Aux

open ESAxioms.Characterization

variable {Ω : Type*} [MeasurableSpace Ω]

lemma VaR_eq (P : Measure Ω) (q : ℝ) (X : Ω → ℝ) :
    VaR P q X = sInf {x | q ≤ TailRiskSharing.VaRConv.distFn P X x} := by
  simp [VaR, TailRiskSharing.VaRConv.VaRL]

/-- VaR of a nonpositive variable that is negative with probability at most `p`. -/
lemma VaR_nonpos_zero (P : Measure Ω) [IsProbabilityMeasure P] (p q : ℝ) (hpq : p < q)
    (hq : q ≤ 1) (Y : Ω → ℝ) (hY : ∀ ω, Y ω ≤ 0) (hneg : P.real {ω | Y ω < 0} ≤ p) :
    VaR P q Y = 0 := by
  rw [VaR_eq]
  apply IsLeast.csInf_eq
  refine ⟨?_, ?_⟩
  · show q ≤ P.real {ω | Y ω ≤ 0}
    have : {ω | Y ω ≤ 0} = Set.univ := Set.eq_univ_of_forall hY
    rw [this, probReal_univ]; exact hq
  · intro x hx
    by_contra hlt
    push Not at hlt
    have h1 : TailRiskSharing.VaRConv.distFn P Y x ≤ P.real {ω | Y ω < 0} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      linarith
    have : q ≤ TailRiskSharing.VaRConv.distFn P Y x := hx
    linarith

lemma ES_nonpos_zero (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (Y : Ω → ℝ) (hY : ∀ ω, Y ω ≤ 0) (hneg : P.real {ω | Y ω < 0} ≤ p) :
    ES P p Y = 0 := by
  unfold ES
  have : ∫ q in Set.Ioo p 1, VaR P q Y = ∫ q in Set.Ioo p 1, (0:ℝ) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro q hq
    exact VaR_nonpos_zero P p q hq.1 hq.2.le Y hY hneg
  rw [this]; simp

lemma VaR_const (P : Measure Ω) [IsProbabilityMeasure P] (q c : ℝ) (hq0 : 0 < q) (hq : q ≤ 1) :
    VaR P q (fun _ => c) = c := by
  rw [VaR_eq]
  apply IsLeast.csInf_eq
  refine ⟨?_, ?_⟩
  · show q ≤ P.real {ω : Ω | c ≤ c}
    simp; exact hq
  · intro x hx
    by_contra hlt
    push Not at hlt
    have : q ≤ P.real {ω : Ω | c ≤ x} := hx
    have h2 : {ω : Ω | c ≤ x} = ∅ := by
      ext ω; simp; linarith
    rw [h2] at this; simp at this; linarith

lemma ES_const (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (c : ℝ) : ES P p (fun _ => c) = c := by
  unfold ES
  have : ∫ q in Set.Ioo p 1, VaR P q (fun _ => c) = ∫ q in Set.Ioo p 1, c := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro q hq
    exact VaR_const P q c (lt_trans hp.1 hq.1) hq.2.le
  rw [this, setIntegral_const]
  rw [Real.volume_real_Ioo_of_le hp.2.le]
  have : (1 - p) ≠ 0 := by linarith [hp.2]
  simp only [smul_eq_mul]
  field_simp

lemma VaR_indicator (P : Measure Ω) [IsProbabilityMeasure P] (B : Set Ω) (hB : MeasurableSet B)
    (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1) :
    VaR P q (B.indicator (fun _ => (1:ℝ))) = (Set.Ioi (1 - P.real B)).indicator (fun _ => (1:ℝ)) q := by
  rw [VaR_eq]
  have hc : P.real Bᶜ = 1 - P.real B := probReal_compl_eq_one_sub hB
  by_cases hqs : 1 - P.real B < q
  · rw [Set.indicator_of_mem (by exact hqs)]
    apply IsLeast.csInf_eq
    refine ⟨?_, ?_⟩
    · show q ≤ P.real {ω | B.indicator (fun _ => (1:ℝ)) ω ≤ 1}
      have : {ω | B.indicator (fun _ => (1:ℝ)) ω ≤ 1} = Set.univ := by
        ext ω; by_cases h : ω ∈ B <;> simp [h]
      rw [this, probReal_univ]; exact hq
    · intro x hx
      by_contra hlt
      push Not at hlt
      have hx' : q ≤ P.real {ω | B.indicator (fun _ => (1:ℝ)) ω ≤ x} := hx
      have h1 : P.real {ω | B.indicator (fun _ => (1:ℝ)) ω ≤ x} ≤ P.real Bᶜ := by
        refine measureReal_mono ?_ (measure_ne_top _ _)
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω
        intro hωB
        rw [Set.indicator_of_mem hωB] at hω
        linarith
      linarith
  · push Not at hqs
    rw [Set.indicator_of_notMem (by simpa using hqs)]
    apply IsLeast.csInf_eq
    refine ⟨?_, ?_⟩
    · show q ≤ P.real {ω | B.indicator (fun _ => (1:ℝ)) ω ≤ 0}
      have : {ω | B.indicator (fun _ => (1:ℝ)) ω ≤ 0} = Bᶜ := by
        ext ω; by_cases h : ω ∈ B <;> simp [h]
      rw [this, hc]; exact hqs
    · intro x hx
      by_contra hlt
      push Not at hlt
      have hx' : q ≤ P.real {ω | B.indicator (fun _ => (1:ℝ)) ω ≤ x} := hx
      have : {ω | B.indicator (fun _ => (1:ℝ)) ω ≤ x} = ∅ := by
        ext ω; by_cases h : ω ∈ B <;> simp [h] <;> linarith
      rw [this] at hx'; simp at hx'; linarith

lemma ES_indicator (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (B : Set Ω) (hB : MeasurableSet B) (hs : P.real B ≤ 1 - p) :
    ES P p (B.indicator (fun _ => (1:ℝ))) = P.real B / (1 - p) := by
  unfold ES
  have : ∫ q in Set.Ioo p 1, VaR P q (B.indicator (fun _ => (1:ℝ))) =
      ∫ q in Set.Ioo p 1, (Set.Ioi (1 - P.real B)).indicator (fun _ => (1:ℝ)) q := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro q hq
    exact VaR_indicator P B hB q (lt_trans hp.1 hq.1) hq.2.le
  rw [this, setIntegral_indicator measurableSet_Ioi]
  have hI : Set.Ioo p 1 ∩ Set.Ioi (1 - P.real B) = Set.Ioo (1 - P.real B) 1 := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioi]; constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
  have hB0 : 0 ≤ P.real B := measureReal_nonneg
  rw [hI, setIntegral_const, Real.volume_real_Ioo_of_le (by linarith)]
  have : (1 - p) ≠ 0 := by linarith [hp.2]
  simp only [smul_eq_mul, mul_one]
  field_simp
  ring

/-- Halving: an atomless probability space has events of arbitrarily small positive probability. -/
lemma exists_small (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (n : ℕ) :
    ∃ B : Set Ω, MeasurableSet B ∧ 0 < P.real B ∧ P.real B ≤ (1/2 : ℝ) ^ n := by
  induction n with
  | zero => exact ⟨Set.univ, MeasurableSet.univ, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨B, hB, hpos, hle⟩ := ih
    have hB' : 0 < P B := by
      rw [measureReal_def] at hpos
      exact ENNReal.toReal_pos_iff.mp hpos |>.1
    obtain ⟨t, htB, ht, ht0, htlt⟩ := hP B hB hB'
    have ht0' : 0 < P.real t := by
      rw [measureReal_def]; exact ENNReal.toReal_pos ht0.ne' (measure_ne_top _ _)
    have htlt' : P.real t < P.real B := by
      rw [measureReal_def, measureReal_def]
      exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr htlt
    have hd : P.real (B \ t) = P.real B - P.real t := measureReal_sdiff htB ht
    by_cases h : P.real t ≤ P.real B / 2
    · refine ⟨t, ht, ht0', ?_⟩
      rw [pow_succ]; linarith
    · refine ⟨B \ t, hB.diff ht, by rw [hd]; linarith, ?_⟩
      rw [hd, pow_succ]; push Not at h; linarith

lemma const_mem_L1 (P : Measure Ω) [IsProbabilityMeasure P] (c : ℝ) :
    (fun _ : Ω => c) ∈ L1 P := ⟨measurable_const, integrable_const c⟩

lemma ind_mem_L1 (P : Measure Ω) [IsProbabilityMeasure P] (B : Set Ω) (hB : MeasurableSet B)
    (c : ℝ) : (fun ω => c * B.indicator (fun _ => (1:ℝ)) ω) ∈ L1 P :=
  ⟨(measurable_const.indicator hB).const_mul c, ((integrable_const (1:ℝ)).indicator hB).const_mul c⟩

/-- Proof of Theorem 1, (⇒), p. 22: if `ρ = a𝔼 + b ESₚ` on `L¹` is monotone, prudent and
normalized, then `a = 0` and `b = 1`. -/
lemma core (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (ρ : (Ω → ℝ) → ℝ) (h1 : ρ (fun _ => 1) = 1) (hM : AxiomM (L1 P) ρ) (hPr : AxiomP (L1 P) ρ)
    (a b : ℝ) (hab : ∀ X ∈ L1 P, ρ X = a * ∫ ω, X ω ∂P + b * ES P p X) :
    ∀ X ∈ L1 P, ρ X = ES P p X := by
  -- normalization
  have hsum : a + b = 1 := by
    have := hab _ (const_mem_L1 P 1)
    rw [h1, ES_const P p hp] at this
    simp at this; linarith
  have h0 : ρ (fun _ => 0) = 0 := by
    rw [hab _ (const_mem_L1 P 0), ES_const P p hp]; simp
  -- small events
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hp.1 (by norm_num : (1/2:ℝ) < 1)
  choose B hBm hBpos hBle using fun k : ℕ => exists_small P hP (k + m)
  have hBp : ∀ k, P.real (B k) < p := by
    intro k
    have : (1/2:ℝ) ^ (k + m) ≤ (1/2) ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith [hBle k]
  have hBi : ∀ k, P (B k) ≤ (2⁻¹ : ENNReal) ^ k := by
    intro k
    rw [← ofReal_measureReal (μ := P) (s := B k)]
    have : P.real (B k) ≤ (1/2:ℝ) ^ k := by
      have : (1/2:ℝ) ^ (k + m) ≤ (1/2) ^ k :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith [hBle k]
    calc ENNReal.ofReal (P.real (B k)) ≤ ENNReal.ofReal ((1/2:ℝ) ^ k) := ENNReal.ofReal_le_ofReal this
      _ = (2⁻¹ : ENNReal) ^ k := by
        rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos two_pos]
        simp
  have hsumB : ∑' i, P (B i) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hBi)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]; simp
  set N : Set Ω := ⋂ n, ⋃ i ≥ n, B i with hN
  have hNm : MeasurableSet N :=
    MeasurableSet.iInter fun n => MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hBm i
  have hN0 : P N = 0 := by
    have := measure_limsup_atTop_eq_zero (μ := P) hsumB
    rw [limsup_eq_iInf_iSup_of_nat] at this
    simpa [hN, Set.iInf_eq_iInter, Set.iSup_eq_iUnion] using this
  have hN0' : P.real N = 0 := by simp [measureReal_def, hN0]
  -- the sequence ξₖ = -(ℙ Bₖ)⁻¹ 1_{Bₖ \ N}
  set ξ : ℕ → Ω → ℝ := fun k ω => -(P.real (B k))⁻¹ * (B k \ N).indicator (fun _ => (1:ℝ)) ω
    with hξ
  have hξL1 : ∀ k, ξ k ∈ L1 P := fun k => ind_mem_L1 P _ ((hBm k).diff hNm) _
  have hξE : ∀ k, ∫ ω, ξ k ω ∂P = -1 := by
    intro k
    simp only [hξ]
    rw [integral_const_mul, integral_indicator_const _ ((hBm k).diff hNm),
      measureReal_sdiff_null hN0']
    have := (hBpos k).ne'
    simp only [smul_eq_mul, mul_one]
    field_simp
  have hξle : ∀ k ω, ξ k ω ≤ 0 := by
    intro k ω
    simp only [hξ]
    have hc : 0 ≤ (P.real (B k))⁻¹ := inv_nonneg.mpr (hBpos k).le
    have hi : 0 ≤ (B k \ N).indicator (fun _ => (1:ℝ)) ω :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    nlinarith
  have hξES : ∀ k, ES P p (ξ k) = 0 := by
    intro k
    apply ES_nonpos_zero P p hp _ (hξle k)
    have hsub : {ω | ξ k ω < 0} ⊆ B k := by
      intro ω hω
      by_contra hn
      simp only [Set.mem_setOf_eq, hξ] at hω
      rw [Set.indicator_of_notMem (fun h => hn h.1)] at hω
      simp at hω
    have := measureReal_mono (μ := P) hsub (measure_ne_top _ _)
    linarith [hBp k]
  have hρξ : ∀ k, ρ (ξ k) = -a := by
    intro k
    rw [hab _ (hξL1 k), hξE k, hξES k]; ring
  -- a ≥ 0 by monotonicity
  have ha0 : 0 ≤ a := by
    have := hM (ξ 0) (hξL1 0) _ (const_mem_L1 P 0) (hξle 0)
    rw [hρξ 0, h0] at this; linarith
  -- a ≤ 0 by prudence
  have ha1 : a ≤ 0 := by
    have hconv : ∀ ω, Tendsto (fun k => ξ k ω) atTop (𝓝 ((fun _ : Ω => (0:ℝ)) ω)) := by
      intro ω
      apply tendsto_const_nhds.congr'
      by_cases hω : ω ∈ N
      · exact Filter.Eventually.of_forall fun k => by
          simp only [hξ]; rw [Set.indicator_of_notMem (fun h => h.2 hω)]; simp
      · simp only [hN, Set.mem_iInter, not_forall] at hω
        obtain ⟨n, hn⟩ := hω
        simp only [Set.mem_iUnion, not_exists] at hn
        rw [Filter.EventuallyEq, Filter.eventually_atTop]
        refine ⟨n, fun k hk => ?_⟩
        simp only [hξ]
        rw [Set.indicator_of_notMem (fun h => hn k hk h.1)]; simp
    have := hPr ξ (fun _ => 0) hξL1 (const_mem_L1 P 0) hconv (-a)
      (by simp only [hρξ]; exact tendsto_const_nhds)
    rw [h0] at this; linarith
  have ha : a = 0 := le_antisymm ha1 ha0
  have hb : b = 1 := by linarith
  intro X hX
  rw [hab X hX, ha, hb]; ring

lemma Lq_one (P : Measure Ω) : Lq P 1 = L1 P := by
  ext X; simp [Lq, L1, memLp_one_iff_integrable]

/-- Uniqueness of `p`: `ESₚ = ES_{p'}` on `L¹` forces `p = p'` (atomless space). -/
lemma ES_inj (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p p' : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (hp' : p' ∈ Set.Ioo (0:ℝ) 1) (h : ∀ X ∈ L1 P, ES P p X = ES P p' X) : p = p' := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (lt_min (sub_pos.mpr hp.2) (sub_pos.mpr hp'.2))
    (by norm_num : (1/2:ℝ) < 1)
  obtain ⟨B, hB, hpos, hle⟩ := exists_small P hP m
  have h1 : P.real B ≤ 1 - p := by linarith [min_le_left (1 - p) (1 - p')]
  have h2 : P.real B ≤ 1 - p' := by linarith [min_le_right (1 - p) (1 - p')]
  have hX : B.indicator (fun _ => (1:ℝ)) ∈ L1 P :=
    ⟨measurable_const.indicator hB, (integrable_const (1:ℝ)).indicator hB⟩
  have := h _ hX
  rw [ES_indicator P p hp B hB h1, ES_indicator P p' hp' B hB h2] at this
  have hne : (1 - p) ≠ 0 := by linarith [hp.2]
  have hne' : (1 - p') ≠ 0 := by linarith [hp'.2]
  rw [div_eq_div_iff hne hne'] at this
  have := mul_left_cancel₀ hpos.ne' this
  linarith

end ESAxT1Aux

namespace ESAxioms.Characterization

open ESAxT1Aux

theorem solution_aux_forward {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (ρ : (Ω → ℝ) → ℝ) (h1 : ρ (fun _ => 1) = 1)
    (hM : AxiomM (L1 P) ρ) (hLI : AxiomLI P (L1 P) ρ) (hPr : AxiomP (L1 P) ρ)
    (A : Set Ω) (hA : IsStressEvent P (L1 P) ρ A) :
    ∀ X ∈ L1 P, ρ X = ES P (1 - P.real A) X := by
  have hp : (1 - P.real A) ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hA.2.2.1], by linarith [hA.2.1]⟩
  have hLIq : AxiomLI P (Lq P 1) ρ := by rw [Lq_one]; exact hLI
  have hAq : IsStressEvent P (Lq P 1) ρ A := by rw [Lq_one]; exact hA
  have hadd := (proposition_4 P hP 1 ρ hLIq).2 A hAq
  rw [Lq_one] at hadd
  obtain ⟨a, b, hab⟩ := (lemma_A2 P hP (1 - P.real A) hp ρ hM).1 ⟨hLI, hadd⟩
  exact core P hP _ hp ρ h1 hM hPr a b hab

end ESAxioms.Characterization

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (ρ : (Ω → ℝ) → ℝ) (h1 : ρ (fun _ => 1) = 1) :
    ((ESAxioms.Characterization.AxiomM (ESAxioms.Characterization.L1 P) ρ ∧
        ESAxioms.Characterization.AxiomLI P (ESAxioms.Characterization.L1 P) ρ ∧
        ESAxioms.Characterization.AxiomP (ESAxioms.Characterization.L1 P) ρ ∧
        ESAxioms.Characterization.AxiomNRC P (ESAxioms.Characterization.L1 P) ρ) ↔
        ∃ p ∈ Set.Ioo (0 : ℝ) 1, ∀ X ∈ ESAxioms.Characterization.L1 P,
          ρ X = ESAxioms.Characterization.ES P p X) ∧
    ((ESAxioms.Characterization.AxiomM (ESAxioms.Characterization.L1 P) ρ ∧
        ESAxioms.Characterization.AxiomLI P (ESAxioms.Characterization.L1 P) ρ ∧
        ESAxioms.Characterization.AxiomP (ESAxioms.Characterization.L1 P) ρ) →
        ∀ A : Set Ω, ESAxioms.Characterization.IsStressEvent P (ESAxioms.Characterization.L1 P) ρ A →
          (∀ X ∈ ESAxioms.Characterization.L1 P,
              ρ X = ESAxioms.Characterization.ES P (1 - P.real A) X) ∧
          ∀ p ∈ Set.Ioo (0 : ℝ) 1, (∀ X ∈ ESAxioms.Characterization.L1 P,
              ρ X = ESAxioms.Characterization.ES P p X) → p = 1 - P.real A) := by
  open ESAxioms.Characterization ESAxT1Aux in
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨hM, hLI, hPr, A, hA⟩
    have hp : (1 - P.real A) ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hA.2.2.1], by linarith [hA.2.1]⟩
    exact ⟨_, hp, solution_aux_forward P hP ρ h1 hM hLI hPr A hA⟩
  · rintro ⟨p, hp, hρ⟩
    obtain ⟨⟨hMES, hLIES, hPES⟩, -⟩ := proposition_1 P p hp
    have hM : AxiomM (L1 P) ρ := by
      intro X hX Y hY hXY; rw [hρ X hX, hρ Y hY]; exact hMES X hX Y hY hXY
    have hLI : AxiomLI P (L1 P) ρ := by
      intro X hX Y hY hXY; rw [hρ X hX, hρ Y hY]; exact hLIES X hX Y hY hXY
    have hPr : AxiomP (L1 P) ρ := by
      intro ξ X hξ hX hconv L hL
      rw [hρ X hX]
      exact hPES ξ X hξ hX hconv L (by simpa [hρ _ (hξ _)] using hL)
    have hESadd : IsPAdditive P p (L1 P) (ES P p) :=
      ((lemma_A2 P hP p hp (ES P p) hMES).2 ⟨0, 1, fun X _ => by ring⟩).2
    have hadd : IsPAdditive P p (L1 P) ρ := by
      intro X hX Y hY hXY
      have hXY1 : X + Y ∈ L1 P := ⟨hX.1.add hY.1, hX.2.add hY.2⟩
      rw [hρ _ hXY1, hρ X hX, hρ Y hY]; exact hESadd X hX Y hY hXY
    have hLIq : AxiomLI P (Lq P 1) ρ := by rw [Lq_one]; exact hLI
    have hNRC := (proposition_4 P hP 1 ρ hLIq).1.2 ⟨p, hp, by rw [Lq_one]; exact hadd⟩
    rw [Lq_one] at hNRC
    exact ⟨hM, hLI, hPr, hNRC⟩
  · rintro ⟨hM, hLI, hPr⟩ A hA
    have hrep := solution_aux_forward P hP ρ h1 hM hLI hPr A hA
    have hp0 : (1 - P.real A) ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hA.2.2.1], by linarith [hA.2.1]⟩
    refine ⟨hrep, fun p hp hρ => ?_⟩
    exact ES_inj P hP p _ hp hp0 (fun X hX => by rw [← hρ X hX, hrep X hX])
