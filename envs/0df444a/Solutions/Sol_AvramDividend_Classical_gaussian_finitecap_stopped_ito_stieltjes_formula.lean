-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_finitecap_stopped_ito_stieltjes_formula
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T07:38:42.285669+00:00
-- url     : https://prove2.me/submissions/f7cbb515-df3c-41f8-bb46-fc1acce7034f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_gaussian_bounded_stop_positive_time_ito_stieltjes_of_reserve_range
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_positive_stop_terminal_prepayment_band

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

set_option maxHeartbeats 800000 in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 < q) (v : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (a b : ℝ) (ha : a < 0) (hb : C.toReal < b)
    (hvSmooth : ContDiffOn ℝ 2 v (Ioo a b))
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) :
  let ρ : Ω → ℝ≥0 := fun ω => (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
  let A : Ω → Set ℝ := fun ω =>
    paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ)
  let pre : ℝ≥0 → Ω → ℝ := riskProcess X x D
  let jump : ℝ≥0 → Ω → ℝ := fun t ω => rightLimit D t ω - D t ω
  let post : ℝ≥0 → Ω → ℝ := fun t ω => pre t ω - jump t ω
  let toll : Ω → ℝ → ℝ := fun ω s =>
    if jump s.toNNReal ω = 0 then deriv v (pre s.toNNReal ω)
    else (v (pre s.toNNReal ω) - v (post s.toNNReal ω)) / jump s.toNNReal ω
  let paid : Ω → ℝ → ℝ := fun ω s => Real.exp (-(q * s)) * toll ω s
  let finish : Ω → ℝ := fun ω =>
    if ρ ω = 0 then post (ρ ω) ω else pre (ρ ω) ω
  let driftTerm : Ω → ℝ → ℝ := fun ω s =>
    Real.exp (-(q * s)) * (X.generator v (pre s.toNNReal ω) - q * v (pre s.toNNReal ω))
  ∃ M : Ω → ℝ,
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
      ∀ᵐ ω ∂P,
        IntegrableOn (paid ω) (A ω) (dividendMeasure D ω) ∧
        (Real.exp (-(q * (ρ ω : ℝ))) * v (finish ω) +
          (∫ s in A ω, paid ω s ∂(dividendMeasure D ω)) =
          v x + M ω + (∫ s in Ico (0 : ℝ) (ρ ω : ℝ), driftTerm ω s)) := by
  classical
  let ρ : Ω → ℝ≥0 := fun ω => (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
  let A : Ω → Set ℝ := fun ω =>
    paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ)
  let pre : ℝ≥0 → Ω → ℝ := riskProcess X x D
  let jump : ℝ≥0 → Ω → ℝ := fun t ω => rightLimit D t ω - D t ω
  let post : ℝ≥0 → Ω → ℝ := fun t ω => pre t ω - jump t ω
  let toll : Ω → ℝ → ℝ := fun ω s =>
    if jump s.toNNReal ω = 0 then deriv v (pre s.toNNReal ω)
    else (v (pre s.toNNReal ω) - v (post s.toNNReal ω)) / jump s.toNNReal ω
  let paid : Ω → ℝ → ℝ := fun ω s => Real.exp (-(q * s)) * toll ω s
  let finish : Ω → ℝ := fun ω =>
    if ρ ω = 0 then post (ρ ω) ω else pre (ρ ω) ω
  let driftTerm : Ω → ℝ → ℝ := fun ω s =>
    Real.exp (-(q * s)) * (X.generator v (pre s.toNNReal ω) - q * v (pre s.toNNReal ω))
  change ∃ M : Ω → ℝ, Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
    ∀ᵐ ω ∂P, IntegrableOn (paid ω) (A ω) (dividendMeasure D ω) ∧
      Real.exp (-(q * (ρ ω : ℝ))) * v (finish ω) +
          (∫ s in A ω, paid ω s ∂(dividendMeasure D ω)) =
        v x + M ω + (∫ s in Ico (0 : ℝ) (ρ ω : ℝ), driftTerm ω s)
  have hMinFinite (ω : Ω) : min (ruinTime X x D ω) (n : ℝ≥0∞) ≠ ⊤ :=
    ne_of_lt ((min_le_right _ _).trans_lt (ENNReal.natCast_lt_top n))
  have hρCast (ω : Ω) : (ρ ω : ℝ≥0∞) = min (ruinTime X x D ω) (n : ℝ≥0∞) :=
    ENNReal.coe_toNNReal (hMinFinite ω)
  have hρLe (ω : Ω) : ρ ω ≤ (n : ℝ≥0) := by
    apply ENNReal.coe_le_coe.mp
    rw [hρCast]
    exact min_le_right _ _
  obtain ⟨τ, hτ, _, hτstop⟩ :=
    avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping X x D n
      (ruinTime_measurable X x D hD.1.1)
      (ruinTime_stopping_rightCont_filtration X x D hD.1.1)
  have hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)) := by
    have hτρ : τ = ρ := funext hτ
    simpa only [hτρ] using hτstop
  have hxcap : x ≤ C.toReal := by
    simpa only [ENNReal.toReal_ofReal hx.le] using ENNReal.toReal_mono hFinite hxc
  have hJump (ω : Ω) (t : ℝ≥0) : 0 ≤ jump t ω :=
    sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD.1.1 ω t)
  have hpre0 (ω : Ω) : pre 0 ω = x := by
    simp [pre, riskProcess, X.X_zero, hD.1.1.1 ω]
  have hpost0 (ω : Ω) : post 0 ω ∈ Icc (0 : ℝ) C.toReal := by
    have hPay := hD.1.2 ω 0 (Or.inl rfl)
    exact ⟨sub_nonneg.mpr hPay, (sub_le_self _ (hJump ω 0)).trans
      (le_of_eq_of_le (hpre0 ω) hxcap)⟩
  have hInitial (ω : Ω) : x - rightLimit D 0 ω ∈ Icc (0 : ℝ) C.toReal := by
    simpa only [post, jump, hpre0 ω, hD.1.1.1 ω, sub_zero] using hpost0 ω
  have hpreBand (ω : Ω) (t : ℝ≥0) (ht : t < ρ ω) : pre t ω ∈ Icc (0 : ℝ) C.toReal := by
    have htRuin : (t : ℝ≥0∞) < ruinTime X x D ω := by
      have hl := ENNReal.coe_lt_coe.mpr ht
      rw [hρCast] at hl
      exact hl.trans_le (min_le_left _ _)
    obtain ⟨h0, hUpper⟩ :=
      capped_riskProcess_range_before_ruin_including_zero X x hx.le C hxc D hD ω t htRuin
    exact ⟨h0, by
      simpa only [pre, ENNReal.toReal_ofReal h0] using ENNReal.toReal_mono hFinite hUpper⟩
  have hBefore (ω : Ω) (t : ℝ≥0) (_ht0 : 0 < t) (ht : t < ρ ω) :
      pre t ω ∈ Icc (0 : ℝ) C.toReal ∧ post t ω ∈ Icc (0 : ℝ) C.toReal := by
    have htRuin : (t : ℝ≥0∞) < ruinTime X x D ω := by
      have hl := ENNReal.coe_lt_coe.mpr ht
      rw [hρCast] at hl
      exact hl.trans_le (min_le_left _ _)
    have hp := hpreBand ω t ht
    exact ⟨hp, sub_nonneg.mpr (hD.1.2 ω t (Or.inr htRuin)),
      (sub_le_self _ (hJump ω t)).trans hp.2⟩
  have hAtStop : ∀ᵐ ω ∂P, 0 < ρ ω → pre (ρ ω) ω ∈ Icc (0 : ℝ) C.toReal :=
    avram_gledger20_original_positive_stop_terminal_prepayment_band
      X hν x D hD.1.1 ρ 0 C.toReal (Eventually.of_forall fun ω t _ ht => hpreBand ω t ht)
  have hActive (ω : Ω) : A ω = ({0} : Set ℝ) ∪ Ioo (0 : ℝ) (ρ ω : ℝ) := by
    ext s
    simp only [A, mem_inter_iff, paymentTimes, mem_setOf_eq, mem_Iic,
      mem_union, mem_singleton_iff, mem_Ioo]
    constructor
    · rintro ⟨⟨hs0, hz | hlt⟩, _⟩
      · exact Or.inl hz
      · rcases hs0.eq_or_lt with hz | hp
        · exact Or.inl hz.symm
        · right
          refine ⟨hp, ?_⟩
          rw [← hρCast ω, ← ENNReal.ofNNReal_toNNReal] at hlt
          have hlt' : s.toNNReal < ρ ω := ENNReal.coe_lt_coe.mp hlt
          have hh : (s.toNNReal : ℝ) < (ρ ω : ℝ) := by exact_mod_cast hlt'
          simpa only [Real.coe_toNNReal s hs0] using hh
    · rintro (rfl | ⟨hs0, hlt⟩)
      · exact ⟨⟨le_rfl, Or.inl rfl⟩, by positivity⟩
      · refine ⟨⟨hs0.le, Or.inr ?_⟩, ?_⟩
        · rw [← hρCast ω, ← ENNReal.ofNNReal_toNNReal]
          apply ENNReal.coe_lt_coe.mpr
          have hh : (s.toNNReal : ℝ) < (ρ ω : ℝ) := by
            simpa only [Real.coe_toNNReal s hs0.le] using hlt
          exact_mod_cast hh
        · have hh : (ρ ω : ℝ) ≤ (n : ℝ) := by exact_mod_cast hρLe ω
          exact hlt.le.trans hh
  obtain ⟨M, hMI, hM0, hM⟩ :=
    gaussian_bounded_stop_positive_time_ito_stieltjes_of_reserve_range
      X hX hBV hν q v a b 0 C.toReal ha hb hvSmooth x D hD.1.1 ρ (n : ℝ≥0)
      hρstop hρLe hInitial hBefore hAtStop
  refine ⟨M, hMI, hM0, ?_⟩
  filter_upwards [hM] with ω hω
  have hAtom : dividendMeasure D ω ({0} : Set ℝ) = ENNReal.ofReal (jump 0 ω) := by
    simpa only [NNReal.coe_zero, jump] using
      dividendMeasure_singleton_eq_rightLimit_sub D hD.1.1 ω 0
  have hAtomI : IntegrableOn (paid ω) ({0} : Set ℝ) (dividendMeasure D ω) :=
    integrableOn_singleton (hx := by rw [hAtom]; exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
  have hPair : (∫ s in ({0} : Set ℝ), paid ω s ∂(dividendMeasure D ω)) =
      v x - v (post 0 ω) := by
    rw [integral_singleton, measureReal_def, hAtom, ENNReal.toReal_ofReal (hJump ω 0), smul_eq_mul]
    have hPaid0 : paid ω 0 = toll ω 0 := by simp [paid]
    rw [hPaid0]
    change jump 0 ω *
      (if jump (0 : ℝ).toNNReal ω = 0 then deriv v (pre (0 : ℝ).toNNReal ω)
        else (v (pre (0 : ℝ).toNNReal ω) - v (post (0 : ℝ).toNNReal ω)) /
          jump (0 : ℝ).toNNReal ω) = _
    rw [Real.toNNReal_zero]
    split_ifs with hz
    · simp [hz, post, hpre0 ω]
    · rw [hpre0 ω]
      field_simp
  have hSplit : Disjoint ({0} : Set ℝ) (Ioo (0 : ℝ) (ρ ω : ℝ)) := by
    simp
  rw [hActive ω]
  refine ⟨hAtomI.union hω.1, ?_⟩
  rw [setIntegral_union hSplit measurableSet_Ioo hAtomI hω.1, hPair]
  linarith only [hω.2]
