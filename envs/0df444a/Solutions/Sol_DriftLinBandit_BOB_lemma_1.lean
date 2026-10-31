-- Prove2me | solution 1 for DriftLinBandit.BOB.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:04:26.662185+00:00
-- url     : https://prove2.me/submissions/f0fc06c2-3597-4697-9be1-4da3c9160cbd

import Mathlib
import Definitions.Def_DriftLinBandit_BOB_Bob

open MeasureTheory Matrix ProbabilityTheory DriftLinBandit.BOB

namespace BOBLemma1Aux

/-- The arithmetic heart: `exp(-2 H ln(T/√H) / r) ≤ r / T²` for `1 ≤ r ≤ H ≤ T`. -/
lemma real_key (H r T : ℕ) (hr : 1 ≤ r) (hrH : r ≤ H) (hHT : H ≤ T) :
    Real.exp (-(2 * (H : ℝ) * Real.log ((T : ℝ) / Real.sqrt H)) / r) ≤ (r : ℝ) / (T : ℝ) ^ 2 := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hH' : (r : ℝ) ≤ H := by exact_mod_cast hrH
  have hT' : (H : ℝ) ≤ T := by exact_mod_cast hHT
  have hHpos : (0 : ℝ) < H := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hL : Real.log ((T : ℝ) / Real.sqrt H) = Real.log T - Real.log H / 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_sqrt hHpos.le]
  -- core: (H - 2r) log H + r log r ≥ 0
  have hcore : 0 ≤ ((H : ℝ) - 2 * r) * Real.log H + r * Real.log r := by
    rcases eq_or_lt_of_le hrH with h | h
    · rw [h]; ring_nf; simp
    · by_cases h3 : H ≤ 2
      · have hH2 : H = 2 := by omega
        have hr1 : r = 1 := by omega
        subst hH2; subst hr1; norm_num
      · have hlogH : 1 ≤ Real.log H := by
          rw [Real.le_log_iff_exp_le hHpos]
          have : (3 : ℝ) ≤ H := by exact_mod_cast (by omega : 3 ≤ H)
          linarith [Real.exp_one_lt_d9]
        have htan : Real.log ((H : ℝ) / r) ≤ (H : ℝ) / r - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_div (by positivity) (by positivity)] at htan
        have h2 : r * (Real.log H - Real.log r) ≤ H - r := by
          have := mul_le_mul_of_nonneg_left htan (by linarith : (0 : ℝ) ≤ r)
          have e : (r : ℝ) * ((H : ℝ) / r - 1) = H - r := by field_simp
          rw [e] at this; linarith
        nlinarith
  have hlogTH : Real.log H ≤ Real.log T := Real.log_le_log hHpos hT'
  have hmain : -(2 * (H : ℝ) * Real.log ((T : ℝ) / Real.sqrt H)) / r ≤
      Real.log r - 2 * Real.log T := by
    rw [div_le_iff₀ (by linarith), hL]
    nlinarith
  calc Real.exp (-(2 * (H : ℝ) * Real.log ((T : ℝ) / Real.sqrt H)) / r)
      ≤ Real.exp (Real.log r - 2 * Real.log T) := Real.exp_le_exp.2 hmain
    _ = (r : ℝ) / (T : ℝ) ^ 2 := by
      rw [Real.exp_sub, Real.exp_log (by linarith), show (2 : ℝ) * Real.log T =
        Real.log ((T : ℝ) ^ 2) by rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]

lemma card_block (H T i : ℕ) (hi : 1 ≤ i) :
    (Finset.Icc (blockStart H i) (blockEnd H T i)).card = min (i * H) T + 1 - ((i - 1) * H + 1) := by
  simp [blockStart, blockEnd, Nat.card_Icc]

lemma card_block_le (H T i : ℕ) (hi : 1 ≤ i) :
    (Finset.Icc (blockStart H i) (blockEnd H T i)).card ≤ H := by
  rw [card_block H T i hi]
  have : i * H = (i - 1) * H + H := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp [add_mul]
  omega

lemma tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (η : ℕ → Ω → ℝ) (R : ℝ) (hη : IsSubGNoise P η R) (B : Finset ℕ) (hB : 0 < B.card)
    (a : ℝ) (ha : 0 ≤ a) (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    P {ω | a ≤ ∑ t ∈ B, sgn * η t ω} ≤
      ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * (B.card * R ^ 2)))) := by
  have hsub : ∀ t, HasSubgaussianMGF (fun ω => sgn * η t ω) (R ^ 2).toNNReal P := by
    intro t
    have h0 : HasSubgaussianMGF (η t) (R ^ 2).toNNReal P := by
      refine ⟨hη.mgf_integrable t, fun s => ?_⟩
      unfold mgf
      rw [Real.coe_toNNReal _ (sq_nonneg R)]
      have := hη.mgf_le t s
      calc ∫ ω, Real.exp (s * η t ω) ∂P ≤ Real.exp (s ^ 2 * R ^ 2 / 2) := this
        _ = Real.exp (R ^ 2 * s ^ 2 / 2) := by ring_nf
    rcases hsgn with h | h
    · subst h; simpa using h0
    · subst h
      have := h0.neg
      simpa [Pi.neg_def] using this
  have hind : iIndepFun (fun t ω => sgn * η t ω) P :=
    hη.indep.comp (fun _ x => sgn * x) (fun _ => measurable_const.mul measurable_id)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind (c := fun _ => (R ^ 2).toNNReal)
    (s := B) (fun t _ => hsub t) ha
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  refine h.trans (le_of_eq ?_)
  congr 2
  push_cast
  rw [Finset.sum_const, nsmul_eq_mul, Real.coe_toNNReal _ (sq_nonneg R)]

end BOBLemma1Aux

open BOBLemma1Aux in
theorem solution {d : ℕ} (I : Instance d) (R ν : ℝ) (hR : 0 < R) (hν : 0 < ν)
    (hνb : ∀ t ∈ Finset.Icc 1 I.T, ∀ x ∈ I.D t, |x ⬝ᵥ I.θ t| ≤ ν)
    (H : ℕ) (hH : 1 ≤ H) (hHT : H ≤ I.T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (η : ℕ → Ω → ℝ) (hη : IsSubGNoise P η R)
    (X : ℕ → Ω → (Fin d → ℝ)) (hXD : ∀ t ∈ Finset.Icc 1 I.T, ∀ ω, X t ω ∈ I.D t) :
    P {ω | ∃ i ∈ Finset.Icc 1 ⌈(I.T : ℝ) / (H : ℝ)⌉₊,
        (H : ℝ) * ν + 2 * R * Real.sqrt ((H : ℝ) * Real.log ((I.T : ℝ) / Real.sqrt H)) <
          |∑ t ∈ Finset.Icc (blockStart H i) (blockEnd H I.T i), (X t ω ⬝ᵥ I.θ t + η t ω)|} ≤
      ENNReal.ofReal (2 / (I.T : ℝ)) := by
  set T := I.T with hTdef
  set a := 2 * R * Real.sqrt ((H : ℝ) * Real.log ((T : ℝ) / Real.sqrt H)) with hadef
  have hT1 : 1 ≤ T := le_trans hH hHT
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHTr : (H : ℝ) ≤ T := by exact_mod_cast hHT
  have hLnn : 0 ≤ Real.log ((T : ℝ) / Real.sqrt H) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (Real.sqrt_pos.2 (by linarith)), one_mul]
    calc Real.sqrt H ≤ H := by
          rw [Real.sqrt_le_left (by linarith)]; nlinarith
      _ ≤ T := hHTr
  have ha0 : 0 ≤ a := by positivity
  have ha2 : a ^ 2 = 4 * R ^ 2 * (H * Real.log ((T : ℝ) / Real.sqrt H)) := by
    rw [hadef, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
  set K := ⌈(T : ℝ) / (H : ℝ)⌉₊ with hK
  let Bk : ℕ → Finset ℕ := fun i => Finset.Icc (blockStart H i) (blockEnd H T i)
  -- event inclusion
  have hsub : {ω | ∃ i ∈ Finset.Icc 1 K, (H : ℝ) * ν + a <
      |∑ t ∈ Bk i, (X t ω ⬝ᵥ I.θ t + η t ω)|} ⊆
      ⋃ i ∈ Finset.Icc 1 K, ({ω | a ≤ ∑ t ∈ Bk i, (1 : ℝ) * η t ω} ∪
        {ω | a ≤ ∑ t ∈ Bk i, (-1 : ℝ) * η t ω}) := by
    intro ω hω
    obtain ⟨i, hi, hlt⟩ := hω
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq]
    refine ⟨i, hi, ?_⟩
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    have hdet : |∑ t ∈ Bk i, X t ω ⬝ᵥ I.θ t| ≤ H * ν := by
      calc |∑ t ∈ Bk i, X t ω ⬝ᵥ I.θ t| ≤ ∑ t ∈ Bk i, |X t ω ⬝ᵥ I.θ t| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ t ∈ Bk i, ν := by
            apply Finset.sum_le_sum
            intro t ht
            simp only [Bk, Finset.mem_Icc, blockStart, blockEnd] at ht
            have htT : t ∈ Finset.Icc 1 T := Finset.mem_Icc.2 ⟨by omega, by omega⟩
            exact hνb t htT _ (hXD t htT ω)
        _ = (Bk i).card * ν := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ H * ν := by
            apply mul_le_mul_of_nonneg_right _ hν.le
            exact_mod_cast card_block_le H T i hi1
    rw [Finset.sum_add_distrib] at hlt
    have h1 := abs_add_le (∑ t ∈ Bk i, X t ω ⬝ᵥ I.θ t) (∑ t ∈ Bk i, η t ω)
    have h2 : a < |∑ t ∈ Bk i, η t ω| := by linarith
    simp only [one_mul, neg_one_mul, Finset.sum_neg_distrib]
    rcases lt_abs.1 h2 with h | h
    · left; exact h.le
    · right; exact h.le
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  -- block sizes
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · rw [hK0]; simp
  obtain ⟨K', hK'⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hceil := (Nat.ceil_eq_iff (by omega : K ≠ 0)).1 hK.symm
  rw [hK'] at hceil
  simp only [Nat.add_sub_cancel] at hceil
  have hHpos : (0 : ℝ) < H := by linarith
  have hlow : K' * H < T := by
    have := hceil.1
    rw [lt_div_iff₀ hHpos] at this
    exact_mod_cast this
  have hup : T ≤ (K' + 1) * H := by
    have := hceil.2
    rw [div_le_iff₀ hHpos] at this
    exact_mod_cast this
  have hcard_full : ∀ i ∈ Finset.Icc 1 K', (Bk i).card = H := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    show (Finset.Icc (blockStart H i) (blockEnd H T i)).card = H
    rw [card_block H T i hi.1]
    have e1 : i * H = (i - 1) * H + H := by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp [add_mul]
    have e2 : i * H ≤ K' * H := Nat.mul_le_mul_right _ hi.2
    omega
  have hcard_last : (Bk (K' + 1)).card = T - K' * H := by
    show (Finset.Icc (blockStart H (K' + 1)) (blockEnd H T (K' + 1))).card = T - K' * H
    rw [card_block H T _ (by omega)]
    simp only [Nat.add_sub_cancel]
    omega
  have hBpos : ∀ i ∈ Finset.Icc 1 K, 0 < (Bk i).card := by
    intro i hi
    rw [Finset.mem_Icc, hK'] at hi
    rcases eq_or_lt_of_le hi.2 with h | h
    · rw [h, hcard_last]; omega
    · rw [hcard_full i (Finset.mem_Icc.2 ⟨hi.1, by omega⟩)]; omega
  -- per-block bound
  set g : ℕ → ℝ := fun i => Real.exp (-a ^ 2 / (2 * ((Bk i).card * R ^ 2))) with hg
  have hblock : ∀ i ∈ Finset.Icc 1 K, P ({ω | a ≤ ∑ t ∈ Bk i, (1 : ℝ) * η t ω} ∪
      {ω | a ≤ ∑ t ∈ Bk i, (-1 : ℝ) * η t ω}) ≤ ENNReal.ofReal (2 * g i) := by
    intro i hi
    refine (measure_union_le _ _).trans ?_
    rw [two_mul, ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
    exact add_le_add (tail P η R hη _ (hBpos i hi) a ha0 1 (Or.inl rfl))
      (tail P η R hη _ (hBpos i hi) a ha0 (-1) (Or.inr rfl))
  refine (Finset.sum_le_sum hblock).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum]
  -- the real computation
  have hgexp : ∀ i, (Bk i).card ≠ 0 → g i =
      Real.exp (-(2 * (H : ℝ) * Real.log ((T : ℝ) / Real.sqrt H)) / (Bk i).card) := by
    intro i hi
    have hc : (0 : ℝ) < (Bk i).card := by exact_mod_cast Nat.pos_of_ne_zero hi
    rw [hg]; simp only
    congr 1
    rw [ha2]; field_simp; ring
  have hfull : ∀ i ∈ Finset.Icc 1 K', g i ≤ (H : ℝ) / (T : ℝ) ^ 2 := by
    intro i hi
    rw [hgexp i (by rw [hcard_full i hi]; omega), hcard_full i hi]
    exact real_key H H T hH le_rfl hHT
  have hlast : g (K' + 1) ≤ ((T - K' * H : ℕ) : ℝ) / (T : ℝ) ^ 2 := by
    rw [hgexp _ (by rw [hcard_last]; omega), hcard_last]
    exact real_key H (T - K' * H) T (by omega) (by
      have : T ≤ K' * H + H := by rw [add_mul, one_mul] at hup; exact hup
      omega) hHT
  rw [hK', Finset.sum_Icc_succ_top (by omega)]
  have hsumfull : ∑ i ∈ Finset.Icc 1 K', g i ≤ K' * ((H : ℝ) / (T : ℝ) ^ 2) := by
    calc ∑ i ∈ Finset.Icc 1 K', g i ≤ ∑ i ∈ Finset.Icc 1 K', (H : ℝ) / (T : ℝ) ^ 2 :=
          Finset.sum_le_sum hfull
      _ = K' * ((H : ℝ) / (T : ℝ) ^ 2) := by simp
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
  have hcast : ((T - K' * H : ℕ) : ℝ) = T - K' * H := by
    rw [Nat.cast_sub hlow.le]; push_cast; ring
  rw [hcast] at hlast
  have : (K' : ℝ) * ((H : ℝ) / (T : ℝ) ^ 2) + (T - K' * H) / (T : ℝ) ^ 2 = 1 / T := by
    field_simp; ring
  have h2T : (2 : ℝ) / T = 2 * (1 / T) := by ring
  rw [h2T]
  linarith
