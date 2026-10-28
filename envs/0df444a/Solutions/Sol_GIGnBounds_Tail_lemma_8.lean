-- Prove2me | solution 1 for GIGnBounds.Tail.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:44:49.067317+00:00
-- url     : https://prove2.me/submissions/1bff3f39-859f-407b-b7e2-be1cc11f38cf

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory GIGnBounds.Tail

namespace GIGnRenewAux

/-! ### Real characterisations of `x ≤ sup` in `EReal` -/

lemma le_iSup_iff_real {ι : Sort*} (v : ι → EReal) (x : ℝ) :
    (x : EReal) ≤ iSup v ↔ ∀ y : ℝ, y < x → ∃ i, (y : EReal) < v i := by
  constructor
  · intro h y hy
    exact lt_iSup_iff.mp (lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hy) h)
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨z, hz1, hz2⟩ := EReal.lt_iff_exists_real_btwn.mp hc
    obtain ⟨i, hi⟩ := h z (EReal.coe_lt_coe_iff.mp hz2)
    exact absurd (lt_of_lt_of_le hi (le_iSup v i)) (not_lt.mpr hz1.le)

lemma le_iSup_coe_iff (u : ℕ → ℝ) (x : ℝ) :
    (x : EReal) ≤ ⨆ k, (u k : EReal) ↔ ∀ y : ℝ, y < x → ∃ k, y < u k := by
  rw [le_iSup_iff_real]
  simp only [EReal.coe_lt_coe_iff]

lemma le_supFrom_iff (f : ℝ → ℝ) (x : ℝ) :
    (x : EReal) ≤ supFrom f ↔ ∀ y : ℝ, y < x → ∃ t, 0 ≤ t ∧ y < f t := by
  rw [supFrom, le_iSup_iff_real]
  simp only [lt_iSup_iff, EReal.coe_lt_coe_iff, exists_prop]

/-! ### Partial sums and the ordinary renewal counting function -/

/-- `S_k = s_0 + ⋯ + s_{k-1}`. -/
def S (s : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, s j

lemma S_mono (s : ℕ → ℝ) (hs : ∀ j, 0 ≤ s j) {a b : ℕ} (hab : a ≤ b) : S s a ≤ S s b :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) (fun j _ _ => hs j)

lemma S_nonneg (s : ℕ → ℝ) (hs : ∀ j, 0 ≤ s j) (k : ℕ) : 0 ≤ S s k :=
  Finset.sum_nonneg (fun j _ => hs j)

lemma ordCount_spec (s : ℕ → ℝ) (hs : ∀ j, 0 ≤ s j) (hunb : ∀ B : ℝ, ∃ k, B < S s k)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ n : ℕ, ordCount s t = n ∧ S s n ≤ t ∧ ∀ k, S s k ≤ t → k ≤ n := by
  classical
  have hex : ∃ k, t < S s (k + 1) := by
    obtain ⟨k, hk⟩ := hunb t
    cases k with
    | zero => simp [S] at hk; linarith
    | succ k => exact ⟨k, hk⟩
  set n := Nat.find hex with hn
  have hiff : ∀ k, S s (k + 1) ≤ t ↔ k < n := by
    intro k
    constructor
    · intro hk
      by_contra hkn
      push Not at hkn
      have h1 : t < S s (n + 1) := Nat.find_spec hex
      have h2 : S s (n + 1) ≤ S s (k + 1) := S_mono s hs (by omega)
      linarith
    · intro hk
      have := Nat.find_min hex hk
      push Not at this
      exact this
  refine ⟨n, ?_, ?_, ?_⟩
  · unfold ordCount
    have : Nat.card {k : ℕ // ∑ j ∈ Finset.range (k + 1), s j ≤ t} = Nat.card {k : ℕ // k < n} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun k => hiff k))
    rw [this, ← Nat.card_congr (Fin.equivSubtype (n := n)), Nat.card_eq_fintype_card,
      Fintype.card_fin]
  · rcases Nat.eq_zero_or_eq_succ_pred n with h0 | h1
    · rw [h0]; simpa [S] using ht
    · rw [h1]; exact (hiff _).mpr (by omega)
  · intro k hk
    cases k with
    | zero => exact Nat.zero_le _
    | succ k => exact (hiff k).mp hk

/-- The pathwise identity behind Lemma 8. -/
lemma pathwise (s : ℕ → ℝ) (hs : ∀ j, 0 ≤ s j) (hunb : ∀ B : ℝ, ∃ k, B < S s k)
    (μ ν x : ℝ) (hμ : 0 < μ) (hν : 0 < ν) :
    (x : EReal) ≤ supFrom (fun t => (ordCount s t : ℝ) - μ * t - ν * t) ↔
      ((x * (1 + ν / μ)⁻¹ : ℝ) : EReal) ≤
        ⨆ k : ℕ, ((μ / (μ + ν) * k - ∑ i ∈ Finset.range k, μ * s i : ℝ) : EReal) := by
  rw [le_supFrom_iff, le_iSup_coe_iff]
  have hK : 0 < 1 + ν / μ := by positivity
  have hscale : ∀ k : ℕ, (1 + ν / μ) * (μ / (μ + ν) * k - ∑ i ∈ Finset.range k, μ * s i) =
      k - (μ + ν) * S s k := by
    intro k
    rw [← Finset.mul_sum]
    unfold S
    field_simp
  -- both sides are equivalent to: `∀ y < x, ∃ k, y < k - (μ+ν) S_k`
  have hmid : (∀ y : ℝ, y < x → ∃ t, 0 ≤ t ∧ y < (ordCount s t : ℝ) - μ * t - ν * t) ↔
      ∀ y : ℝ, y < x → ∃ k : ℕ, y < k - (μ + ν) * S s k := by
    constructor
    · intro h y hy
      obtain ⟨t, ht, hyt⟩ := h y hy
      obtain ⟨n, hn, hSn, -⟩ := ordCount_spec s hs hunb t ht
      refine ⟨n, ?_⟩
      rw [hn] at hyt
      nlinarith
    · intro h y hy
      obtain ⟨k, hk⟩ := h y hy
      refine ⟨S s k, S_nonneg s hs k, ?_⟩
      obtain ⟨n, hn, -, hmax⟩ := ordCount_spec s hs hunb (S s k) (S_nonneg s hs k)
      have hkn : (k : ℝ) ≤ n := by exact_mod_cast hmax k le_rfl
      rw [hn]
      nlinarith
  rw [hmid]
  constructor
  · intro h y hy
    have hy' : (1 + ν / μ) * y < x := by
      rwa [lt_mul_inv_iff₀ hK, mul_comm] at hy
    obtain ⟨k, hk⟩ := h _ hy'
    refine ⟨k, ?_⟩
    rw [← hscale k] at hk
    exact lt_of_mul_lt_mul_left hk hK.le
  · intro h y hy
    have hy' : y * (1 + ν / μ)⁻¹ < x * (1 + ν / μ)⁻¹ :=
      mul_lt_mul_of_pos_right hy (inv_pos.mpr hK)
    obtain ⟨k, hk⟩ := h _ hy'
    refine ⟨k, ?_⟩
    rw [← hscale k]
    have := mul_lt_mul_of_pos_left hk hK
    rwa [← mul_assoc, mul_comm (1 + ν / μ) y, mul_assoc, mul_inv_cancel₀ hK.ne', mul_one] at this

/-! ### Almost-sure facts for i.i.d. nonnegative sequences -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

lemma ae_nonneg {X : ℕ → Ω → ℝ} {μ : Measure ℝ} (hX : IsIIDSeq P X μ)
    (h0 : μ (Set.Iio 0) = 0) : ∀ᵐ ω ∂P, ∀ j, 0 ≤ X j ω := by
  rw [ae_all_iff]
  intro i
  have h1 : P (X i ⁻¹' Set.Iio 0) = 0 := by
    rw [← Measure.map_apply (hX.measurable i) measurableSet_Iio, hX.law i, h0]
  rw [ae_iff]
  simpa [Set.preimage, not_le] using h1

lemma exists_delta (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : μ (Set.Iio 0) = 0)
    (hmean : 0 < ∫ x, x ∂μ) : ∃ δ : ℝ, 0 < δ ∧ 0 < μ (Set.Ioi δ) := by
  by_contra hcon
  push Not at hcon
  have hpos : μ (Set.Ioi 0) = 0 := by
    have : Set.Ioi (0 : ℝ) = ⋃ n : ℕ, Set.Ioi (1 / ((n : ℝ) + 1)) := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
        exact ⟨n, hn⟩
      · rintro ⟨n, hn⟩
        exact lt_trans (by positivity) hn
    rw [this]
    exact measure_iUnion_null (fun n => le_antisymm (hcon _ (by positivity)) (by simp))
  have hzero : ∀ᵐ x ∂μ, x = 0 := by
    have hu : μ (Set.Iio 0 ∪ Set.Ioi 0) = 0 := measure_union_null h0 hpos
    rw [ae_iff]
    have : {a : ℝ | ¬ a = 0} = Set.Iio 0 ∪ Set.Ioi 0 := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
      constructor
      · intro h; exact lt_or_gt_of_ne h
      · rintro (h | h) <;> intro h' <;> subst h' <;> exact lt_irrefl _ h
    rw [this]; exact hu
  have : ∫ x, x ∂μ = 0 := by
    rw [integral_congr_ae (hzero.mono (fun x hx => (hx : x = 0)))]
    simp
  linarith

lemma ae_io {X : ℕ → Ω → ℝ} {μ : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (hX : IsIIDSeq P X μ) (δ : ℝ) (hq : 0 < μ (Set.Ioi δ)) :
    ∀ᵐ ω ∂P, ∀ m : ℕ, ∃ j, m ≤ j ∧ δ < X j ω := by
  rw [ae_all_iff]
  intro m
  rw [ae_iff]
  simp only [not_exists, not_and, not_lt]
  set r := μ (Set.Iic δ) with hr
  have hr1 : r < 1 := by
    have : Set.Iic δ = (Set.Ioi δ)ᶜ := by ext; simp
    rw [hr, this, prob_compl_eq_one_sub measurableSet_Ioi]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq.ne'
  have hbound : ∀ n : ℕ, P {ω | ∀ j, m ≤ j → X j ω ≤ δ} ≤ r ^ n := by
    intro n
    calc P {ω | ∀ j, m ≤ j → X j ω ≤ δ}
        ≤ P (⋂ j ∈ Finset.Ico m (m + n), X j ⁻¹' Set.Iic δ) := by
          apply measure_mono
          intro ω hω
          simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Iic, Finset.mem_Ico]
          intro j hj
          exact hω j hj.1
      _ = ∏ j ∈ Finset.Ico m (m + n), P (X j ⁻¹' Set.Iic δ) := by
          apply hX.indep.meas_biInter
          intro j _
          exact ⟨Set.Iic δ, measurableSet_Iic, rfl⟩
      _ = r ^ n := by
          have : ∀ j, P (X j ⁻¹' Set.Iic δ) = r := by
            intro j
            rw [← Measure.map_apply (hX.measurable j) measurableSet_Iic, hX.law j]
          simp [this]
  apply le_antisymm _ (by simp)
  apply ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr1) hbound

lemma unbounded_of_io (s : ℕ → ℝ) (hs : ∀ j, 0 ≤ s j) (δ : ℝ) (hδ : 0 < δ)
    (hio : ∀ m : ℕ, ∃ j, m ≤ j ∧ δ < s j) : ∀ B : ℝ, ∃ k, B < S s k := by
  have hstep : ∀ n : ℕ, ∃ k, (n : ℝ) * δ ≤ S s k := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp [S]⟩
    | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨j, hj, hδj⟩ := hio k
      refine ⟨j + 1, ?_⟩
      have h1 : S s (j + 1) = S s j + s j := by simp [S, Finset.sum_range_succ]
      have h2 : S s k ≤ S s j := S_mono s hs hj
      push_cast
      linarith
  intro B
  obtain ⟨n, hn⟩ := exists_nat_gt (B / δ)
  obtain ⟨k, hk⟩ := hstep n
  refine ⟨k, ?_⟩
  have : B < n * δ := by rwa [div_lt_iff₀ hδ] at hn
  linarith

lemma ae_unbounded {X : ℕ → Ω → ℝ} {μ : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure μ] (hX : IsIIDSeq P X μ) (h0 : μ (Set.Iio 0) = 0)
    (hmean : 0 < ∫ x, x ∂μ) : ∀ᵐ ω ∂P, ∀ B : ℝ, ∃ k, B < S (fun j => X j ω) k := by
  obtain ⟨δ, hδ, hq⟩ := exists_delta μ h0 hmean
  filter_upwards [ae_io hX δ hq, ae_nonneg hX h0] with ω hio hnn
  exact unbounded_of_io _ hnn δ hδ hio

end GIGnRenewAux

open GIGnRenewAux in
theorem solution (μA : Measure ℝ) [IsProbabilityMeasure μA] (hA : IsTimeLaw μA)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : IsIIDSeq P X μA) (ν x : ℝ) (hν : 0 < ν) (_hx : 0 < x) :
    P.real {ω | (x : EReal) ≤
        supFrom (fun t => (ordCount (fun j => X j ω) t : ℝ) - rate μA * t - ν * t)} =
      P.real {ω | ((x * (1 + ν / rate μA)⁻¹ : ℝ) : EReal) ≤
        ⨆ k : ℕ, ((rate μA / (rate μA + ν) * k - ∑ i ∈ Finset.range k, rate μA * X i ω : ℝ) : EReal)} := by
  have hrate : 0 < rate μA := inv_pos.mpr hA.mean_pos
  apply measureReal_congr
  filter_upwards [ae_nonneg hX hA.nonneg, ae_unbounded hX hA.nonneg hA.mean_pos] with ω hnn hunb
  exact propext (pathwise (fun j => X j ω) hnn hunb (rate μA) ν x hrate hν)
