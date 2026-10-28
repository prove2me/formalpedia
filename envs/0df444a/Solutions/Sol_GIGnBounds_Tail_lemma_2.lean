-- Prove2me | solution 1 for GIGnBounds.Tail.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:49:27.709169+00:00
-- url     : https://prove2.me/submissions/eb228b1b-9bab-4127-9943-dd28a7cd72a9

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory GIGnBounds.Tail

namespace GIGnRenewAux2

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


lemma eqCount_le (R : ℝ) (hR : 0 ≤ R) (s : ℕ → ℝ) (hs : ∀ j, 0 ≤ s j)
    (hunb : ∀ B : ℝ, ∃ k, B < S s k) (t : ℝ) :
    (eqCount R s t : ℝ) ≤ 1 + ordCount s t := by
  unfold eqCount
  rcases lt_or_ge t 0 with ht | ht
  · have : Nat.card {k : ℕ // R + ∑ j ∈ Finset.range k, s j ≤ t} ≤ Nat.card (Fin 1) := by
      apply Nat.card_le_card_of_injective (fun _ => 0)
      intro a b _
      exfalso
      have := a.2
      have h2 : 0 ≤ ∑ j ∈ Finset.range a.1, s j := Finset.sum_nonneg (fun j _ => hs j)
      linarith
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    have h0 : (0 : ℝ) ≤ ordCount s t := Nat.cast_nonneg _
    have : (Nat.card {k : ℕ // R + ∑ j ∈ Finset.range k, s j ≤ t} : ℝ) ≤ 1 := by exact_mod_cast this
    linarith
  · obtain ⟨n, hn, -, hmax⟩ := ordCount_spec s hs hunb t ht
    have : Nat.card {k : ℕ // R + ∑ j ∈ Finset.range k, s j ≤ t} ≤ Nat.card (Fin (n + 1)) := by
      apply Nat.card_le_card_of_injective
        (fun k => (⟨k.1, Nat.lt_succ_of_le (hmax k.1 (by have := k.2; unfold S; linarith))⟩ :
          Fin (n + 1)))
      intro a b hab
      apply Subtype.ext
      simpa using congrArg Fin.val hab
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    rw [hn]
    have : (Nat.card {k : ℕ // R + ∑ j ∈ Finset.range k, s j ≤ t} : ℝ) ≤ n + 1 := by
      exact_mod_cast this
    linarith

lemma eqLaw_Iio (μ : Measure ℝ) : eqLaw μ (Set.Iio 0) = 0 := by
  unfold eqLaw
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply measurableSet_Iio]
  have : Set.Iio (0 : ℝ) ∩ Set.Ioi 0 = ∅ := by
    ext a; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_empty_iff_false,
      iff_false, not_and, not_lt]; intro h; exact h.le
  rw [this, measure_empty]

end GIGnRenewAux2

open GIGnRenewAux2 in
theorem solution (n : ℕ) (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (hS1 : mean μS = 1) (hstab : rate μA < n)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : RenewalFamily Ω P n μA μS) (x : ℝ) (hx : 2 < x) :
    P.real {ω | (x : EReal) ≤ supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ))} ≤
      P.real {ω | ((1 / 2 * x - 1 : ℝ) : EReal) ≤
          supFrom (fun t => (F.Ao ω t : ℝ) - rate μA * t - 1 / 2 * (n - rate μA) * t)} +
        P.real {ω | ((1 / 2 * x : ℝ) : EReal) ≤
          supFrom (fun t => n * t - ∑ i, (F.Ne i ω t : ℝ) - 1 / 2 * (n - rate μA) * t)} := by
  -- the later arrival intervals form an i.i.d. sequence with law `μA`
  have hinj : Function.Injective (fun j : ℕ => (Sum.inl (some j) : Option ℕ ⊕ (Fin n × Option ℕ))) := by
    intro a b h; simpa using h
  have hiid : IsIIDSeq P (fun j => F.arr (some j)) μA := by
    refine ⟨fun j => F.measurable_arr (some j), ?_, fun j => F.law_arr_some j⟩
    exact F.indep_all.precomp hinj
  have hR : ∀ᵐ ω ∂P, 0 ≤ F.arr none ω := by
    have h1 : P (F.arr none ⁻¹' Set.Iio 0) = 0 := by
      rw [← Measure.map_apply (F.measurable_arr none) measurableSet_Iio, F.law_arr_none,
        eqLaw_Iio]
    rw [ae_iff]
    simpa [Set.preimage, not_le] using h1
  have hgood : ∀ᵐ ω ∂P, ∀ t, (F.Ae ω t : ℝ) ≤ 1 + F.Ao ω t := by
    filter_upwards [hR, ae_nonneg hiid hA.nonneg, ae_unbounded hiid hA.nonneg hA.mean_pos]
      with ω hRω hnn hunb
    intro t
    exact eqCount_le _ hRω _ hnn hunb t
  set E1 := {ω | ((1 / 2 * x - 1 : ℝ) : EReal) ≤
          supFrom (fun t => (F.Ao ω t : ℝ) - rate μA * t - 1 / 2 * (n - rate μA) * t)}
  set E2 := {ω | ((1 / 2 * x : ℝ) : EReal) ≤
          supFrom (fun t => n * t - ∑ i, (F.Ne i ω t : ℝ) - 1 / 2 * (n - rate μA) * t)}
  have hsub : {ω | (x : EReal) ≤ supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ))}
      ≤ᵐ[P] (E1 ∪ E2 : Set Ω) := by
    filter_upwards [hgood] with ω hω
    intro hin
    replace hin : (x : EReal) ≤ supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ)) := hin
    show ω ∈ E1 ∪ E2
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    obtain ⟨h1, h2⟩ := hnot
    replace h1 : ¬ (((1 / 2 * x - 1 : ℝ) : EReal) ≤
          supFrom (fun t => (F.Ao ω t : ℝ) - rate μA * t - 1 / 2 * (n - rate μA) * t)) := h1
    replace h2 : ¬ (((1 / 2 * x : ℝ) : EReal) ≤
          supFrom (fun t => n * t - ∑ i, (F.Ne i ω t : ℝ) - 1 / 2 * (n - rate μA) * t)) := h2
    rw [not_le] at h1 h2
    obtain ⟨z1, hz1a, hz1b⟩ := EReal.lt_iff_exists_real_btwn.mp h1
    obtain ⟨z2, hz2a, hz2b⟩ := EReal.lt_iff_exists_real_btwn.mp h2
    have hz1 : z1 < 1 / 2 * x - 1 := EReal.coe_lt_coe_iff.mp hz1b
    have hz2 : z2 < 1 / 2 * x := EReal.coe_lt_coe_iff.mp hz2b
    obtain ⟨t, ht, hyt⟩ := (le_supFrom_iff _ x).mp hin (z1 + 1 + z2) (by linarith)
    have hg1 : (F.Ao ω t : ℝ) - rate μA * t - 1 / 2 * (n - rate μA) * t < z1 := by
      have := lt_of_le_of_lt (le_iSup₂ (f := fun t (_ : 0 ≤ t) =>
        (((F.Ao ω t : ℝ) - rate μA * t - 1 / 2 * (n - rate μA) * t : ℝ) : EReal)) t ht) hz1a
      exact EReal.coe_lt_coe_iff.mp this
    have hg2 : (n : ℝ) * t - ∑ i, (F.Ne i ω t : ℝ) - 1 / 2 * (n - rate μA) * t < z2 := by
      have := lt_of_le_of_lt (le_iSup₂ (f := fun t (_ : 0 ≤ t) =>
        (((n : ℝ) * t - ∑ i, (F.Ne i ω t : ℝ) - 1 / 2 * (n - rate μA) * t : ℝ) : EReal)) t ht) hz2a
      exact EReal.coe_lt_coe_iff.mp this
    have := hω t
    linarith
  calc _ ≤ P.real (E1 ∪ E2) := by
        rw [measureReal_def, measureReal_def]
        exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ P.real E1 + P.real E2 := measureReal_union_le _ _
