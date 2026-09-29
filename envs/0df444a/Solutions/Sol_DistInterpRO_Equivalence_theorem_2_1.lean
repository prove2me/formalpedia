-- Prove2me | solution 1 for DistInterpRO.Equivalence.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:07:42.308888+00:00
-- url     : https://prove2.me/submissions/ebd6e26d-ecf3-45c4-a87d-bb8099471e59

import Mathlib
import Definitions.Def_DistInterpRO_Equivalence_Model

open MeasureTheory


namespace DistInterpRO.Equivalence

theorem carried_core {m n : ℕ} (f : (Fin m → ℝ) → ℝ)
    (c : Fin n → ℝ) (hsum : ∑ i, c i = 1)
    (Z : Fin n → Set (Fin m → ℝ))
    (hZm : ∀ i, MeasurableSet (Z i))
    (μ : Measure (Fin m → ℝ)) (hμ : μ ∈ distSet c Z) :
    μ (⋃ i, Z i)ᶜ = 0 ∧ expect μ f = expect (μ.restrict (⋃ i, Z i)) f := by
  obtain ⟨hP, hS⟩ := hμ
  have h1 := hS Finset.univ
  simp only [Finset.mem_univ, Set.iUnion_true, hsum, ENNReal.ofReal_one] at h1
  have hm : MeasurableSet (⋃ i, Z i) := MeasurableSet.iUnion hZm
  have hc : μ (⋃ i, Z i)ᶜ = 0 := by
    rw [measure_compl hm (measure_ne_top _ _), measure_univ]
    have : μ (⋃ i, Z i) = 1 := le_antisymm prob_le_one h1
    rw [this]; simp
  refine ⟨hc, ?_⟩
  have : μ.restrict (⋃ i, Z i) = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    have : {a | ¬ a ∈ ⋃ i, Z i} = (⋃ i, Z i)ᶜ := rfl
    rw [this]; exact hc
  rw [this]

theorem dual_core {m n : ℕ} (f : (Fin m → ℝ) → ℝ)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (Z : Fin n → Set (Fin m → ℝ)) (hZne : ∀ i, (Z i).Nonempty)
    (α : Finset (Fin n) → ℝ) (hα : IsDualFeasible Z f α) :
    ∑ i, c i * ∑ S : Finset (Fin n), α S * (if i ∈ S then (1 : ℝ) else 0) ≤
      ∑ i, c i * ⨅ x : Z i, f x := by
  classical
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hc i).le
  haveI : Nonempty (Z i) := (hZne i).to_subtype
  apply le_ciInf
  rintro ⟨x, hx⟩
  have hxU : x ∈ ⋃ i, Z i := Set.mem_iUnion.2 ⟨i, hx⟩
  refine le_trans ?_ (hα.1 x hxU)
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : S = Finset.univ
  · subst hS
    simp only [Finset.mem_univ, if_true, Set.iUnion_true, hxU]
    exact le_rfl
  · have h0 := hα.2 S hS
    apply mul_le_mul_of_nonneg_left _ h0
    by_cases hi : i ∈ S
    · have : x ∈ ⋃ j ∈ S, Z j := Set.mem_biUnion hi hx
      simp [hi, this]
    · simp only [hi, if_false]
      split_ifs <;> norm_num


noncomputable def gext {n : ℕ} (fi : Fin n → ℝ) (t : ℕ) : ℝ :=
  if h : t < n then fi ⟨t, h⟩ else 0

lemma nestedDual_eq {n : ℕ} (fi : Fin n → ℝ) (S : Finset (Fin n)) :
    nestedDual fi S = ∑ i : Fin n,
      if S = Finset.Iic i then gext fi i.val - gext fi (i.val + 1) else 0 := by
  unfold nestedDual gext
  apply Finset.sum_congr rfl
  intro i _
  simp [i.isLt]

lemma nestedDual_swap {n : ℕ} (fi : Fin n → ℝ) (w : Finset (Fin n) → ℝ) :
    ∑ S : Finset (Fin n), nestedDual fi S * w S =
      ∑ i : Fin n, (gext fi i.val - gext fi (i.val + 1)) * w (Finset.Iic i) := by
  simp_rw [nestedDual_eq, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

lemma tele_nat (g : ℕ → ℝ) (k : ℕ) : ∀ N, k ≤ N →
    ∑ t ∈ Finset.range N, (g t - g (t + 1)) * (if k ≤ t then (1:ℝ) else 0) = g k - g N := by
  intro N hN
  induction N with
  | zero =>
    have : k = 0 := by omega
    subst this; simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge N k with h | h
    · have hk : k = N + 1 := by omega
      subst hk
      have : ∀ t ∈ Finset.range N, (g t - g (t + 1)) * (if N + 1 ≤ t then (1:ℝ) else 0) = 0 := by
        intro t ht
        simp at ht
        have : ¬ (N + 1 ≤ t) := by omega
        simp [this]
      rw [Finset.sum_eq_zero this]
      simp
    · rw [ih h]
      simp [h]

lemma tele_fin {n : ℕ} (fi : Fin n → ℝ) (k : Fin n) :
    ∑ i : Fin n, (gext fi i.val - gext fi (i.val + 1)) * (if k ≤ i then (1:ℝ) else 0) = fi k := by
  have := tele_nat (gext fi) k.val n k.isLt.le
  rw [Finset.sum_range (fun t => (gext fi t - gext fi (t + 1)) *
    (if k.val ≤ t then (1:ℝ) else 0))] at this
  simp only [Fin.le_iff_val_le_val]
  rw [this]
  simp [gext, k.isLt]

theorem nested_core {m n : ℕ} (f : (Fin m → ℝ) → ℝ)
    (c : Fin n → ℝ)
    (Z : Fin n → Set (Fin m → ℝ))
    (hbdd : ∀ i, BddBelow (f '' Z i))
    (hsorted : Antitone (fun i : Fin n => ⨅ x : Z i, f x)) :
    IsDualFeasible Z f (nestedDual (fun i => ⨅ x : Z i, f x)) ∧
      (∀ i : Fin n, ∑ S : Finset (Fin n),
          nestedDual (fun j => ⨅ x : Z j, f x) S * (if i ∈ S then (1 : ℝ) else 0) =
            ⨅ x : Z i, f x) ∧
      ∑ i, c i * ∑ S : Finset (Fin n),
          nestedDual (fun j => ⨅ x : Z j, f x) S * (if i ∈ S then (1 : ℝ) else 0) =
        ∑ i, c i * ⨅ x : Z i, f x := by
  classical
  set fi : Fin n → ℝ := fun i => ⨅ x : Z i, f x with hfi
  have P2 : ∀ i : Fin n, ∑ S : Finset (Fin n),
      nestedDual fi S * (if i ∈ S then (1 : ℝ) else 0) = fi i := by
    intro i
    rw [nestedDual_swap]
    simp only [Finset.mem_Iic]
    exact tele_fin fi i
  refine ⟨⟨?_, ?_⟩, P2, ?_⟩
  · intro x hx
    have hne : (Finset.univ.filter (fun j => x ∈ Z j)).Nonempty := by
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
      exact ⟨j, by simp [hj]⟩
    set k := (Finset.univ.filter (fun j => x ∈ Z j)).min' hne with hk
    have hkmem : x ∈ Z k := by
      have := Finset.min'_mem _ hne
      rw [← hk] at this
      simpa using this
    have hiff : ∀ j : Fin n, (x ∈ ⋃ l ∈ Finset.Iic j, Z l) ↔ k ≤ j := by
      intro j
      simp only [Set.mem_iUnion, Finset.mem_Iic, exists_prop]
      constructor
      · rintro ⟨l, hl, hxl⟩
        have : k ≤ l := Finset.min'_le _ _ (by simp [hxl])
        exact le_trans this hl
      · intro h; exact ⟨k, h, hkmem⟩
    rw [nestedDual_swap]
    simp only [hiff]
    rw [tele_fin fi k]
    have hb : BddBelow (Set.range fun y : Z k => f y) := by
      rw [← Set.image_eq_range]; exact hbdd k
    exact ciInf_le hb ⟨x, hkmem⟩
  · intro S hS
    rw [nestedDual_eq]
    apply Finset.sum_nonneg
    intro i _
    split_ifs with h
    · by_cases hi : i.val + 1 < n
      · have e1 : gext fi i.val = fi i := by simp [gext, i.isLt]
        have e2 : gext fi (i.val + 1) = fi ⟨i.val + 1, hi⟩ := by simp [gext, hi]
        rw [e1, e2, sub_nonneg]
        apply hsorted
        rw [Fin.le_iff_val_le_val]; simp
      · exfalso; apply hS
        rw [h]
        ext j
        simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
        rw [Fin.le_iff_val_le_val]; omega
    · exact le_rfl
  · apply Finset.sum_congr rfl
    intro i _
    rw [P2 i]


lemma expect_integrable {m : ℕ} (μ : Measure (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ)
    (hg : Integrable g μ) : expect μ g = ((∫ x, g x ∂μ : ℝ) : EReal) := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
  have h1 := hg.lintegral_lt_top
  have h2 := hg.neg.lintegral_lt_top
  unfold expect
  rw [EReal.coe_sub, EReal.coe_ennreal_toReal h1.ne, EReal.coe_ennreal_toReal]
  simpa using h2.ne

lemma expect_mono_ae {m : ℕ} (μ : Measure (Fin m → ℝ)) (g f : (Fin m → ℝ) → ℝ)
    (h : ∀ᵐ x ∂μ, g x ≤ f x) : expect μ g ≤ expect μ f := by
  unfold expect
  apply EReal.sub_le_sub
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.2
      (lintegral_mono_ae (h.mono fun x hx => ENNReal.ofReal_le_ofReal hx))
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.2
      (lintegral_mono_ae (h.mono fun x hx => ENNReal.ofReal_le_ofReal (by linarith)))

noncomputable def diracMix {m n : ℕ} (c : Fin n → ℝ) (x : Fin n → Fin m → ℝ) :
    Measure (Fin m → ℝ) :=
  ∑ i, ENNReal.ofReal (c i) • Measure.dirac (x i)

lemma diracMix_mem {m n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (hsum : ∑ i, c i = 1)
    (Z : Fin n → Set (Fin m → ℝ)) (x : Fin n → Fin m → ℝ) (hx : ∀ i, x i ∈ Z i) :
    diracMix c x ∈ distSet c Z := by
  classical
  have happ : ∀ s, diracMix c x s = ∑ i, ENNReal.ofReal (c i) * Measure.dirac (x i) s := by
    intro s
    simp [diracMix]
  refine ⟨⟨?_⟩, ?_⟩
  · rw [happ]
    simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hc i).le), hsum, ENNReal.ofReal_one]
  · intro S
    rw [happ, ENNReal.ofReal_sum_of_nonneg (fun i _ => (hc i).le)]
    calc ∑ i ∈ S, ENNReal.ofReal (c i)
        = ∑ i ∈ S, ENNReal.ofReal (c i) * Measure.dirac (x i) (⋃ i ∈ S, Z i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Measure.dirac_apply_of_mem (by simp only [Set.mem_iUnion]; exact ⟨i, hi, hx i⟩ :
            x i ∈ ⋃ j ∈ S, Z j), mul_one]
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma diracMix_expect {m n : ℕ} (f : (Fin m → ℝ) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (x : Fin n → Fin m → ℝ) :
    expect (diracMix c x) f = ((∑ i, c i * f (x i) : ℝ) : EReal) := by
  have hint : ∀ i, Integrable f (Measure.dirac (x i)) := fun i =>
    integrable_dirac' hf.stronglyMeasurable (by simp)
  have hint2 : Integrable f (diracMix c x) := by
    unfold diracMix
    rw [integrable_finsetSum_measure]
    intro i _
    exact (hint i).smul_measure ENNReal.ofReal_ne_top
  rw [expect_integrable _ _ hint2]
  congr 1
  unfold diracMix
  rw [integral_finsetSum_measure (fun i _ => (hint i).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure, integral_dirac' _ _ hf.stronglyMeasurable,
    ENNReal.toReal_ofReal (hc i).le, smul_eq_mul]


theorem lower_core {m n : ℕ} (f : (Fin m → ℝ) → ℝ)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (hsum : ∑ i, c i = 1)
    (Z : Fin n → Set (Fin m → ℝ))
    (hZm : ∀ i, MeasurableSet (Z i))
    (hbdd : ∀ i, BddBelow (f '' Z i))
    (μ : Measure (Fin m → ℝ)) (hμ : μ ∈ distSet c Z) :
    ((∑ i, c i * ⨅ x : Z i, f x : ℝ) : EReal) ≤ expect μ f := by
  classical
  haveI : IsProbabilityMeasure μ := hμ.1
  set r : Fin n → ℝ := fun i => ⨅ x : Z i, f x with hr
  set σ := Tuple.sort (fun i => -r i) with hσ
  have hmono := Tuple.monotone_sort (fun i => -r i)
  have hanti : Antitone (fun i : Fin n => ⨅ x : Z (σ i), f x) := by
    intro a b hab
    have := hmono hab
    simp only [Function.comp, neg_le_neg_iff] at this
    exact this
  obtain ⟨hfeas, -, hval⟩ := nested_core f (fun i => c (σ i)) (fun i => Z (σ i))
    (fun i => hbdd (σ i)) hanti
  set α := nestedDual (fun j => ⨅ x : Z (σ j), f x) with hα
  set U : Finset (Fin n) → Set (Fin m → ℝ) := fun S => ⋃ i ∈ S, Z (σ i) with hU
  have hUm : ∀ S, MeasurableSet (U S) := fun S =>
    Finset.measurableSet_biUnion S (fun i _ => hZm _)
  set h : (Fin m → ℝ) → ℝ := fun x => ∑ S, α S * (U S).indicator 1 x with hh
  have hint : Integrable h μ := by
    apply integrable_finset_sum
    intro S _
    exact ((integrable_const (1:ℝ)).indicator (hUm S)).const_mul (α S)
  have hcarr := (carried_core f c hsum Z hZm μ hμ).1
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ i, Z i := by
    rw [ae_iff]
    have : {a | ¬ a ∈ ⋃ i, Z i} = (⋃ i, Z i)ᶜ := rfl
    rw [this]; exact hcarr
  have hle : ∀ᵐ x ∂μ, h x ≤ f x := by
    filter_upwards [hae] with x hx
    have hx' : x ∈ ⋃ i, Z (σ i) := by
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
      exact Set.mem_iUnion.2 ⟨σ.symm j, by simpa using hj⟩
    have := hfeas.1 x hx'
    simpa [hh, Set.indicator_apply, U] using this
  have hcons : ∀ S : Finset (Fin n), ∑ i ∈ S, c (σ i) ≤ μ.real (U S) := by
    intro S
    have h0 := hμ.2 (S.image σ)
    rw [Finset.set_biUnion_finset_image, Finset.sum_image (fun a _ b _ hab => σ.injective hab)] at h0
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h0
  have hint_eq : ∫ x, h x ∂μ = ∑ S, α S * μ.real (U S) := by
    rw [hh, integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro S _
      rw [integral_const_mul, integral_indicator_one (hUm S)]
    · intro S _
      exact ((integrable_const (1:ℝ)).indicator (hUm S)).const_mul (α S)
  have hbound : ∑ S, α S * ∑ i ∈ S, c (σ i) ≤ ∑ S, α S * μ.real (U S) := by
    apply Finset.sum_le_sum
    intro S _
    by_cases hS : S = Finset.univ
    · have e1 : ∑ i ∈ S, c (σ i) = 1 := by
        rw [hS, Equiv.sum_comp σ c, hsum]
      have e2 : μ.real (U S) = 1 := by
        apply le_antisymm
        · rw [measureReal_def]
          have := prob_le_one (μ := μ) (s := U S)
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
        · rw [← e1]; exact hcons S
      rw [e1, e2]
    · exact mul_le_mul_of_nonneg_left (hcons S) (hfeas.2 S hS)
  have hdual : ∑ S, α S * ∑ i ∈ S, c (σ i) = ∑ i, c i * r i := by
    have e : ∀ S : Finset (Fin n), ∑ i ∈ S, c (σ i) =
        ∑ i, c (σ i) * (if i ∈ S then (1:ℝ) else 0) := by
      intro S
      simp only [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      congr 1
      ext i; simp
    simp_rw [e, Finset.mul_sum]
    rw [Finset.sum_comm]
    have := hval
    simp only [Finset.mul_sum] at this
    rw [← Equiv.sum_comp σ (fun i => c i * r i)]
    rw [← this]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro S _
    ring
  calc ((∑ i, c i * ⨅ x : Z i, f x : ℝ) : EReal)
      ≤ ((∫ x, h x ∂μ : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.2 (by rw [hint_eq, ← hdual]; exact hbound)
    _ = expect μ h := (expect_integrable μ h hint).symm
    _ ≤ expect μ f := expect_mono_ae μ h f hle


lemma einf_coe {m : ℕ} (f : (Fin m → ℝ) → ℝ) (s : Set (Fin m → ℝ)) (hne : s.Nonempty)
    (hb : BddBelow (f '' s)) :
    ⨅ x ∈ s, ((f x : ℝ) : EReal) = ((⨅ x : s, f x : ℝ) : EReal) := by
  haveI : Nonempty s := hne.to_subtype
  have hb' : BddBelow (Set.range fun x : s => f x) := by
    rw [← Set.image_eq_range]; exact hb
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro a ha
    induction a using EReal.rec with
    | bot => exact absurd ha (not_lt_bot)
    | coe t =>
      have : ⨅ x : s, f x < t := EReal.coe_lt_coe_iff.1 ha
      obtain ⟨⟨x, hx⟩, hlt⟩ := exists_lt_of_ciInf_lt this
      exact (iInf₂_le x hx).trans (EReal.coe_le_coe_iff.2 hlt.le)
    | top => exact le_top
  · exact le_iInf₂ fun x hx => EReal.coe_le_coe_iff.2 (ciInf_le hb' ⟨x, hx⟩)

lemma einf_bot {m : ℕ} (f : (Fin m → ℝ) → ℝ) (s : Set (Fin m → ℝ))
    (hb : ¬ BddBelow (f '' s)) :
    ⨅ x ∈ s, ((f x : ℝ) : EReal) = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro y
  obtain ⟨_, ⟨z, hz, rfl⟩, hlt⟩ := (not_bddBelow_iff.1 hb) y
  exact lt_of_le_of_lt (iInf₂_le z hz) (EReal.coe_lt_coe_iff.2 hlt)

lemma ereal_coe_sum {n : ℕ} (s : Finset (Fin n)) (g : Fin n → ℝ) :
    ((∑ i ∈ s, g i : ℝ) : EReal) = ∑ i ∈ s, (g i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

theorem main_core {m n : ℕ} (f : (Fin m → ℝ) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (hsum : ∑ i, c i = 1)
    (Z : Fin n → Set (Fin m → ℝ)) (hZne : ∀ i, (Z i).Nonempty)
    (hZm : ∀ i, MeasurableSet (Z i)) :
    (∑ i, ((c i : ℝ) : EReal) * ⨅ x ∈ Z i, ((f x : ℝ) : EReal)) =
      ⨅ μ ∈ distSet c Z, expect μ f := by
  classical
  by_cases hB : ∀ i, BddBelow (f '' Z i)
  · have hL : (∑ i, ((c i : ℝ) : EReal) * ⨅ x ∈ Z i, ((f x : ℝ) : EReal)) =
        ((∑ i, c i * ⨅ x : Z i, f x : ℝ) : EReal) := by
      rw [ereal_coe_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [einf_coe f (Z i) (hZne i) (hB i), EReal.coe_mul]
    rw [hL]
    apply le_antisymm
    · exact le_iInf₂ fun μ hμ => lower_core f c hc hsum Z hZm hB μ hμ
    · apply le_of_forall_gt_imp_ge_of_dense
      intro a ha
      induction a using EReal.rec with
      | bot => exact absurd ha (not_lt_bot)
      | top => exact le_top
      | coe t =>
        have hst := EReal.coe_lt_coe_iff.1 ha
        set s := ∑ i, c i * ⨅ x : Z i, f x with hs
        have hε : 0 < t - s := by linarith
        have hex : ∀ i, ∃ x, x ∈ Z i ∧ f x < (⨅ x : Z i, f x) + (t - s) := by
          intro i
          haveI : Nonempty (Z i) := (hZne i).to_subtype
          obtain ⟨⟨x, hx⟩, hlt⟩ := exists_lt_of_ciInf_lt
            (lt_add_of_pos_right (⨅ x : Z i, f x) hε)
          exact ⟨x, hx, hlt⟩
        choose x hx hlt using hex
        calc ⨅ μ ∈ distSet c Z, expect μ f ≤ expect (diracMix c x) f :=
              iInf₂_le _ (diracMix_mem c hc hsum Z x hx)
          _ = ((∑ i, c i * f (x i) : ℝ) : EReal) := diracMix_expect f hf c hc x
          _ ≤ (t : EReal) := by
            apply EReal.coe_le_coe_iff.2
            calc ∑ i, c i * f (x i) ≤ ∑ i, c i * ((⨅ x : Z i, f x) + (t - s)) :=
                  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hlt i).le (hc i).le
              _ = s + (t - s) * ∑ i, c i := by
                  rw [hs, Finset.mul_sum, ← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl; intro i _; ring
              _ = t := by rw [hsum]; ring
  · push_neg at hB
    obtain ⟨i₀, hi₀⟩ := hB
    have hL : (∑ i, ((c i : ℝ) : EReal) * ⨅ x ∈ Z i, ((f x : ℝ) : EReal)) = ⊥ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), einf_bot f _ hi₀,
        EReal.coe_mul_bot_of_pos (hc i₀), EReal.bot_add]
    rw [hL, eq_comm, EReal.eq_bot_iff_forall_lt]
    intro t
    choose y hy using hZne
    set K := ∑ j, c j * f (y j) with hK
    obtain ⟨_, ⟨z, hz, rfl⟩, hlt⟩ :=
      (not_bddBelow_iff.1 hi₀) ((t - 1 - K + c i₀ * f (y i₀)) / c i₀)
    set x := Function.update y i₀ z with hxdef
    have hx : ∀ j, x j ∈ Z j := by
      intro j
      by_cases hj : j = i₀
      · subst hj; simp [hxdef, hz]
      · simp [hxdef, hj, hy j]
    have hsumx : ∑ j, c j * f (x j) = K - c i₀ * f (y i₀) + c i₀ * f z := by
      have e : ∀ j, c j * f (x j) = c j * f (y j) +
          (if j = i₀ then c i₀ * f z - c i₀ * f (y i₀) else 0) := by
        intro j
        by_cases hj : j = i₀
        · subst hj; simp [hxdef]
        · simp [hxdef, hj]
      rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]
      rw [← hK]; ring
    have hlt2 : c i₀ * f z < t - 1 - K + c i₀ * f (y i₀) := by
      have := (lt_div_iff₀ (hc i₀)).1 hlt
      linarith
    calc ⨅ μ ∈ distSet c Z, expect μ f ≤ expect (diracMix c x) f :=
          iInf₂_le _ (diracMix_mem c hc hsum Z x hx)
      _ = ((∑ j, c j * f (x j) : ℝ) : EReal) := diracMix_expect f hf c hc x
      _ < (t : EReal) := by
        apply EReal.coe_lt_coe_iff.2
        rw [hsumx]; linarith

end DistInterpRO.Equivalence

open DistInterpRO.Equivalence


theorem solution {m n : ℕ} (f : (Fin m → ℝ) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (hsum : ∑ i, c i = 1)
    (Z : Fin n → Set (Fin m → ℝ)) (hZne : ∀ i, (Z i).Nonempty)
    (hZm : ∀ i, MeasurableSet (Z i)) :
    (∑ i, ((c i : ℝ) : EReal) * ⨅ x ∈ Z i, ((f x : ℝ) : EReal)) =
      ⨅ μ ∈ distSet c Z, expect μ f := by
  exact main_core f hf c hc hsum Z hZne hZm
