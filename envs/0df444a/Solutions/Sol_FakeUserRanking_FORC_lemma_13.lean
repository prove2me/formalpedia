-- Prove2me | solution 1 for FakeUserRanking.FORC.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T01:27:31.890238+00:00
-- url     : https://prove2.me/submissions/2b89c790-352f-4554-8b8c-0752482a73c0

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (T : ℕ) (X Y : Fin T → Ω → ℝ) (μ : ℝ)
    (hindep : iIndepFun (Sum.elim X Y) ν)
    (hXmeas : ∀ i, Measurable (X i)) (hYmeas : ∀ i, Measurable (Y i))
    (hX01 : ∀ i, ∀ᵐ ω ∂ν, X i ω = 0 ∨ X i ω = 1)
    (hY01 : ∀ i, ∀ᵐ ω ∂ν, Y i ω = 0 ∨ Y i ω = 1)
    (hXmean : ∀ i, ∫ ω, X i ω ∂ν = μ) (hYmean : ∀ i, ∫ ω, Y i ω ∂ν = μ)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (η₁ η₂ : ℕ) (h₁ : η₁ ≤ T) (h₂ : η₂ ≤ T)
    (hη : 0 < (η₁ : ℝ) + η₂ / 2 ^ ℓ) (ε : ℝ) (hε : 0 < ε) :
    ν.real {ω | ε < |(1 / ((η₁ : ℝ) + η₂ / 2 ^ ℓ)) *
        (∑ i ∈ Finset.univ.filter (fun i : Fin T => (i : ℕ) < η₁), X i ω +
          ∑ i ∈ Finset.univ.filter (fun i : Fin T => (i : ℕ) < η₂), Y i ω / 2 ^ ℓ) - μ|}
      ≤ 2 * Real.exp (-2 * ε ^ 2 * ((η₁ : ℝ) + η₂ / 2 ^ ℓ)) := by
  set E : ℝ := (η₁ : ℝ) + η₂ / 2 ^ ℓ with hE
  let c : Fin T ⊕ Fin T → ℝ := Sum.elim (fun i => if (i : ℕ) < η₁ then 1 else 0)
    (fun i => if (i : ℕ) < η₂ then 1 / 2 ^ ℓ else 0)
  let Z : Fin T ⊕ Fin T → Ω → ℝ := Sum.elim X Y
  let W : Fin T ⊕ Fin T → Ω → ℝ := fun k ω => c k * (Z k ω - μ)
  have hZmeas : ∀ k, Measurable (Z k) := by
    intro k; cases k with
    | inl i => exact hXmeas i
    | inr i => exact hYmeas i
  have hZ01 : ∀ k, ∀ᵐ ω ∂ν, Z k ω ∈ Set.Icc (0:ℝ) 1 := by
    intro k
    cases k with
    | inl i => filter_upwards [hX01 i] with ω h; rcases h with h | h <;> simp [Z, h]
    | inr i => filter_upwards [hY01 i] with ω h; rcases h with h | h <;> simp [Z, h]
  have hZmean : ∀ k, ν[Z k] = μ := by
    intro k; cases k with
    | inl i => exact hXmean i
    | inr i => exact hYmean i
  have hWi : iIndepFun W ν :=
    hindep.comp (fun k x => c k * (x - μ)) (fun k => by fun_prop)
  let cc : Fin T ⊕ Fin T → NNReal := fun k => ⟨c k ^ 2, sq_nonneg _⟩
  set q : NNReal := (‖(1:ℝ) - 0‖₊ / 2) ^ 2 with hq
  have hsub : ∀ k, HasSubgaussianMGF (W k) (cc k * q) ν := by
    intro k
    have h := hasSubgaussianMGF_of_mem_Icc (X := Z k) (a := 0) (b := 1) (μ := ν)
      (hZmeas k).aemeasurable (hZ01 k)
    rw [hZmean k] at h
    exact h.const_mul (c k)
  have hsubn : ∀ k, HasSubgaussianMGF (-W k) (cc k * q) ν :=
    fun k => (hsub k).neg
  have hWin : iIndepFun (fun k => -W k) ν :=
    hWi.comp (fun _ x => -x) (fun k => by fun_prop)
  -- sums
  have hcard1 : ((Finset.univ.filter (fun i : Fin T => (i : ℕ) < η₁)).card : ℝ) = η₁ := by
    rw [Fin.card_filter_val_lt, min_eq_right h₁]
  have hcard2 : ((Finset.univ.filter (fun i : Fin T => (i : ℕ) < η₂)).card : ℝ) = η₂ := by
    rw [Fin.card_filter_val_lt, min_eq_right h₂]
  have hkey : ∀ ω, (1 / E) * (∑ i ∈ Finset.univ.filter (fun i : Fin T => (i : ℕ) < η₁), X i ω +
          ∑ i ∈ Finset.univ.filter (fun i : Fin T => (i : ℕ) < η₂), Y i ω / 2 ^ ℓ) - μ
        = (∑ k, W k ω) / E := by
    intro ω
    have hs : ∑ k, W k ω = (∑ i ∈ Finset.univ.filter (fun i : Fin T => (i : ℕ) < η₁), X i ω +
          ∑ i ∈ Finset.univ.filter (fun i : Fin T => (i : ℕ) < η₂), Y i ω / 2 ^ ℓ) - μ * E := by
      simp only [W, Z, c, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      have e1 : ∑ i : Fin T, (if (i:ℕ) < η₁ then (1:ℝ) else 0) * (X i ω - μ)
          = ∑ i ∈ Finset.univ.filter (fun i : Fin T => (i : ℕ) < η₁), X i ω - μ * η₁ := by
        rw [← hcard1, Finset.sum_filter, Finset.card_filter, Nat.cast_sum, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
      have e2 : ∑ i : Fin T, (if (i:ℕ) < η₂ then (1:ℝ) / 2 ^ ℓ else 0) * (Y i ω - μ)
          = ∑ i ∈ Finset.univ.filter (fun i : Fin T => (i : ℕ) < η₂), Y i ω / 2 ^ ℓ
            - μ * (η₂ / 2 ^ ℓ) := by
        rw [← hcard2, Finset.sum_filter, Finset.card_filter, Nat.cast_sum, Finset.sum_div,
          Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp; ring
      rw [e1, e2, hE]; ring
    rw [hs]; field_simp
  have hS : ((∑ k, cc k * q : NNReal) : ℝ)
      = ((η₁ : ℝ) + η₂ / 4 ^ ℓ) / 4 := by
    have hq' : (q : ℝ) = 1 / 4 := by simp [hq]; norm_num
    have hk : ∀ k, ((cc k * q : NNReal) : ℝ) = c k ^ 2 * (1 / 4) := by
      intro k; rw [NNReal.coe_mul, hq']; rfl
    rw [NNReal.coe_sum]
    simp only [hk]
    rw [← Finset.sum_mul, Fintype.sum_sum_type]
    simp only [c, Sum.elim_inl, Sum.elim_inr]
    have e1 : ∑ i : Fin T, (if (i:ℕ) < η₁ then (1:ℝ) else 0) ^ 2 = η₁ := by
      rw [← hcard1, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    have e2 : ∑ i : Fin T, (if (i:ℕ) < η₂ then (1:ℝ) / 2 ^ ℓ else 0) ^ 2 = η₂ / 4 ^ ℓ := by
      rw [← hcard2, Finset.card_filter, Nat.cast_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs
      · rw [div_pow, show (4:ℝ) ^ ℓ = (2 ^ ℓ) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
        simp
      · simp
    rw [e1, e2]; ring
  have h4 : (η₂ : ℝ) / 4 ^ ℓ ≤ η₂ / 2 ^ ℓ := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) ℓ
  have hSpos : 0 < (η₁ : ℝ) + η₂ / 4 ^ ℓ := by
    rcases Nat.eq_zero_or_pos η₁ with h | h
    · subst h
      have : (0:ℝ) < η₂ / 2 ^ ℓ := by simpa [hE] using hη
      have : (0:ℝ) < η₂ := by
        by_contra hc; push Not at hc
        have : (η₂:ℝ) / 2 ^ ℓ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc (by positivity)
        linarith
      simp only [Nat.cast_zero, zero_add]; positivity
    · have : (0:ℝ) < η₁ := by exact_mod_cast h
      positivity
  have hεE : 0 ≤ ε * E := by positivity
  have hexp : Real.exp (-(ε * E) ^ 2 /
      (2 * ((∑ k, cc k * q : NNReal) : ℝ)))
      ≤ Real.exp (-2 * ε ^ 2 * E) := by
    rw [hS]
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ (by positivity)]
    have : (η₁ : ℝ) + η₂ / 4 ^ ℓ ≤ E := by rw [hE]; linarith
    have hε2 : 0 ≤ ε ^ 2 * E := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hε2]
  have h1 := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hWi (s := Finset.univ) (fun k _ => hsub k) hεE
  have h2 := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hWin (s := Finset.univ) (fun k _ => hsubn k) hεE
  have hsubset : {ω | ε < |(1 / E) *
        (∑ i ∈ Finset.univ.filter (fun i : Fin T => (i : ℕ) < η₁), X i ω +
          ∑ i ∈ Finset.univ.filter (fun i : Fin T => (i : ℕ) < η₂), Y i ω / 2 ^ ℓ) - μ|}
      ⊆ {ω | ε * E ≤ ∑ k, W k ω} ∪ {ω | ε * E ≤ ∑ k, (-W k) ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    rw [hkey ω, abs_div, abs_of_pos hη, lt_div_iff₀ hη] at hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, Pi.neg_apply, Finset.sum_neg_distrib]
    rcases le_or_gt 0 (∑ k, W k ω) with h | h
    · left; rw [abs_of_nonneg h] at hω; linarith
    · right; rw [abs_of_neg h] at hω; linarith
  calc _ ≤ ν.real ({ω | ε * E ≤ ∑ k, W k ω} ∪ {ω | ε * E ≤ ∑ k, (-W k) ω}) :=
        measureReal_mono hsubset
    _ ≤ ν.real {ω | ε * E ≤ ∑ k, W k ω} + ν.real {ω | ε * E ≤ ∑ k, (-W k) ω} :=
        measureReal_union_le _ _
    _ ≤ _ := by linarith [h1.trans hexp, h2.trans hexp]
