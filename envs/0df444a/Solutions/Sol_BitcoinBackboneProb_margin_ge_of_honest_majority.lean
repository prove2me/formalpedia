-- Prove2me | solution 1 for BitcoinBackboneProb.margin_ge_of_honest_majority
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T00:33:57.127709+00:00
-- url     : https://prove2.me/submissions/ace5ba9c-0c12-40a9-b1ad-c6a1e3564c05

import Definitions.Def_BitcoinBackboneProb

open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

private theorem integral_pi_prod_ber (m : ℕ) (p : unitInterval) (g : Fin m → Bool → ℝ) :
    ∫ f : Fin m → Bool, ∏ i, g i (f i) ∂(Measure.pi fun _ => ber p) =
      ∏ i, ((p : ℝ) * g i true + (1 - (p : ℝ)) * g i false) := by
  rw [integral_fintype_prod_eq_prod]
  congr 1; ext i
  simp [ber, integral_bernoulliMeasure]

private theorem integral_pi_eval_ber (m : ℕ) (p : unitInterval) (j : Fin m) (g : Bool → ℝ) :
    ∫ f : Fin m → Bool, g (f j) ∂(Measure.pi fun _ => ber p) =
      (p : ℝ) * g true + (1 - (p : ℝ)) * g false := by
  have h := integral_pi_prod_ber m p (fun i b => if i = j then g b else 1)
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true] at h
  rw [h]
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

private theorem honestCount_eq_zero_iff {n t : ℕ} (ρ : Round n t) :
    honestCount ρ = 0 ↔ ∀ i, ρ.1 i = false := by
  simp [honestCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

private theorem honestCount_eq_one_iff {n t : ℕ} (ρ : Round n t) (i : Fin n) :
    (∀ j, ρ.1 j = decide (j = i)) → honestCount ρ = 1 := by
  intro h
  unfold honestCount
  rw [Finset.card_eq_one]
  exact ⟨i, by ext j; simp [h j]⟩

private theorem roundY_real_eq {n t : ℕ} (ρ : Round n t) :
    (roundY ρ : ℝ) = ∑ i, ∏ j, (if ρ.1 j = decide (j = i) then (1 : ℝ) else 0) := by
  simp only [Finset.prod_boole, Finset.mem_univ, true_implies]
  rw [Finset.sum_boole]
  unfold roundY
  by_cases h : honestCount ρ = 1
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h
    have hf : ∀ j, ρ.1 j = decide (j = a) := by
      intro j
      have := congrArg (fun s => j ∈ s) ha
      simp at this
      cases hj : ρ.1 j <;> simp_all
    have : (Finset.univ.filter fun i => ∀ j, ρ.1 j = decide (j = i)) = {a} := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hi; have := (hi a).symm.trans (hf a); simpa [eq_comm] using this
      · rintro rfl; exact hf
    simp [h, this]
  · have : (Finset.univ.filter fun i => ∀ j, ρ.1 j = decide (j = i)) = ∅ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hi; exact h (honestCount_eq_one_iff ρ i hi)
    simp [h, this]

private theorem roundX_real_eq {n t : ℕ} (ρ : Round n t) :
    (roundX ρ : ℝ) = 1 - ∏ i, (if ρ.1 i = false then (1 : ℝ) else 0) := by
  rw [Finset.prod_boole]
  unfold roundX
  have := honestCount_eq_zero_iff ρ
  by_cases h : honestCount ρ = 0
  · simp [h, this.1 h]
  · have h' : ¬ ∀ i, ρ.1 i = false := fun h'' => h (this.2 h'')
    simp [Nat.pos_of_ne_zero h, h']

private theorem advCount_real_eq {n t : ℕ} (ρ : Round n t) :
    (advCount ρ : ℝ) = ∑ j, (if ρ.2 j = true then (1 : ℝ) else 0) := by
  simp [advCount, Finset.sum_boole]

private theorem integral_round_fst (n t : ℕ) (p : unitInterval) (g : (Fin n → Bool) → ℝ) :
    ∫ ρ, g ρ.1 ∂(roundMeasure n t p) = ∫ f, g f ∂(Measure.pi fun _ => ber p) := by
  unfold roundMeasure
  rw [integral_fun_fst]; simp

private theorem integral_round_snd (n t : ℕ) (p : unitInterval) (g : (Fin t → Bool) → ℝ) :
    ∫ ρ, g ρ.2 ∂(roundMeasure n t p) = ∫ f, g f ∂(Measure.pi fun _ => ber p) := by
  unfold roundMeasure
  rw [integral_fun_snd]; simp

private theorem integral_trace_eval (n t : ℕ) (p : unitInterval) (r : ℕ) (g : Round n t → ℝ) :
    ∫ ω, g (ω r) ∂(P n t p) = ∫ ρ, g ρ ∂(roundMeasure n t p) := by
  unfold P
  conv_rhs => rw [← Measure.infinitePi_map_eval (fun _ : ℕ => roundMeasure n t p) r]
  rw [integral_map (measurable_pi_apply r).aemeasurable (Measurable.of_discrete.aestronglyMeasurable)]

/-- Honest majority with a gap: if `t ≤ (1 - δ) n` and `p n ≤ δ / 2`, then the margin is at least
`δ p n / 2` (using Bernoulli's inequality `(1 - p)^(n-1) ≥ 1 - (n - 1) p`). -/
theorem solution (n t : ℕ) (p : unitInterval) (δ : ℝ)
    (ht : (t : ℝ) ≤ (1 - δ) * n) (hp : (n : ℝ) * p ≤ δ / 2) :
    δ * p * n / 2 ≤ margin n t p := by
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbern : 1 + ((n - 1 : ℕ) : ℝ) * (-(p : ℝ)) ≤ (1 + -(p : ℝ)) ^ (n - 1) :=
    one_add_mul_le_pow (by linarith) _
  have hcast : ((n - 1 : ℕ) : ℝ) ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · rw [Nat.cast_sub h]; simp
  have h1 : 1 - (n : ℝ) * p ≤ (1 - (p : ℝ)) ^ (n - 1) := by
    have : ((n - 1 : ℕ) : ℝ) * p ≤ n * p := mul_le_mul_of_nonneg_right hcast hp0
    simp only [← sub_eq_add_neg] at hbern
    nlinarith
  have hnp : (0 : ℝ) ≤ n * p := mul_nonneg hn hp0
  unfold margin
  have h2 : (n : ℝ) * p * (1 - (n : ℝ) * p) ≤ n * p * (1 - (p : ℝ)) ^ (n - 1) :=
    mul_le_mul_of_nonneg_left h1 hnp
  have h3 : (t : ℝ) * p ≤ (1 - δ) * n * p := mul_le_mul_of_nonneg_right ht hp0
  nlinarith
