-- Prove2me | solution 1 for BitcoinBackboneProb.iIndepFun_rounds
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T00:33:53.520787+00:00
-- url     : https://prove2.me/submissions/418e9cad-110e-4c7c-9be8-b0ff5685f136

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

/-- The rounds of a trace are independent under `P n t p`. -/
theorem solution (n t : ℕ) (p : unitInterval) :
    ProbabilityTheory.iIndepFun (fun r (ω : Trace n t) => ω r) (P n t p) := by
  exact iIndepFun_infinitePi (X := fun _ ρ => ρ) (fun _ => measurable_id)
