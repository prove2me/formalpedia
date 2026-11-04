-- Prove2me | solution 1 for GMCPBandit.Regret.lemma_EC_10_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T14:31:09.491448+00:00
-- url     : https://prove2.me/submissions/eb1c625c-457f-4553-99a5-ea706c049107

import Mathlib
import Definitions.Def_GMCPBandit_Regret_Model
import Definitions.Def_GMCPBandit_Regret_Algorithm
import Theorems.Thm_GMCPBandit_Regret_lemma_EC_10_1

open MeasureTheory ProbabilityTheory

open GMCPBandit.Regret in
theorem solution {d K : ℕ} (hK : 2 ≤ K) (𝒳 : Set (Fin d → ℝ)) (ν : Measure ℝ)
    (g : ℝ → ℝ → ℝ) (β : Fin K → Fin d → ℝ) (xmax s Rmax βmin b h σ σ2 σ3 : ℝ)
    (hglm : IsGLMFamily ν g Rmax)
    (hA1 : A1 𝒳 β xmax s Rmax βmin b)
    (hA5 : A5 g Rmax b xmax σ σ2 σ3)
    (hf' : ∀ r ∈ Set.Icc (-Rmax) Rmax, ∀ η : ℝ, |η| ≤ b * xmax →
      |deriv (fun η => negLogDens g r η) η| ≤ σ2)
    (hh : 0 < h)
    (βhat : Fin K → Fin d → ℝ) (hfeas : ∀ k, l1 (βhat k) ≤ b)
    (hclose : ∀ k, l1 (βhat k - β k) ≤
      min (1 / (σ2 * xmax)) (h / (4 * Real.exp 1 * σ2 * Rmax * xmax)))
    (i : Fin K) (x : Fin d → ℝ) (hx : x ∈ optRegion 𝒳 ν g β h i) :
    maxOther ν g βhat x i + h / 2 ≤ meanFn ν g (x ⬝ᵥ βhat i) := by
  obtain ⟨hx𝒳, hxi⟩ := hx
  have hxmax : 0 < xmax := hA1.1
  have hRmax : 0 < Rmax := hA1.2.2.1
  have hσ2 : 0 < σ2 := hA5.2.1
  -- each estimate moves the mean by at most h/4
  have hq : ∀ k, |meanFn ν g (x ⬝ᵥ β k) - meanFn ν g (x ⬝ᵥ βhat k)| ≤ h / 4 := by
    intro k
    have h1 := lemma_EC_10_1 𝒳 ν g β xmax s Rmax βmin b σ σ2 σ3 hglm hA1 hA5 hf' x hx𝒳 k
      (βhat k) (hfeas k)
    set L := l1 (βhat k - β k)
    have hL0 : 0 ≤ L := Finset.sum_nonneg fun j _ => abs_nonneg _
    have ha : 0 < σ2 * xmax := mul_pos hσ2 hxmax
    have hL1 : σ2 * xmax * L ≤ 1 := by
      have := (hclose k).trans (min_le_left _ _)
      rw [le_div_iff₀ ha] at this; linarith
    have hden : 0 < 4 * Real.exp 1 * σ2 * Rmax * xmax := by positivity
    have hL2 : 4 * Real.exp 1 * σ2 * Rmax * xmax * L ≤ h := by
      have := (hclose k).trans (min_le_right _ _)
      rw [le_div_iff₀ hden] at this; linarith
    have he : Real.exp (σ2 * xmax * L) ≤ Real.exp 1 := Real.exp_le_exp.mpr hL1
    have hpos : 0 ≤ Rmax * σ2 * xmax * L := by positivity
    calc _ ≤ Rmax * Real.exp (σ2 * xmax * L) * σ2 * xmax * L := h1
      _ = Real.exp (σ2 * xmax * L) * (Rmax * σ2 * xmax * L) := by ring
      _ ≤ Real.exp 1 * (Rmax * σ2 * xmax * L) := mul_le_mul_of_nonneg_right he hpos
      _ ≤ h / 4 := by nlinarith
  have hne : Nonempty {j : Fin K // j ≠ i} := by
    by_cases h0 : i.val = 0
    · exact ⟨⟨⟨1, by omega⟩, fun e => by simp [Fin.ext_iff] at e; omega⟩⟩
    · exact ⟨⟨⟨0, by omega⟩, fun e => by simp [Fin.ext_iff] at e; omega⟩⟩
  have hi := hq i
  unfold maxOther
  rw [← le_sub_iff_add_le]
  refine ciSup_le fun j => ?_
  have hj := hq j.1
  have hle : meanFn ν g (x ⬝ᵥ β j.1) ≤ maxOther ν g β x i :=
    le_ciSup (f := fun j : {j : Fin K // j ≠ i} => meanFn ν g (x ⬝ᵥ β j.1))
      (Set.finite_range _).bddAbove j
  rw [abs_le] at hi hj
  linarith
