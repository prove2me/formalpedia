-- Prove2me | solution 1 for DROOptimal.Predictor.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:27:34.410448+00:00
-- url     : https://prove2.me/submissions/c2c83b95-ba4b-4067-9145-473a53521085

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Definitions.Def_DROOptimal_Predictor_Problem5
import Theorems.Thm_DROOptimal_Predictor_theorem_3
import Theorems.Thm_DROOptimal_Predictor_eq_10_attained
import Theorems.Thm_DROOptimal_Predictor_eq_15
import Theorems.Thm_DROOptimal_Predictor_theorem_1_lower

open DROOptimal.Predictor

theorem solution {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 < r) :
    StronglyOptimal5 γ r (drPredictor γ r) := by
  refine ⟨theorem_3 X hX γ hγ r hr.le, ?_⟩
  intro chat hfeas x ℙ'₀
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨ℙ₀, h14, hOpt⟩ := eq_10_attained X hX γ hγ r hr.le x ℙ'₀
  set ε := drPredictor γ r x ℙ'₀ - chat x ℙ'₀ with hε
  have hεpos : 0 < ε := by linarith
  obtain ⟨ℙ₂, hpos, hI, hc⟩ := eq_15 X hX γ hγ r hr x ℙ'₀ ℙ₀ h14 hOpt ε hεpos
  -- ℙ'₀ lies in the disappointment set of ĉ at (x, ℙ₂), which is open
  set D := disappointSet γ chat x ℙ₂ with hD
  have hmem : ℙ'₀ ∈ D := by
    show chat x ℙ'₀ < cost γ x ℙ₂
    linarith
  have hopen : IsOpen D := by
    have hc1 : Continuous (fun ℙ' : Δ d => chat x ℙ') :=
      hfeas.1.comp (Continuous.prodMk continuous_const continuous_id)
    exact isOpen_lt hc1 continuous_const
  have hint : ℙ'₀ ∈ interior D := by rwa [hopen.interior_eq]
  -- pick s with I(ℙ'₀, ℙ₂) < s < r
  have hIinf : (⨅ ℙ' ∈ interior D, relEntropy ℙ' ℙ₂) ≤ relEntropy ℙ'₀ ℙ₂ :=
    biInf_le _ hint
  have hlt2 : (⨅ ℙ' ∈ interior D, relEntropy ℙ' ℙ₂) < (r : EReal) := lt_of_le_of_lt hIinf hI
  obtain ⟨s', hs'1, hs'2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt2
  have hs'r : s' < r := by exact_mod_cast hs'2
  set s := (s' + r) / 2
  have hs1 : (⨅ ℙ' ∈ interior D, relEntropy ℙ' ℙ₂) < (s : EReal) :=
    lt_trans hs'1 (by exact_mod_cast (show s' < s by simp only [s]; linarith))
  have hlow := theorem_1_lower ℙ₂ hpos D hopen.measurableSet s hs1
  have hup := hfeas.2 x ℙ₂ ((s + r) / 2) (by simp only [s]; linarith)
  obtain ⟨T, hT⟩ := (hlow.and (hup.and (Filter.eventually_ge_atTop 1))).exists
  obtain ⟨h1, h2, h3⟩ := hT
  have hTpos : (0 : ℝ) < T := by exact_mod_cast h3
  have : Real.exp (-(s * (T : ℝ))) ≤ Real.exp (-((s + r) / 2 * (T : ℝ))) := le_trans h1 h2
  rw [Real.exp_le_exp] at this
  have : s * (T : ℝ) < (s + r) / 2 * T := by
    apply mul_lt_mul_of_pos_right _ hTpos; simp only [s]; linarith
  linarith
