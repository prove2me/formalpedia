-- Prove2me | solution 1 for FiniteEnergyPlane.hasLoopWind_unique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T22:37:34.724982+00:00
-- url     : https://prove2.me/submissions/df530ec6-c835-403b-a792-459865d5a26b

import Definitions.Def_FiniteEnergyPlane_Winding



namespace FiniteEnergyPlane

open scoped Real

theorem hasLoopWind_unique_aux {f : ℝ → ℂ} {k k' : ℤ} (h : HasLoopWind f k)
    (h' : HasLoopWind f k') : k = k' := by
  obtain ⟨-, -, hf0, θ, hθc, hθ, hθk⟩ := h
  obtain ⟨-, -, -, θ', hθc', hθ', hθk'⟩ := h'
  have hpi := Real.pi_pos
  -- `θ - θ'` takes values in `2πℤ`
  have hint : ∀ t, ∃ n : ℤ, θ t - θ' t = 2 * π * n := by
    intro t
    have hn : (‖f t‖ : ℂ) ≠ 0 := by simpa using hf0 t
    have he : Complex.exp ((θ t : ℂ) * Complex.I) = Complex.exp ((θ' t : ℂ) * Complex.I) :=
      mul_left_cancel₀ hn ((hθ t).symm.trans (hθ' t))
    have he1 : Complex.exp (((θ t - θ' t : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, he, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 he1
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    linarith
  set g : ℝ → ℝ := fun t => (θ t - θ' t) / (2 * π) with hg
  have hgc : Continuous g := (hθc.sub hθc').div_const _
  have hgint : ∀ t, ∃ n : ℤ, g t = n := by
    intro t
    obtain ⟨n, hn⟩ := hint t
    refine ⟨n, ?_⟩
    simp only [hg, hn]
    field_simp
  obtain ⟨n₀, hn₀⟩ := hgint 0
  obtain ⟨n₁, hn₁⟩ := hgint 1
  have hcont : ContinuousOn g (Set.Icc 0 1) := hgc.continuousOn
  have heq : n₀ = n₁ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmem : (n₀ : ℝ) + 1 / 2 ∈ Set.Icc (g 0) (g 1) := by
        rw [hn₀, hn₁]
        have : (n₀ : ℝ) + 1 ≤ n₁ := by exact_mod_cast hlt
        constructor <;> linarith
      obtain ⟨t, -, ht⟩ := intermediate_value_Icc zero_le_one hcont hmem
      obtain ⟨m, hm⟩ := hgint t
      rw [hm] at ht
      have h2 : (2 : ℝ) * (m - n₀) = 1 := by linarith
      have h3 : (2 : ℤ) * (m - n₀) = 1 := by exact_mod_cast h2
      omega
    · have hmem : (n₁ : ℝ) + 1 / 2 ∈ Set.Icc (g 1) (g 0) := by
        rw [hn₀, hn₁]
        have : (n₁ : ℝ) + 1 ≤ n₀ := by exact_mod_cast hgt
        constructor <;> linarith
      obtain ⟨t, -, ht⟩ := intermediate_value_Icc' zero_le_one hcont hmem
      obtain ⟨m, hm⟩ := hgint t
      rw [hm] at ht
      have h2 : (2 : ℝ) * (m - n₁) = 1 := by linarith
      have h3 : (2 : ℤ) * (m - n₁) = 1 := by exact_mod_cast h2
      omega
  have e0 : θ 0 - θ' 0 = 2 * π * g 0 := by simp only [hg]; field_simp
  have e1 : θ 1 - θ' 1 = 2 * π * g 1 := by simp only [hg]; field_simp
  have h0 : θ 0 - θ' 0 = θ 1 - θ' 1 := by rw [e0, e1, hn₀, hn₁, heq]
  have h2 : (2 * π) * ((k : ℝ) - k') = 0 := by linarith
  rcases mul_eq_zero.1 h2 with h | h
  · linarith
  · exact_mod_cast sub_eq_zero.1 h

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {f : ℝ → ℂ} {k k' : ℤ} (h : HasLoopWind f k)
    (h' : HasLoopWind f k') : k = k' :=
  hasLoopWind_unique_aux h h'
