-- Prove2me | solution 1 for DiazModulus.fv_cor_1_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:19:05.317088+00:00
-- url     : https://prove2.me/submissions/31ad5e0e-78a3-4df4-954b-3e08b15acd7d

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_strong_six_exponentials_unconditional

open Complex ComplexConjugate

/-! # Fischler–Viola, Cor. 1.3

Suppose both `Λ₁Λ₂` and `Λ₁Λ₃` lie in `ℒ̃`. Put `x = (1, Λ₁)` and `y = (1, Λ₂, Λ₃)`. The six products `xᵢyⱼ`
are `1, Λ₂, Λ₃, Λ₁, Λ₁Λ₂, Λ₁Λ₃`, all in `ℒ̃` (`1 ∈ ℒ̃` by definition of `ℒ̃`). The triple `y` is `Q̄`-free by
hypothesis. The pair `x` is `Q̄`-free: a relation `s + tΛ₁ = 0` with `t ≠ 0` would give `Λ₁ = −s/t ∈ Q̄`,
against the transcendence of `Λ₁`, and `t = 0` forces `s = 0`. Roy's strong six exponentials theorem, in product
form, says that a `Q̄`-free pair and a `Q̄`-free triple never have all six products in `ℒ̃`: contradiction. -/

open DiazModulus in
theorem solution (Λ₁ Λ₂ Λ₃ : ℂ) (h₁ : Λ₁ ∈ LogAlgTilde) (h₂ : Λ₂ ∈ LogAlgTilde)
    (h₃ : Λ₃ ∈ LogAlgTilde) (htr : Transcendental ℚ Λ₁)
    (hfree : LinearIndependent (↥Qbar) ![1, Λ₂, Λ₃]) :
    Λ₁ * Λ₂ ∉ LogAlgTilde ∨ Λ₁ * Λ₃ ∉ LogAlgTilde := by
  by_contra h
  push Not at h
  obtain ⟨h12, h13⟩ := h
  have h1 : (1 : ℂ) ∈ LogAlgTilde := Submodule.subset_span (Set.mem_insert 1 _)
  have hx : LinearIndependent (↥Qbar) ![(1 : ℂ), Λ₁] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simpa using hst
    · exfalso
      apply htr
      have hΛ : Λ₁ = -((s : ℂ) / t) := by
        rw [Subfield.smul_def, Subfield.smul_def, smul_eq_mul, smul_eq_mul, mul_one] at hst
        have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
        field_simp
        linear_combination hst
      rw [hΛ, ← mem_Qbar_iff]
      exact Qbar.neg_mem (Qbar.div_mem s.2 t.2)
  refine DiazModulus.strong_six_exponentials_unconditional ![1, Λ₁] ![1, Λ₂, Λ₃] hx hfree fun i j => ?_
  fin_cases i <;> fin_cases j <;> simpa
