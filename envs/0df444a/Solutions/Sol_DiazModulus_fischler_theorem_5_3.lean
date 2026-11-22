-- Prove2me | solution 1 for DiazModulus.fischler_theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-21T08:58:06.192011+00:00
-- url     : https://prove2.me/submissions/0f28c662-961c-48b7-98e8-1272df6b1180

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fischler_power_span_finrank

open Complex ComplexConjugate

/-! # Fischler 2001, Theorem 5.3, with a vector hyperplane

Conjecture 2 for the set of pure tensors `v ⊗ ⋯ ⊗ v` in `(ℂᵐ)^{⊗k}`, `m, k ≥ 2`, `(k, m) ≠ (2, 2)`, in the
coordinates `x_I = ∏ₜ v(I t)` of the basis `e_I`, which is defined over `Q̄`; the hyperplane found passes through
`0`. Suppose every `x_I` lies in `ℒ̃`. The bound behind Fischler's Theorems 6.2 and 6.4, which follows from Roy's
strong six exponentials theorem, controls the dimension `n` of the `Q̄`-span of
`v₀, …, v_{m−1}`: `n ≤ 2`, and `n ≤ 1` when `k ≥ 3`. In both cases `n < m`, so the `vᵢ` are linearly dependent over
`Q̄`: `Σ βᵢ vᵢ = 0` with algebraic `βᵢ`, not all zero. Fix the index `0` and send `i` to the multi-index
`ι(i) = (i, 0, …, 0)`, an injective map. Put `ψ = Σᵢ βᵢ e_{ι(i)}`. It has algebraic coordinates and is non-zero,
since its coordinate at `ι(i)` is `βᵢ`. Finally `Σ_I ψ_I x_I = Σᵢ βᵢ x_{ι(i)} = Σᵢ βᵢ vᵢ v₀^{k−1} = 0`. -/

open DiazModulus in
theorem solution {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k) (hkm : (k, m) ≠ (2, 2))
    (v : Fin m → ℂ) (hv : ∀ I : Fin k → Fin m, ∏ t, v (I t) ∈ LogAlgTilde) :
    ∃ ψ : (Fin k → Fin m) → ℂ, (∀ I, ψ I ∈ Qbar) ∧ ψ ≠ 0 ∧
      ∑ I, ψ I * ∏ t, v (I t) = 0 := by
  obtain ⟨h2, h3⟩ := DiazModulus.fischler_power_span_finrank hk v hv
  -- the `vᵢ` are dependent over `Q̄`
  have hlt : Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range v)) < m := by
    by_cases hk3 : 3 ≤ k
    · have := h3 hk3; omega
    · have : m ≠ 2 := fun h => hkm (by rw [h]; congr 1; omega)
      omega
  have hdep : ¬ LinearIndependent (↥Qbar) v := fun h => by
    rw [finrank_span_eq_card h, Fintype.card_fin] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hdep
  -- the multi-indices `(i, 0, …, 0)`
  obtain ⟨p, rfl⟩ : ∃ p, k = p + 1 := ⟨k - 1, by omega⟩
  let j₀ : Fin m := ⟨0, by omega⟩
  let ι : Fin m → Fin (p + 1) → Fin m := fun i => Fin.cons i fun _ => j₀
  have hinj : Function.Injective ι := fun a b h => by simpa [ι] using congrFun h 0
  have hprod : ∀ i, ∏ t, v (ι i t) = v i * v j₀ ^ p := fun i => by
    simp [ι, Fin.prod_univ_succ]
  refine ⟨fun I => ∑ i, if ι i = I then (g i : ℂ) else 0, fun I => ?_, fun h => ?_, ?_⟩
  · refine Subfield.sum_mem Qbar fun i _ => ?_
    split_ifs
    · exact (g i).2
    · exact Qbar.zero_mem
  · have := congrFun h (ι i₀)
    simp only [hinj.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply] at this
    exact hi₀ (Subtype.ext this)
  · simp only [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, hprod, ← mul_assoc, ← Finset.sum_mul]
    have hg' : ∑ i, (g i : ℂ) * v i = 0 := by simpa [Subfield.smul_def] using hg
    rw [hg', zero_mul]
