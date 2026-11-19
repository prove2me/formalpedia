-- Prove2me | solution 1 for DiazModulus.fischler_theorem_6_4_two
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:19:02.439685+00:00
-- url     : https://prove2.me/submissions/2c6df416-79dc-4820-ad5f-6d17ff2a663d

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fischler_power_span_finrank
import Theorems.Thm_DiazModulus_fischler_rational_hull
import Theorems.Thm_DiazModulus_qbar_linearIndependent_complex

open Complex ComplexConjugate

/-! # Fischler 2001, Theorem 6.4 (2)

Suppose every product `vᵢvⱼ` lies in `ℒ̃` and `m ≥ 2`. Then the `Q̄`-span of `v₁, …, v_m` has dimension at most
`2`. Write `v = Σₐ cₐwₐ` with complex `cₐ` and `Q̄`-free algebraic vectors `wₐ`, the number of terms being that
dimension; we need two algebraic, `ℂ`-free vectors whose `ℂ`-span contains `v`. With `0` terms, `v = 0` and the
first two unit vectors work. With `1` term, `v = c₀w₀` with `w₀ ≠ 0`; pick `i₀` with `w₀,i₀ ≠ 0` and `j ≠ i₀`
(possible as `m ≥ 2`); then `w₀` and the unit vector `e_j` are `ℂ`-free (a relation `sw₀ + te_j = 0` read at
`i₀` gives `s = 0`, then at `j` gives `t = 0`) and their span contains `v`. With `2` terms, `w₀, w₁` are
algebraic and `Q̄`-free, hence `ℂ`-free, and `v = c₀w₀ + c₁w₁` lies in their span. -/

open DiazModulus in
theorem solution {m : ℕ} (hm : 2 ≤ m) (v : Fin m → ℂ)
    (hv : ∀ I : Fin 2 → Fin m, ∏ t, v (I t) ∈ LogAlgTilde) :
    ∃ w : Fin 2 → Fin m → ℂ, (∀ a i, w a i ∈ Qbar) ∧ LinearIndependent ℂ w ∧
      v ∈ Submodule.span ℂ (Set.range w) := by
  classical
  have hn := (DiazModulus.fischler_power_span_finrank le_rfl v hv).1
  obtain ⟨n, c, w, hn', -, hw, hwQ, hvw, -⟩ := DiazModulus.fischler_rational_hull v
  rw [← hn'] at hn
  have hsingle : ∀ (j : Fin m) (i : Fin m), (Pi.single j (1 : ℂ) : Fin m → ℂ) i ∈ Qbar := by
    intro j i
    rw [Pi.single_apply]
    split_ifs
    · exact Qbar.one_mem
    · exact Qbar.zero_mem
  interval_cases n
  · refine ⟨fun a => Pi.single (Fin.castLE hm a) 1, fun a i => hsingle _ i, ?_, ?_⟩
    · have := (Pi.basisFun ℂ (Fin m)).linearIndependent.comp _ (Fin.castLE_injective hm)
      simpa [Function.comp_def] using this
    · have hv0 : v = 0 := by simpa using hvw
      rw [hv0]; exact zero_mem _
  · have hv1 : v = c 0 • w 0 := by simpa using hvw
    obtain ⟨i₀, hi₀⟩ : ∃ i, w 0 i ≠ 0 := by
      by_contra h; push Not at h; exact hw.ne_zero 0 (funext h)
    obtain ⟨j, hj⟩ : ∃ j : Fin m, j ≠ i₀ := by
      by_cases h : i₀ = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by rw [h]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, by omega⟩, Ne.symm h⟩
    refine ⟨![w 0, Pi.single j 1], fun a i => ?_, ?_, ?_⟩
    · fin_cases a
      · exact hwQ 0 i
      · exact hsingle j i
    · rw [LinearIndependent.pair_iff]
      intro s t hst
      have h₀ := congr_fun hst i₀
      simp [hj.symm] at h₀
      have hs : s = 0 := by
        rcases h₀ with h | h
        · exact h
        · exact absurd h hi₀
      subst hs
      have h₁ := congr_fun hst j
      simpa using h₁
    · rw [hv1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  · refine ⟨w, hwQ, DiazModulus.qbar_linearIndependent_complex w hwQ hw, ?_⟩
    rw [hvw]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
