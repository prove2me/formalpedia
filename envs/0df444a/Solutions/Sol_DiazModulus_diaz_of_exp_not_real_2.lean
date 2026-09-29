-- Prove2me | solution 2 for DiazModulus.diaz_of_exp_not_real
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-13T10:45:22.563416+00:00
-- url     : https://prove2.me/submissions/e06fca14-7953-4932-962e-d1669dc1b8a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DiazModulus_diaz_of_exp_not_real_off_axes
import Theorems.Thm_DiazModulus_sixExponentials_cannot_refute_candidate
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate

-- Off the axes this is the off-axes child. On an axis `conj u = ± u`, so the certificate
-- space `span_Q̄ {1, u, conj u}` sits inside `span_Q̄ {1, u}` and has dimension at most 2,
-- while the six-exponentials no-go node, under Hermite–Lindemann, gives it dimension 3.

open DiazModulus in
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      Transcendental ℚ (Complex.exp u) := by
  classical
  intro u hu hmod hexp
  by_cases hax : u.im = 0 ∨ u.re = 0
  · intro halg
    have hc : IsCandidate u := ⟨hu, hmod, halg⟩
    obtain ⟨-, h2, -⟩ := sixExponentials_cannot_refute_candidate u
    obtain ⟨hrank, -⟩ := h2 hc hermite_lindemann_holds
    -- `conj u = ± u`, so the certificate space sits inside `span {1, u}`
    have hcu : conj u = u ∨ conj u = -u := by
      rcases hax with h | h
      · exact Or.inl (Complex.conj_eq_iff_im.mpr h)
      · exact Or.inr (by apply Complex.ext <;> simp [h])
    have hsub : Submodule.span Qbar ({1, u, conj u} : Set ℂ)
        ≤ Submodule.span Qbar (({1, u} : Finset ℂ) : Set ℂ) := by
      rw [Submodule.span_le]
      intro x hx
      have h1 : (1 : ℂ) ∈ Submodule.span Qbar (({1, u} : Finset ℂ) : Set ℂ) :=
        Submodule.subset_span (by simp)
      have hU : u ∈ Submodule.span Qbar (({1, u} : Finset ℂ) : Set ℂ) :=
        Submodule.subset_span (by simp)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact h1
      · exact hU
      · rcases hcu with h | h
        · rw [h]; exact hU
        · rw [h]; exact neg_mem hU
    have hcard : Module.finrank Qbar (Submodule.span Qbar (({1, u} : Finset ℂ) : Set ℂ))
        ≤ (({1, u} : Finset ℂ)).card := finrank_span_finset_le_card _
    have hle := Submodule.finrank_mono (R := Qbar) hsub
    have hc2 : (({1, u} : Finset ℂ)).card ≤ 2 := by
      refine (Finset.card_insert_le _ _).trans ?_
      simp
    omega
  · exact diaz_of_exp_not_real_off_axes u hu hmod hexp hax
