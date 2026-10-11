-- Prove2me | solution 1 for DiazModulus.candidate_real_pencil_not_both_mem_logAlgTilde
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:06:35.376803+00:00
-- url     : https://prove2.me/submissions/6e59697c-7d2f-4a57-9486-90e69f733499

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_conj_stable_real_pencil_space_carries_two_by_three_configuration
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_DiazModulus_logAlg_conj_stable

open Complex ComplexConjugate

/-! # A real `f` and `f/(|u| + λu)` are not both in `ℒ̃` at a candidate

Under Roy's strong six exponentials hypothesis, let `u` be a candidate, `λ ∈ Q̄` with `λ λ̄ = 1`,
and `f` real with `1, u, ū, f, f/(|u| + λu)` linearly independent over `Q̄`. Then `f` and
`f/(|u| + λu)` are not both in `ℒ̃`.

At a candidate `u ≠ 0` and `u ∉ Q̄` by Hermite–Lindemann; `s = |u|` is algebraic, real, and
`s·s = u ū`. Both `u` and `ū` lie in `ℒ` (`logAlg_conj_stable`), so if `f` and `f/(s + λu)` were
in `ℒ̃`, the whole space `Q̄ + Q̄u + Q̄ū + Q̄f + Q̄ f/(s + λu)` would lie in `ℒ̃`. The node
`conj_stable_real_pencil_space_carries_two_by_three_configuration` puts a `2 × 3` configuration
inside that space, which contradicts the strong six exponentials hypothesis. -/

namespace R11_realPencil

open DiazModulus

/-- The space `Q̄ + Q̄u + Q̄ū + Q̄f + Q̄g` lies in `ℒ̃` once `u ∈ ℒ` and `f, g ∈ ℒ̃`. -/
theorem span_le_logAlgTilde {u f g : ℂ} (huL : u ∈ LogAlg) (hf : f ∈ LogAlgTilde)
    (hg : g ∈ LogAlgTilde) :
    Submodule.span Qbar ({1, u, conj u, f, g} : Set ℂ) ≤ LogAlgTilde :=
  Submodule.span_le.2 (Set.insert_subset_iff.2 ⟨Submodule.subset_span (Set.mem_insert _ _),
    Set.insert_subset_iff.2 ⟨Submodule.subset_span (Set.mem_insert_of_mem _ huL),
      Set.insert_subset_iff.2
        ⟨Submodule.subset_span (Set.mem_insert_of_mem _ (logAlg_conj_stable u huL)),
        Set.insert_subset_iff.2 ⟨hf, Set.singleton_subset_iff.2 hg⟩⟩⟩⟩)

end R11_realPencil

open DiazModulus R11_realPencil in
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {u : ℂ} (h : IsCandidate u) (lam : ℂ) (hlam : lam ∈ Qbar) (hlam1 : lam * conj lam = 1) (f : ℂ) (hf : conj f = f)
    (hind : LinearIndependent (↥Qbar) ![1, u, conj u, f, f / (((‖u‖ : ℝ) : ℂ) + lam * u)]) :
    ¬ (f ∈ LogAlgTilde ∧ f / (((‖u‖ : ℝ) : ℂ) + lam * u) ∈ LogAlgTilde) := by
  rintro ⟨hfL, hgL⟩
  have huQ : u ∉ Qbar := fun hq => hermite_lindemann_holds u h.1 (mem_Qbar_iff.1 hq) h.2.2
  have hs : ((‖u‖ : ℝ) : ℂ) ∈ Qbar := mem_Qbar_iff.2 h.2.1
  have hsr : conj ((‖u‖ : ℝ) : ℂ) = ((‖u‖ : ℝ) : ℂ) := Complex.conj_ofReal _
  have hss : ((‖u‖ : ℝ) : ℂ) * ((‖u‖ : ℝ) : ℂ) = u * conj u := by
    rw [Complex.mul_conj', sq]
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    (conj_stable_real_pencil_space_carries_two_by_three_configuration u _ huQ hs hsr hss
      lam hlam hlam1 f hf hind).2
  exact hSSE x y hx hy fun i j => span_le_logAlgTilde h.2.2 hfL hgL (hxy i j)
