-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.cover_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:22.159692+00:00
-- url     : https://prove2.me/submissions/ebaf0050-f95f-4822-b0c4-3646c497a3ee

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution (Γ : Set G) (hΓ : ∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ) (h1 : (1 : G) ∈ Γ)
    (R : ℕ → Set G) (m : ℕ) (hm : ∀ x ∈ R m, x = 1) (S : ℕ → Set G) (hS : ∀ k, IsCompact (S k))
    (hstep : ∀ k < m, ∀ x ∈ R k, ∃ γ ∈ Γ, ∃ y ∈ R (k + 1), ∃ s ∈ S k, x = γ * y * s) :
    ∃ C : Set G, IsCompact C ∧ ∀ x ∈ R 0, ∃ γ ∈ Γ, ∃ c ∈ C, x = γ * c := by
  have main : ∀ n k, k + n = m →
      ∃ C : Set G, IsCompact C ∧ ∀ x ∈ R k, ∃ γ ∈ Γ, ∃ c ∈ C, x = γ * c := by
    intro n
    induction n with
    | zero =>
      intro k hk
      have hkm : k = m := by omega
      subst hkm
      refine ⟨{1}, isCompact_singleton, fun x hx => ⟨1, h1, 1, Set.mem_singleton 1, ?_⟩⟩
      rw [hm x hx, one_mul]
    | succ n ih =>
      intro k hk
      obtain ⟨C, hC, hCx⟩ := ih (k + 1) (by omega)
      refine ⟨C * S k, hC.mul (hS k), fun x hx => ?_⟩
      obtain ⟨γ, hγ, y, hy, s, hs, rfl⟩ := hstep k (by omega) x hx
      obtain ⟨γ', hγ', c, hc, rfl⟩ := hCx y hy
      exact ⟨γ * γ', hΓ _ hγ _ hγ', c * s, Set.mul_mem_mul hc hs, by simp only [mul_assoc]⟩
  exact main m 0 (zero_add m)
end Formalism.L2.SG.Pf.Unip
