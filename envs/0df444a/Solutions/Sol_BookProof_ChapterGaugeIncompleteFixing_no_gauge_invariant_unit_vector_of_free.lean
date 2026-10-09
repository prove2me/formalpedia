-- Prove2me | solution 1 for BookProof.ChapterGaugeIncompleteFixing.no_gauge_invariant_unit_vector_of_free
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:33:09.123719+00:00
-- url     : https://prove2.me/submissions/c25581dd-1ecb-4465-b552-76431c7ccde9

-- Generated from ChapterGaugeIncompleteFixing.lean — solution of BookProof.ChapterGaugeIncompleteFixing.no_gauge_invariant_unit_vector_of_free
import Mathlib
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing



open scoped InnerProductSpace

variable {X : Type*}
variable (G : Type*) [Group G] [MulAction G X]
variable {G : Type*} [Group G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial G]
    {U : G → (H →L[ℂ] H)}
    (hfree : ∀ g : G, g ≠ 1 → ∀ Ψ : H, Ψ ≠ 0 → U g Ψ ≠ Ψ) :
    ¬ ∃ Ψ : H, ‖Ψ‖ = 1 ∧ ∀ g : G, U g Ψ = Ψ := by

  rintro ⟨Ψ, hnorm, hinv⟩
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hΨ : Ψ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact one_ne_zero hnorm.symm
  exact hfree g hg Ψ hΨ (hinv g)
