-- Prove2me | solution 1 for FamousTheorems.three_subgroups_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:37:32.581253+00:00
-- url     : https://prove2.me/submissions/73777a1e-63fd-40d9-8ce3-2d7ba4b395ba

import Mathlib

theorem solution {G : Type*} [Group G] {H₁ H₂ H₃ : Subgroup G} (h₁ : ⁅⁅H₂, H₃⁆, H₁⁆ = ⊥) (h₂ : ⁅⁅H₃, H₁⁆, H₂⁆ = ⊥) :
    ⁅⁅H₁, H₂⁆, H₃⁆ = ⊥ :=
  Subgroup.commutator_commutator_eq_bot_of_rotate h₁ h₂
