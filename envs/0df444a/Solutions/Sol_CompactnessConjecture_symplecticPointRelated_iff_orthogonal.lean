-- Prove2me | solution 1 for CompactnessConjecture.symplecticPointRelated_iff_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/bc19e2e1-2422-4d91-aca2-2a703dc5d141

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticPoint_sup_finrank

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (p q : SymplecticPoint K) :
    SymplecticPointRelated K p q ↔
      p ≠ q ∧ p.1 ≤ SymplecticPointOrthogonal K q := by
  constructor
  · rintro ⟨hpq, L, hpL, hqL⟩
    refine ⟨hpq, ?_⟩
    intro x hx
    change ∀ y ∈ q.1, standardSymplecticForm K y x = 0
    intro y hy
    exact L.2.2 y (hqL hy) x (hpL hx)
  · rintro ⟨hpq, hporth⟩
    let U : Submodule K (SymplecticVector K) := p.1 ⊔ q.1
    have hdim : Module.finrank K U = 2 :=
      symplecticPoint_sup_finrank K hpq
    have hqU : q.1 ≤ U := le_sup_right
    have hUorth : U ≤ SymplecticPointOrthogonal K q :=
      sup_le hporth (symplecticPoint_le_orthogonal K q)
    exact ⟨hpq,
      ⟨U, hdim, symplectic_two_plane_isotropic K hdim hqU hUorth⟩,
      le_sup_left, le_sup_right⟩
end CompactnessConjecture
