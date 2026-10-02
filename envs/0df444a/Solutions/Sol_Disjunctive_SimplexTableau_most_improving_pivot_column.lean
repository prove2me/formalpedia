-- Prove2me | solution 1 for Disjunctive.SimplexTableau.most_improving_pivot_column
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T00:39:23.387335+00:00
-- url     : https://prove2.me/submissions/f52a5dd0-f00d-4faa-88f7-cecc0b1a2ae8

import Mathlib
import Definitions.Def_Disjunctive_SimplexTableau_Tableau
import Definitions.Def_Disjunctive_SimplexTableau_Eval

set_option autoImplicit false

open Disjunctive.SimplexTableau in
theorem solution {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (k i : Fin n)
    (J : Finset (Fin n)) (xbar : Fin n → ℝ)
    (hrange : ∃ l ∈ J, -(Abar0 Atil btil ι k) / Abar0 Atil btil ι i < GammaOf Atil ι k i l ∧
      GammaOf Atil ι k i l < (1 - Abar0 Atil btil ι k) / Abar0 Atil btil ι i) :
    ∃ lstar ∈ J,
      (-(Abar0 Atil btil ι k) / Abar0 Atil btil ι i < GammaOf Atil ι k i lstar ∧
          GammaOf Atil ι k i lstar < (1 - Abar0 Atil btil ι k) / Abar0 Atil btil ι i) ∧
        ∀ l ∈ J, (-(Abar0 Atil btil ι k) / Abar0 Atil btil ι i < GammaOf Atil ι k i l ∧
            GammaOf Atil ι k i l < (1 - Abar0 Atil btil ι k) / Abar0 Atil btil ι i) →
          FEval Atil btil ι k i J xbar lstar ≤ FEval Atil btil ι k i J xbar l := by
  classical
  obtain ⟨l0, hl0J, hl0⟩ := hrange
  have hne : (J.filter (fun l => -(Abar0 Atil btil ι k) / Abar0 Atil btil ι i < GammaOf Atil ι k i l ∧
      GammaOf Atil ι k i l < (1 - Abar0 Atil btil ι k) / Abar0 Atil btil ι i)).Nonempty :=
    ⟨l0, Finset.mem_filter.mpr ⟨hl0J, hl0⟩⟩
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image _ (fun l => FEval Atil btil ι k i J xbar l) hne
  rw [Finset.mem_filter] at hm
  refine ⟨m, hm.1, hm.2, fun l hlJ hl => hmin l (Finset.mem_filter.mpr ⟨hlJ, hl⟩)⟩
