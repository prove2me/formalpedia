-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_six_cycle_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/67365986-74e8-462f-a83e-6a621aa7eecb

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplectic_triangle_lines_eq
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_adjacent_to_point
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_adjacent_to_line

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution :
    (SimpleGraph.cycleGraph 6).Free (symplecticQuadrangle K) := by
  rintro ⟨copy⟩
  have h01 : (symplecticQuadrangle K).Adj (copy 0) (copy 1) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 0 1 by decide)
  have h12 : (symplecticQuadrangle K).Adj (copy 1) (copy 2) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 1 2 by decide)
  have h23 : (symplecticQuadrangle K).Adj (copy 2) (copy 3) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 2 3 by decide)
  have h34 : (symplecticQuadrangle K).Adj (copy 3) (copy 4) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 3 4 by decide)
  have h45 : (symplecticQuadrangle K).Adj (copy 4) (copy 5) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 4 5 by decide)
  have h50 : (symplecticQuadrangle K).Adj (copy 5) (copy 0) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 5 0 by decide)
  cases h0 : copy 0 with
  | inl p =>
      rw [h0] at h01 h50
      obtain ⟨L, h1, hpL⟩ :=
        symplecticQuadrangle_adjacent_to_point K h01
      rw [h1] at h12
      obtain ⟨q, h2, hqL⟩ :=
        symplecticQuadrangle_adjacent_to_line K h12
      rw [h2] at h23
      obtain ⟨M, h3, hqM⟩ :=
        symplecticQuadrangle_adjacent_to_point K h23
      rw [h3] at h34
      obtain ⟨r, h4, hrM⟩ :=
        symplecticQuadrangle_adjacent_to_line K h34
      rw [h4] at h45
      obtain ⟨N, h5, hrN⟩ :=
        symplecticQuadrangle_adjacent_to_point K h45
      rw [h5] at h50
      have hpN : p.1 ≤ N.1 :=
        (symplecticQuadrangle_incidence_adj K p N).mp h50.symm
      have hpq : p ≠ q := by
        intro heq
        apply (by decide : (0 : Fin 6) ≠ 2)
        apply copy.injective
        change copy 0 = copy 2
        rw [h0, h2, heq]
      have hqr : q ≠ r := by
        intro heq
        apply (by decide : (2 : Fin 6) ≠ 4)
        apply copy.injective
        change copy 2 = copy 4
        rw [h2, h4, heq]
      have hLM : L = M := symplectic_triangle_lines_eq K hpq hqr
        hpL hqL hpN hrN hqM hrM
      apply (by decide : (1 : Fin 6) ≠ 3)
      apply copy.injective
      change copy 1 = copy 3
      rw [h1, h3, hLM]
  | inr L =>
      rw [h0] at h01 h50
      obtain ⟨p, h1, hpL⟩ :=
        symplecticQuadrangle_adjacent_to_line K h01
      rw [h1] at h12
      obtain ⟨M, h2, hpM⟩ :=
        symplecticQuadrangle_adjacent_to_point K h12
      rw [h2] at h23
      obtain ⟨q, h3, hqM⟩ :=
        symplecticQuadrangle_adjacent_to_line K h23
      rw [h3] at h34
      obtain ⟨N, h4, hqN⟩ :=
        symplecticQuadrangle_adjacent_to_point K h34
      rw [h4] at h45
      obtain ⟨r, h5, hrN⟩ :=
        symplecticQuadrangle_adjacent_to_line K h45
      rw [h5] at h50
      have hrL : r.1 ≤ L.1 :=
        (symplecticQuadrangle_incidence_adj K r L).mp h50
      have hpq : p ≠ q := by
        intro heq
        apply (by decide : (1 : Fin 6) ≠ 3)
        apply copy.injective
        change copy 1 = copy 3
        rw [h1, h3, heq]
      have hqr : q ≠ r := by
        intro heq
        apply (by decide : (3 : Fin 6) ≠ 5)
        apply copy.injective
        change copy 3 = copy 5
        rw [h3, h5, heq]
      have hMN : M = N := symplectic_triangle_lines_eq K hpq hqr
        hpM hqM hpL hrL hqN hrN
      apply (by decide : (2 : Fin 6) ≠ 4)
      apply copy.injective
      change copy 2 = copy 4
      rw [h2, h4, hMN]
end CompactnessConjecture
