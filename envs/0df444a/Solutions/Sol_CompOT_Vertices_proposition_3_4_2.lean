-- Prove2me | solution 2 for CompOT.Vertices.proposition_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:55:52.348017+00:00
-- url     : https://prove2.me/submissions/b2028246-cd23-49dc-98e2-0c47a736d8f4

import Mathlib
import Definitions.Def_CompOT_Vertices_Defs
import Theorems.Thm_CompOT_Vertices_prop_3_4_cycle_perturbation
import Theorems.Thm_CompOT_Vertices_prop_3_4_edges_eq_nonzero
import Theorems.Thm_CompOT_Vertices_prop_3_4_perturbation_feasible

-- carved verbatim out of submission aa58bafa-e00a-42de-88a4-fbaad32273c9, lines 248-291

section
set_option autoImplicit false
open CompOT.Vertices Filter Topology

theorem solution {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (hP : IsExtremal (CompOT.Assignment.couplings a b) P) :
    (supportGraph P).IsAcyclic ∧ (nonzeroEntries P).card ≤ n + m - 1 := by
  classical
  obtain ⟨hPmem, hext⟩ := hP
  have hacyc : (supportGraph P).IsAcyclic := by
    by_contra hcyc
    obtain ⟨E, hE0, hrow, hcol, hsupp⟩ := CompOT.Vertices.prop_3_4_cycle_perturbation P hcyc
    obtain ⟨t, ht, hQ, hR⟩ := CompOT.Vertices.prop_3_4_perturbation_feasible a b P E ha hb hPmem hrow hcol hsupp
    have hmid : P = (1 / 2 : ℝ) • ((P + t • E) + (P - t • E)) := by
      ext i j
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
      ring
    obtain ⟨h1, _⟩ := hext _ hQ _ hR hmid
    apply hE0
    have h2 : t • E = 0 := by
      have : P + t • E = P + 0 := by rw [add_zero]; exact h1.symm
      exact add_left_cancel this
    rcases smul_eq_zero.1 h2 with h | h
    · exact absurd h ht.ne'
    · exact h
  refine ⟨hacyc, ?_⟩
  have hPnn : ∀ i j, 0 ≤ P i j := hPmem.1
  have hcard := CompOT.Vertices.prop_3_4_edges_eq_nonzero P hPnn
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have := ha.2
      simp at this
    · exact h
  have hne : Nonempty (Fin n ⊕ Fin m) := ⟨Sum.inl ⟨0, hn⟩⟩
  have hconn : (⊤ : SimpleGraph (Fin n ⊕ Fin m)).Connected := SimpleGraph.connected_top
  obtain ⟨F, hGF, _, hF⟩ := hconn.exists_isTree_le_of_le_of_isAcyclic (le_top : supportGraph P ≤ ⊤) hacyc
  have h1 := hF.card_edgeFinset
  have h2 : Nat.card (supportGraph P).edgeSet ≤ Nat.card F.edgeSet :=
    Nat.card_mono (Set.toFinite _) (SimpleGraph.edgeSet_mono hGF)
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at h2
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at h2
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at hcard
  simp only [Fintype.card_sum, Fintype.card_fin] at h1
  omega

end
