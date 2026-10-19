-- Prove2me | solution 1 for CompactnessConjecture.subdivisionLine_pair_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/43d7003c-16b5-4d46-83f4-89e3fc55a698

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_adjacent_to_line
import Theorems.Thm_CompactnessConjecture_subdivisionGraph_base_pair_adj
import Theorems.Thm_CompactnessConjecture_subdivisionGraph_center_pair_adj

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {L C : SymplecticLine K}
    (hbase : copy (.inl (.inl base)) = .inr L)
    (hcenter : copy (.inl (.inr center)) = .inr C) :
    ∃ p : SymplecticPoint K,
      copy (.inr (base, center)) = .inl p ∧
        p.1 ≤ L.1 ∧ p.1 ≤ C.1 := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨p, hpair, hpL⟩ :=
    symplecticQuadrangle_adjacent_to_line K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hcenter, hpair] at hcenteradj
  exact ⟨p, hpair, hpL,
    (symplecticQuadrangle_incidence_adj K p C).mp hcenteradj.symm⟩
end CompactnessConjecture
