-- Prove2me | solution 1 for CompactnessConjecture.subdivisionLine_base_of_line_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/cc8c1c4b-d574-4f29-a25a-aa8bfd6df95d

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_adjacent_to_point
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
    {C : SymplecticLine K}
    (hcenter : copy (.inl (.inr center)) = .inr C) :
    ∃ L : SymplecticLine K,
      copy (.inl (.inl base)) = .inr L := by
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hcenter] at hcenteradj
  obtain ⟨p, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hcenteradj
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hpair] at hbaseadj
  obtain ⟨L, hL, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hbaseadj.symm
  exact ⟨L, hL⟩
end CompactnessConjecture
