-- Prove2me | solution 1 for Erdos180.subdivisionLine_center_of_line_base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:45:49.418025+00:00
-- url     : https://prove2.me/submissions/e02e8ecf-a625-4b9c-8c8f-c4d0c14dbbc5

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.LinearAlgebra.Dimension.Finrank
import Theorems.Thm_Erdos180_subdivisionGraph_base_pair_adj
import Theorems.Thm_Erdos180_subdivisionGraph_center_pair_adj
import Theorems.Thm_Erdos180_symplecticQuadrangle_adjacent_to_line
import Theorems.Thm_Erdos180_symplecticQuadrangle_adjacent_to_point

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {L : SymplecticLine K}
    (hbase : copy (.inl (.inl base)) = .inr L) :
    ∃ C : SymplecticLine K,
      copy (.inl (.inr center)) = .inr C := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨p, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hpair] at hcenteradj
  obtain ⟨C, hC, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hcenteradj.symm
  exact ⟨C, hC⟩
