-- Prove2me | solution 1 for Erdos180.subdivisionPoint_center_of_point_base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:43:24.448669+00:00
-- url     : https://prove2.me/submissions/3ff4f5c4-0c21-4a9e-a8a7-4b0a6b33eb58

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
    {p : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p) :
    ∃ c : SymplecticPoint K,
      copy (.inl (.inr center)) = .inl c := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨L, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hpair] at hcenteradj
  obtain ⟨c, hc, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hcenteradj.symm
  exact ⟨c, hc⟩
