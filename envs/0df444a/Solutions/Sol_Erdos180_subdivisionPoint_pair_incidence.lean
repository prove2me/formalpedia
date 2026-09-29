-- Prove2me | solution 1 for Erdos180.subdivisionPoint_pair_incidence
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:42:32.591218+00:00
-- url     : https://prove2.me/submissions/e98b40d2-6845-4481-a7d6-8de68397eaa2

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.LinearAlgebra.Dimension.Finrank
import Theorems.Thm_Erdos180_subdivisionGraph_base_pair_adj
import Theorems.Thm_Erdos180_subdivisionGraph_center_pair_adj
import Theorems.Thm_Erdos180_symplecticQuadrangle_adjacent_to_point

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {p c : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p)
    (hcenter : copy (.inl (.inr center)) = .inl c) :
    ∃ L : SymplecticLine K,
      copy (.inr (base, center)) = .inr L ∧
        p.1 ≤ L.1 ∧ c.1 ≤ L.1 := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨L, hpair, hpL⟩ :=
    symplecticQuadrangle_adjacent_to_point K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hcenter, hpair] at hcenteradj
  exact ⟨L, hpair, hpL,
    (symplecticQuadrangle_incidence_adj K c L).mp hcenteradj⟩
