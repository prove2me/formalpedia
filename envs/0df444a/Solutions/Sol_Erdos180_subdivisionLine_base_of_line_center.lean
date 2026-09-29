-- Prove2me | solution 1 for Erdos180.subdivisionLine_base_of_line_center
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:46:41.155886+00:00
-- url     : https://prove2.me/submissions/530bfe04-986c-4692-b2a2-7d23fed38d0b

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
