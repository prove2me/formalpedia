-- Prove2me | solution 1 for CompactnessConjecture.subdivisionPoint_base_center_related
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/8c4455af-98d7-4b77-8b1c-f3f9959d0d82

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_subdivisionPoint_pair_incidence

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
    {p c : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p)
    (hcenter : copy (.inl (.inr center)) = .inl c) :
    SymplecticPointRelated K p c := by
  obtain ⟨L, _, hpL, hcL⟩ :=
    subdivisionPoint_pair_incidence K copy hbase hcenter
  refine ⟨?_, L, hpL, hcL⟩
  intro hpc
  have hvertex :
      (Sum.inl (Sum.inl base) : SubdivisionVertex k) =
        .inl (.inr center) := by
    apply copy.injective
    change copy (.inl (.inl base)) =
      copy (.inl (.inr center))
    rw [hbase, hcenter, hpc]
  cases hvertex
end CompactnessConjecture
