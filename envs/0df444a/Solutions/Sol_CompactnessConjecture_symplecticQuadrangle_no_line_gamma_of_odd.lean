-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_no_line_gamma_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/d1214bd6-dad1-443d-8e37-7bd8c9734627

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_subdivisionLine_pair_incidence
import Theorems.Thm_CompactnessConjecture_subdivisionLine_center_of_line_base
import Theorems.Thm_CompactnessConjecture_subdivisionLine_base_of_line_center
import Theorems.Thm_CompactnessConjecture_subdivisionLine_centers_injective
import Theorems.Thm_CompactnessConjecture_subdivisionLine_bases_disjoint
import Theorems.Thm_CompactnessConjecture_symplecticLine_no_three_common_centers

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (htwo : (2 : K) ≠ 0)
    (copy : SimpleGraph.Copy gammaGraph
      (symplecticQuadrangle K))
    (C : SymplecticLine K)
    (hC : copy kSpecifiedCenter = .inr C) :
    False := by
  classical
  have hspecified :
      copy (.inl (.inr (0 : Fin 3))) = .inr C := by
    simpa [kSpecifiedCenter] using hC
  have hbase_exists (i : Fin 3) :
      ∃ L : SymplecticLine K,
        copy (.inl (.inl i)) = .inr L :=
    subdivisionLine_base_of_line_center K copy
      (base := i) (center := (0 : Fin 3)) hspecified
  choose bases hbase using hbase_exists
  have hcenter_exists (i : Fin 3) :
      ∃ L : SymplecticLine K,
        copy (.inl (.inr i)) = .inr L :=
    subdivisionLine_center_of_line_base K copy
      (base := (0 : Fin 3)) (center := i) (hbase 0)
  choose centers hcenter using hcenter_exists
  apply symplecticLine_no_three_common_centers K htwo
    (bases 1) (bases 2) (bases 0)
    (centers := centers)
  · exact subdivisionLine_bases_disjoint K copy bases centers
      hbase hcenter (by decide : (1 : Fin 3) ≠ 2) 0
  · exact subdivisionLine_bases_disjoint K copy bases centers
      hbase hcenter (by decide : (0 : Fin 3) ≠ 1) 0
  · exact subdivisionLine_bases_disjoint K copy bases centers
      hbase hcenter (by decide : (0 : Fin 3) ≠ 2) 0
  · exact subdivisionLine_centers_injective K copy centers hcenter
  · intro i
    obtain ⟨p, _, hpB, hpC⟩ := subdivisionLine_pair_incidence
      K copy (hbase 1) (hcenter i)
    exact ⟨p, hpB, hpC⟩
  · intro i
    obtain ⟨p, _, hpB, hpC⟩ := subdivisionLine_pair_incidence
      K copy (hbase 2) (hcenter i)
    exact ⟨p, hpB, hpC⟩
  · intro i
    obtain ⟨p, _, hpB, hpC⟩ := subdivisionLine_pair_incidence
      K copy (hbase 0) (hcenter i)
    exact ⟨p, hpB, hpC⟩
end CompactnessConjecture
