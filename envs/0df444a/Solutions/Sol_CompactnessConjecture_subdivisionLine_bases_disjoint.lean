-- Prove2me | solution 1 for CompactnessConjecture.subdivisionLine_bases_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/3bcd65a4-f49f-4cbb-b0d6-0d8ac23ad877

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticLine_eq_of_points
import Theorems.Thm_CompactnessConjecture_symplectic_triangle_lines_eq
import Theorems.Thm_CompactnessConjecture_subdivisionLine_pair_incidence

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
    (L : Fin 3 → SymplecticLine K)
    (C : Fin k → SymplecticLine K)
    (hbase : ∀ base : Fin 3,
      copy (.inl (.inl base)) = .inr (L base))
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inr (C center))
    {i j : Fin 3} (hij : i ≠ j) (center : Fin k) :
    Disjoint (L i).1 (L j).1 := by
  apply Submodule.disjoint_def.mpr
  intro x hxi hxj
  by_contra hx
  let p : SymplecticPoint K :=
    ⟨K ∙ x, finrank_span_singleton hx⟩
  have hpLi : p.1 ≤ (L i).1 :=
    (Submodule.span_le).mpr (by simpa using hxi)
  have hpLj : p.1 ≤ (L j).1 :=
    (Submodule.span_le).mpr (by simpa using hxj)
  obtain ⟨pi, hpairi, hpiLi, hpiC⟩ :=
    subdivisionLine_pair_incidence K copy (hbase i) (hcenter center)
  obtain ⟨pj, hpairj, hpjLj, hpjC⟩ :=
    subdivisionLine_pair_incidence K copy (hbase j) (hcenter center)
  have hpipj : pi ≠ pj := by
    intro heq
    apply hij
    have hsource :
        (Sum.inr (i, center) : SubdivisionVertex k) =
          .inr (j, center) := by
      apply copy.injective
      change copy (.inr (i, center)) =
        copy (.inr (j, center))
      rw [hpairi, hpairj, heq]
    exact congrArg Prod.fst (Sum.inr.inj hsource)
  have hcenterNeBase (base : Fin 3) : C center ≠ L base := by
    intro heq
    have hsource :
        (Sum.inl (Sum.inr center) : SubdivisionVertex k) =
          .inl (.inl base) := by
      apply copy.injective
      change copy (.inl (.inr center)) =
        copy (.inl (.inl base))
      rw [hcenter center, hbase base, heq]
    cases Sum.inl.inj hsource
  have hpjp : pj ≠ p := by
    intro heq
    have hpjLi : pj.1 ≤ (L i).1 := by
      simpa only [heq] using hpLi
    have hline : C center = L i :=
      symplecticLine_eq_of_points K hpipj
        hpiC hpjC hpiLi hpjLi
    exact hcenterNeBase i hline
  have hline : C center = L j :=
    symplectic_triangle_lines_eq K hpipj hpjp
      hpiC hpjC hpiLi hpLi hpjLj hpLj
  exact hcenterNeBase j hline
end CompactnessConjecture
