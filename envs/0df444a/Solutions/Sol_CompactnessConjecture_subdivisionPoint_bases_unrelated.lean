-- Prove2me | solution 1 for CompactnessConjecture.subdivisionPoint_bases_unrelated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/0a5a7642-4dfb-4e0a-8447-f66c87c7a058

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplectic_triangle_lines_eq
import Theorems.Thm_CompactnessConjecture_symplecticPointRelated_symm
import Theorems.Thm_CompactnessConjecture_subdivisionPoint_pair_incidence
import Theorems.Thm_CompactnessConjecture_subdivisionPoint_base_center_related

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
    (p : Fin 3 → SymplecticPoint K)
    (c : Fin k → SymplecticPoint K)
    (hbase : ∀ base : Fin 3,
      copy (.inl (.inl base)) = .inl (p base))
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inl (c center))
    {i j : Fin 3} (hij : i ≠ j) (center : Fin k) :
    ¬ SymplecticPointRelated K (p i) (p j) := by
  obtain ⟨Li, hi_pair, hpiLi, hcLi⟩ :=
    subdivisionPoint_pair_incidence K copy (hbase i)
      (hcenter center)
  obtain ⟨Lj, hj_pair, hpjLj, hcLj⟩ :=
    subdivisionPoint_pair_incidence K copy (hbase j)
      (hcenter center)
  have hic : SymplecticPointRelated K (p i) (c center) :=
    subdivisionPoint_base_center_related K copy (hbase i)
      (hcenter center)
  have hjc : SymplecticPointRelated K (p j) (c center) :=
    subdivisionPoint_base_center_related K copy (hbase j)
      (hcenter center)
  rintro ⟨_, Lij, hpiLij, hpjLij⟩
  have hlines : Li = Lj :=
    symplectic_triangle_lines_eq K hic.1
      (symplecticPointRelated_symm K hjc).1
      hpiLi hcLi hpiLij hpjLij hcLj hpjLj
  have hpair :
      copy (.inr (i, center)) = copy (.inr (j, center)) := by
    rw [hi_pair, hj_pair, hlines]
  have hsource :
      (Sum.inr (i, center) : SubdivisionVertex k) =
        .inr (j, center) := copy.injective hpair
  exact hij (congrArg Prod.fst (Sum.inr.inj hsource))
end CompactnessConjecture
