-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf_of_forall_away
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ec911bf5-20e3-57a8-883e-f8a54c77f919

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isBaseChangeAlong_of_isLocalization
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_forall_isBaseChangeAlong_away_of_overlap
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_of_forall_isBaseChangeAlong_away
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_isQuadrupleOf_iff_isIsomorphic
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_map_of_isBaseChangeAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf_of_forall_away

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B)
    {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (Q : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
    (hQ : ∀ i : Fin k, (Q i).IsQuadrupleOf
      (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))))) :
    ∃ Qg : DrinfeldDatum (K := K) π B, Qg.IsQuadrupleOf d := by
  classical

  let C : Fin k → Fin k → Type := fun i j => Localization.Away (algebraMap B (Localization.Away (f i)) (f j))
  letI algR : ∀ i j : Fin k, Algebra (Localization.Away (f j)) (C i j) := fun i j =>
    (IsLocalization.Away.awayToAwayLeft (f j) (f i) :
      Localization.Away (f j) →+* Localization.Away (algebraMap B (Localization.Away (f i)) (f j))).toAlgebra
  haveI towR : ∀ i j : Fin k, IsScalarTower B (Localization.Away (f j)) (C i j) := fun i j =>
    IsScalarTower.of_algebraMap_eq fun b => (IsLocalization.Away.awayToAwayLeft_eq (f j) (f i) b).symm
  haveI towR𝒪 : ∀ i j : Fin k, IsScalarTower 𝒪 (Localization.Away (f j)) (C i j) := fun i j =>
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away (f j)), ← IsScalarTower.algebraMap_apply B _ (C i j),
        IsScalarTower.algebraMap_apply 𝒪 B (C i j)]
  haveI locR : ∀ i j : Fin k, IsLocalization.Away (algebraMap B (Localization.Away (f j)) (f i)) (C i j) := fun i j =>
    IsLocalization.Away.commutes (Localization.Away (f j)) (Localization.Away (f i)) (C i j) (f j) (f i)

  have bc1 : ∀ i j : Fin k, ∃ Q₂ : DrinfeldDatum (K := K) π (C i j),
      (Q i).IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) Q₂ := fun i j =>
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isBaseChangeAlong_of_isLocalization (Q i)
      (Submonoid.powers (algebraMap B (Localization.Away (f i)) (f j))) (C i j)
  choose Q₂ hQ₂ using bc1
  have bc2 : ∀ i j : Fin k, ∃ Q₂' : DrinfeldDatum (K := K) π (C i j),
      (Q j).IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) Q₂' := fun i j =>
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isBaseChangeAlong_of_isLocalization (Q j)
      (Submonoid.powers (algebraMap B (Localization.Away (f j)) (f i))) (C i j)
  choose Q₂' hQ₂' using bc2

  have hmap : ∀ i j : Fin k,
      (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))).map π
          (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) =
        (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j)))).map π
          (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) := by
    intro i j
    have h1 := (Omega K π).map_comp (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))
      (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) d
    have h2 := (Omega K π).map_comp (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j)))
      (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) d
    have h3 : (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)).comp
          (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) =
        (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)).comp
          (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j))) := by
      apply AlgHom.ext; intro b
      simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, ← IsScalarTower.algebraMap_apply]
    exact h1.symm.trans (h3 ▸ h2)
  have hd1 : ∀ i j : Fin k, (Q₂ i j).IsQuadrupleOf ((d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))).map π
      (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j))) := fun i j =>
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.map_of_isBaseChangeAlong _ (hQ i) (hQ₂ i j)
  have hd2 : ∀ i j : Fin k, (Q₂' i j).IsQuadrupleOf ((d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))).map π
      (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j))) := fun i j => by
    rw [hmap]
    exact CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.map_of_isBaseChangeAlong _ (hQ j) (hQ₂' i j)
  have hBC : ∀ i j : Fin k, IsNilpotent (algebraMap 𝒪 (C i j) π) := fun i j => by
    rw [IsScalarTower.algebraMap_apply 𝒪 B (C i j)]; exact hB.map _
  have hiso : ∀ i j : Fin k, (Q₂' i j).IsIsomorphic (Q₂ i j) := fun i j =>
    (CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isQuadrupleOf_iff_isIsomorphic hπ (hBC i j) (hd1 i j)
      (Q₂' i j)).mp (hd2 i j)
  have hr : ∀ i j : Fin k,
      (Q j).IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) (Q₂ i j) := fun i j =>
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic _ (hQ₂' i j) (hiso i j)
  obtain ⟨Qg, hQg⟩ :=
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_forall_isBaseChangeAlong_away_of_overlap f hf Q C Q₂ hQ₂ hr
  exact ⟨Qg, CerednikDrinfeld.FormalOmega.DrinfeldDatum.isQuadrupleOf_of_forall_isBaseChangeAlong_away f hf Qg d Q hQg hQ⟩

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf_of_forall_away
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf_of_forall_away (solution)
