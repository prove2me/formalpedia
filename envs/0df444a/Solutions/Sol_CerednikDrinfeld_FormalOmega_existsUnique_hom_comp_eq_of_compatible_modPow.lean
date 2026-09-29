-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.existsUnique_hom_comp_eq_of_compatible_modPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/725e47d9-fac1-58ad-a971-6e1db12d11e1

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_AlgebraicGeometry_existsUnique_specMap_mk_pow_comp_eq_of_isAdicComplete_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_hom_comp_eq_of_compatible_modPow

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

namespace AdicLim12

variable {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (R : Type) [CommRing R] [Algebra 𝒪 R]

theorem span_pow_eq (n : ℕ) :
    Ideal.span {algebraMap 𝒪 R π ^ (n + 1)} = Ideal.span {algebraMap 𝒪 R π} ^ (n + 1) :=
  (Ideal.span_singleton_pow _ _).symm

def e (n : ℕ) : modPow π R n ≃+* R ⧸ Ideal.span {algebraMap 𝒪 R π} ^ (n + 1) :=
  Ideal.quotEquivOfEq (span_pow_eq π R n)

theorem e_mk (n : ℕ) (r : R) :
    e π R n (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r := Ideal.quotEquivOfEq_mk _ _

theorem e_comp_mk (n : ℕ) :
    (e π R n).toRingHom.comp (algebraMap R (modPow π R n)) = Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π} ^ (n + 1)) := by
  ext r; exact e_mk π R n r

theorem factorPowSucc_comp_e (n : ℕ) :
    (Ideal.Quotient.factorPowSucc (Ideal.span {algebraMap 𝒪 R π}) (n + 1)).comp (e π R (n + 1)).toRingHom =
      (e π R n).toRingHom.comp (modPowTransition π R n).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  ext r
  simp only [RingHom.comp_apply]
  show Ideal.Quotient.factorPowSucc _ (n + 1) (e π R (n + 1) (Ideal.Quotient.mk _ r)) =
    e π R n (modPowTransition π R n (Ideal.Quotient.mk _ r))
  rw [e_mk]
  show _ = e π R n (Ideal.Quotient.mk _ r)
  rw [e_mk]
  rfl

end AdicLim12

open AdicLim12 in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (R : Type) [CommRing R] [Algebra 𝒪 R] [IsLocalRing R]
    (hR : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    {X : Scheme.{0}} (x : ∀ n : ℕ, Spec (CommRingCat.of (modPow π R n)) ⟶ X)
    (hx : ∀ n : ℕ, Spec.map (CommRingCat.ofHom (modPowTransition π R n).toRingHom) ≫ x (n + 1) = x n) :
    ∃! y : Spec (CommRingCat.of R) ⟶ X,
      ∀ n : ℕ, Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ y = x n := by
  set I : Ideal R := Ideal.span {algebraMap 𝒪 R π} with hI
  haveI : IsAdicComplete I R := hR

  let x' : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X := fun n =>
    Spec.map (CommRingCat.ofHom (e π R n).toRingHom) ≫ x n
  have hx' : ∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1))) ≫ x' (n + 1) = x' n := by
    intro n
    simp only [x']
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, factorPowSucc_comp_e, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc, hx n]
  obtain ⟨y, hy, huniq⟩ :=
    AlgebraicGeometry.existsUnique_specMap_mk_pow_comp_eq_of_isAdicComplete_of_isLocalRing I x' hx'

  have key : ∀ (z : Spec (CommRingCat.of R) ⟶ X) (n : ℕ),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ z = x' n ↔
        Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ z = x n := by
    intro z n
    simp only [x']
    rw [← e_comp_mk π R n, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hcancel : Spec.map (CommRingCat.ofHom (e π R n).symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom (e π R n).toRingHom) = 𝟙 _ := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingEquiv.symm_toRingHom_comp_toRingHom, CommRingCat.ofHom_id, Spec.map_id]
    constructor
    · intro h
      have h2 := congrArg (fun w => Spec.map (CommRingCat.ofHom (e π R n).symm.toRingHom) ≫ w) h
      rw [← Category.assoc, hcancel, Category.id_comp, ← Category.assoc, hcancel, Category.id_comp] at h2
      exact h2
    · intro h; rw [h]
  refine ⟨y, fun n => (key y n).1 (hy n), fun z hz => huniq z (fun n => (key z n).2 (hz n))⟩

end S_CerednikDrinfeld_FormalOmega_existsUnique_hom_comp_eq_of_compatible_modPow
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_hom_comp_eq_of_compatible_modPow (solution)
