-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_zmod_prod_equiv_factorsThrough_of_etale_of_forall_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b0f71cac-41e7-5ae6-8fda-58bcd8ac8878

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_zmod_prod_equiv_factorsThrough_of_etale_of_forall_injective

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (N : ℕ) (hN : IsUnit ((N : ℕ) : R))
    {C : Scheme.{u}} (lev : C ⟶ 𝒜) [IsClosedImmersion lev] [IsFinite (lev ≫ f)] [Etale (lev ≫ f)]
    (lev_sub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      FactorsThrough lev P → FactorsThrough lev Q →
        FactorsThrough lev (L.mul t P Q) ∧ FactorsThrough lev (L.inv t P))
    (lev_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), FactorsThrough lev (L.one t))
    (lev_torsion : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      FactorsThrough lev P → nsmulPt L t N P = L.one t)
    (lev_rank : ∀ s : ↥(Spec (CommRingCat.of R)), (lev ≫ f).finrank s = N ^ 2)
    (hgen : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k), Function.Injective sk →
      ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough lev P},
        ∀ x y : ZMod N × ZMod N,
          (e (x + y) : SchemeHomOver (geomPoint k sk) f) = L.mul (geomPoint k sk) (e x) (e y)) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k),
      ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough lev P},
        ∀ x y : ZMod N × ZMod N,
          (e (x + y) : SchemeHomOver (geomPoint k sk) f) = L.mul (geomPoint k sk) (e x) (e y) := by
  intro k _ _ sk
  classical
  obtain ⟨G, instG, instF, hG⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale L lev
      (fun t => lev_one t) (fun t x y hx hy => (lev_sub t x y hx hy).1)
  letI : Group G := instG

  let K : Type u := FractionRing R
  let Kb : Type u := AlgebraicClosure K
  let sk₀ : R →+* Kb := (algebraMap K Kb).comp (algebraMap R K)
  have hsk₀ : Function.Injective sk₀ :=
    (algebraMap K Kb).injective.comp (IsFractionRing.injective R K)
  obtain ⟨e₀, he₀⟩ := hgen Kb sk₀ hsk₀
  obtain ⟨g₀, hg₀⟩ := hG Kb sk₀
  obtain ⟨g, hg⟩ := hG k sk

  let ψ : ZMod N × ZMod N ≃ G := e₀.trans g₀.symm
  have hψv : ∀ z : ZMod N × ZMod N,
      ((g₀ (ψ z) : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom sk₀)) f // ∃ z : _ ⟶ C, z ≫ lev = x.1}) :
        SchemeHomOver (Spec.map (CommRingCat.ofHom sk₀)) f) = (e₀ z).1 :=
    fun z => congrArg Subtype.val (g₀.apply_symm_apply (e₀ z))
  have hψ : ∀ x y : ZMod N × ZMod N, ψ (x + y) = ψ x * ψ y := by
    intro x y
    apply g₀.injective
    apply Subtype.ext
    rw [hg₀, hψv, hψv, hψv]
    exact he₀ x y
  refine ⟨ψ.trans g, fun x y => ?_⟩
  exact (congrArg (fun w => ((g w : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f //
      ∃ z : _ ⟶ C, z ≫ lev = x.1}) : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f)) (hψ x y)).trans
    (hg (ψ x) (ψ y))

end S_CerednikDrinfeld_QM_exists_zmod_prod_equiv_factorsThrough_of_etale_of_forall_injective
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_zmod_prod_equiv_factorsThrough_of_etale_of_forall_injective (solution)
