-- Prove2me | solution 1 for Formalism.L2.Pj.TranscendenceDegreeLemmas.fg_residueField_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:16:52.46524+00:00
-- url     : https://prove2.me/submissions/932f2ebf-bfa3-4fdd-b8a7-24ea4c714333

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_KapTrdegPfA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_KapTrdegPfB
import Theorems.Thm_Formalism_L2_Pj_TranscendenceDegreeLemmas_primeIdealOf_mem_minimalPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.TranscendenceDegreeLemmas
open AlgebraicGeometry CategoryTheory
namespace Formalism.L2.Pj.TranscendenceDegreeLemmas
theorem _root_.solution {K : Type} [Field K] [CharZero K] [FiniteDimensional ℚ K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) [Algebra K (X.residueField hZ.1.genericPoint)] :
    (⊤ : IntermediateField K (X.residueField hZ.1.genericPoint)).FG := by
  classical
  obtain ⟨U, hU, V, hV, hxV, e, hP⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) hZ.1.genericPoint
  have hUtop : U = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have hfx : f hZ.1.genericPoint ∈ U := e hxV
    rwa [Subsingleton.elim y (f hZ.1.genericPoint)]
  subst hUtop
  let e0 : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  let ψ : K →+* Γ(X, V) := (f.appLE ⊤ V e).hom.comp (e0 : K →+* _)
  let _ : Algebra K Γ(X, V) := ψ.toAlgebra
  have hsm : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, V) :=
    hP.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e0)
  have hmin := primeIdealOf_mem_minimalPrimes hV hZ hxV
  let _ : Algebra Γ(X, V) (X.presheaf.stalk hZ.1.genericPoint) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hZ.1.genericPoint, hxV⟩
  have hloc := hV.isLocalization_stalk ⟨hZ.1.genericPoint, hxV⟩
  let eL := IsLocalization.algEquiv (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.primeCompl
    (Localization.AtPrime (hV.primeIdealOf ⟨_, hxV⟩).asIdeal) (X.presheaf.stalk hZ.1.genericPoint)
  let eR : (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField ≃+* X.residueField hZ.1.genericPoint :=
    IsLocalRing.ResidueField.mapEquiv eL.toRingEquiv
  have hc1 : CharZero (X.residueField hZ.1.genericPoint) :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have hc2 : CharZero (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have t1 : IsScalarTower ℚ K (X.residueField hZ.1.genericPoint) :=
    IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm
  have t2 : IsScalarTower ℚ K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm
  have f00 : Algebra.IsStandardSmooth K Γ(X, V) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have f01 : Algebra.FinitePresentation K Γ(X, V) := inferInstance
  have f0 : Algebra.EssFiniteType K Γ(X, V) := inferInstance
  have f1 : Algebra.EssFiniteType K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp K Γ(X, V) _
  have f2 : Algebra.EssFiniteType ℚ K := inferInstance
  have f3 : Algebra.EssFiniteType ℚ (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp ℚ K _
  have f4 : Algebra.EssFiniteType ℚ (X.residueField hZ.1.genericPoint) :=
    (Algebra.EssFiniteType.iff_of_algEquiv eR.toRatAlgEquiv).1 f3
  have f5 : Algebra.EssFiniteType K (X.residueField hZ.1.genericPoint) := Algebra.EssFiniteType.of_comp ℚ K _
  exact IntermediateField.fg_top K _
end Formalism.L2.Pj.TranscendenceDegreeLemmas
