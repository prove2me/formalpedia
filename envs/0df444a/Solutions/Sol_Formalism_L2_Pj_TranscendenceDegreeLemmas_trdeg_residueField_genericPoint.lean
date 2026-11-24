-- Prove2me | solution 1 for Formalism.L2.Pj.TranscendenceDegreeLemmas.trdeg_residueField_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:24:01.957331+00:00
-- url     : https://prove2.me/submissions/98d9a4fb-741a-437c-ab8f-3e12c3dab913

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_KapTrdegPfA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_KapTrdegPfB
import Theorems.Thm_Formalism_L2_Pj_TranscendenceDegreeLemmas_primeIdealOf_mem_minimalPrimes
import Theorems.Thm_Formalism_L2_Pj_TranscendenceDegreeLemmas_trdeg_residueField_of_minimal


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
theorem _root_.solution {K : Type} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) [Algebra K (X.residueField hZ.1.genericPoint)] :
    Algebra.trdeg K (X.residueField hZ.1.genericPoint) = n := by
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
  have hcore := trdeg_residueField_of_minimal (K := K) n (hV.primeIdealOf ⟨_, hxV⟩).asIdeal hmin
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
  have a1 := trdeg_add_eq ℚ K (A := X.residueField hZ.1.genericPoint)
  have a2 := trdeg_add_eq ℚ K (A := (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField)
  have a3 := (eR.toRatAlgEquiv).trdeg_eq
  rw [trdeg_eq_zero (R := ℚ) (A := K), zero_add] at a1 a2
  rw [a1, ← a3, ← a2, hcore]
end Formalism.L2.Pj.TranscendenceDegreeLemmas
