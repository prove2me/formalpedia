-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.comap_logDerivIdealSheafIterate_ker_le_derivIdealSheafIterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:01:25.948803+00:00
-- url     : https://prove2.me/submissions/2c8576d1-2ef1-43a2-950b-60544c2f975d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealQuotient
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheafClosedSubscheme
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_map_appLE_le_comap_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_algebraMap_sectionsAlgebra
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_mono
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.logDerivIdealSheafIterate_ideal


section
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
private theorem comp_app_apply {X Y Z : Scheme.{u}} (u : X ⟶ Y) (q : Y ⟶ Z) (U : Z.Opens)
    (a : Γ(Z, U)) : ((u ≫ q).app U).hom a = (u.app (q ⁻¹ᵁ U)).hom ((q.app U).hom a) := by
  have h : (u ≫ q).app U = q.app U ≫ u.app (q ⁻¹ᵁ U) := Scheme.Hom.comp_app u q U
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) a
private theorem comap_le_of_map_ideal_le {S X : Scheme.{u}} (ι : S ⟶ X) [IsAffineHom ι]
    (L : X.IdealSheafData) (D : S.IdealSheafData)
    (h : ∀ U : X.affineOpens, Ideal.map (ι.app (U : X.Opens)).hom (L.ideal U)
        ≤ D.ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩) :
    L.comap ι ≤ D := by
  have key : ∀ (U : X.affineOpens), L.ideal U
      ≤ RingHom.ker ((D.subschemeι ≫ ι).app (U : X.Opens)).hom := by
    intro U a ha
    have h1 := h U (Ideal.mem_map_of_mem _ ha)
    have h2 : (Scheme.Hom.ker D.subschemeι).ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩
        = RingHom.ker (D.subschemeι.app (ι ⁻¹ᵁ (U : X.Opens))).hom := by
      rw [Scheme.Hom.ker_apply]
    rw [Scheme.IdealSheafData.ker_subschemeι] at h2
    rw [h2] at h1
    refine RingHom.mem_ker.mpr ?_
    rw [comp_app_apply]
    exact RingHom.mem_ker.mp h1
  have hle : L ≤ Scheme.Hom.ker (D.subschemeι ≫ ι) := by
    unfold Scheme.Hom.ker
    exact Scheme.IdealSheafData.le_ofIdeals_iff.mpr key
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
  exact hle
private theorem derivIdealIterate_mono_of_le (k : Type u) [CommRing k] {T : Type u} [CommRing T]
    [Algebra k T] (r : ℕ) {I J : Ideal T} (h : I ≤ J) :
    derivIdealIterate k r I ≤ derivIdealIterate k r J := by
  induction r with
  | zero => exact h
  | succ r ih =>
      rw [derivIdealIterate_succ, derivIdealIterate_succ]
      exact derivIdeal_mono k ih
private theorem app_comp_sectionsAlgebraMap (k : Type u) [CommRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (ι : S ⟶ X) (U : X.Opens) :
    (ι.app U).hom.comp (sectionsAlgebraMap k p U) = sectionsAlgebraMap k (ι ≫ p) (ι ⁻¹ᵁ U) := by
  have happ : ι.appLE U (ι ⁻¹ᵁ U) le_rfl = ι.app U := Scheme.Hom.appLE_eq_app ι
  have hc : p.appLE ⊤ U (le_preimage_top k p U) ≫ ι.appLE U (ι ⁻¹ᵁ U) le_rfl
      = (ι ≫ p).appLE ⊤ (ι ⁻¹ᵁ U) (le_preimage_top k (ι ≫ p) (ι ⁻¹ᵁ U)) :=
    Scheme.Hom.appLE_comp_appLE ι p ⊤ U (ι ⁻¹ᵁ U) (le_preimage_top k p U) le_rfl
  have hmor : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U))
        ≫ ι.app U
      = (Scheme.ΓSpecIso (CommRingCat.of k)).inv
        ≫ (ι ≫ p).appLE ⊤ (ι ⁻¹ᵁ U) (le_preimage_top k (ι ≫ p) (ι ⁻¹ᵁ U)) := by
    rw [Category.assoc, ← happ, hc]
  rw [sectionsAlgebraMap_eq k p U, sectionsAlgebraMap_eq k (ι ≫ p) (ι ⁻¹ᵁ U)]
  exact congrArg CommRingCat.Hom.hom hmor
private theorem app_sectionsAlgebraMap (k : Type u) [CommRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (ι : S ⟶ X) (U : X.Opens) (a : k) :
    (ι.app U).hom (sectionsAlgebraMap k p U a) = sectionsAlgebraMap k (ι ≫ p) (ι ⁻¹ᵁ U) a :=
  DFunLike.congr_fun (app_comp_sectionsAlgebraMap k p ι U) a
private theorem map_logDerivIdealSheafIterate_ideal_le
    (k : Type u) [CommRing k] [IsNoetherianRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (ι : S ⟶ X) [IsClosedImmersion ι] [LocallyOfFiniteType (ι ≫ p)]
    (A : X.IdealSheafData) (r : ℕ) (U : X.affineOpens) :
    Ideal.map (ι.app (U : X.Opens)).hom ((logDerivIdealSheafIterate k p ι.ker r A).ideal U)
      ≤ (derivIdealSheafIterate k (ι ≫ p) r (A.comap ι)).ideal
          ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ := by
  have hcomm : ∀ a : k,
      (ι.app (U : X.Opens)).hom
          (@algebraMap k _ _ _ (sectionsAlgebra k p (U : X.Opens)) a)
        = @algebraMap k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) a := by
    intro a
    have e1 : @algebraMap k _ _ _ (sectionsAlgebra k p (U : X.Opens))
        = sectionsAlgebraMap k p (U : X.Opens) :=
      algebraMap_sectionsAlgebra k p (U : X.Opens)
    have e2 : @algebraMap k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens)))
        = sectionsAlgebraMap k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens)) :=
      algebraMap_sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))
    rw [e1, e2]
    exact app_sectionsAlgebraMap k p ι (U : X.Opens) a
  have hmapLE : ∀ (V : S.affineOpens) (e : (V : S.Opens) ≤ ι ⁻¹ᵁ (U : X.Opens)),
      Ideal.map (ι.appLE (U : X.Opens) (V : S.Opens) e).hom (A.ideal U)
        ≤ (A.comap ι).ideal V := by
    intro V e
    apply Scheme.IdealSheafData.map_appLE_le_comap_ideal
  have hmap : Ideal.map (ι.app (U : X.Opens)).hom (A.ideal U)
      ≤ (A.comap ι).ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ := by
    rw [Scheme.Hom.app_eq_appLE]
    exact hmapLE ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ le_rfl
  have halg := @map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker k _ _ _ _ _
      (sectionsAlgebra k p (U : X.Opens))
      (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens)))
      (@AlgHom.mk k _ _ _ _ _ (sectionsAlgebra k p (U : X.Opens))
        (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) (ι.app (U : X.Opens)).hom hcomm)
      (Scheme.Hom.app_surjective ι (U : X.Opens) U.2) _ rfl r (A.ideal U)
  rw [logDerivIdealSheafIterate_ideal, Scheme.Hom.ker_apply, derivIdealSheafIterate_ideal]
  refine le_trans halg ?_
  exact @derivIdealIterate_mono_of_le k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) r _ _
    hmap
private theorem logDerivIdealSheafIterate_comap_le_derivIdealSheafIterate
    (k : Type u) [CommRing k] [IsNoetherianRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (ι : S ⟶ X) [IsClosedImmersion ι] [LocallyOfFiniteType (ι ≫ p)]
    (A : X.IdealSheafData) (r : ℕ) :
    (logDerivIdealSheafIterate k p ι.ker r A).comap ι
      ≤ derivIdealSheafIterate k (ι ≫ p) r (A.comap ι) :=
  comap_le_of_map_ideal_le ι (logDerivIdealSheafIterate k p ι.ker r A)
    (derivIdealSheafIterate k (ι ≫ p) r (A.comap ι))
    (map_logDerivIdealSheafIterate_ideal_le k p ι A r)
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution
    (k : Type u) [CommRing k] [IsNoetherianRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (ι : S ⟶ X) [IsClosedImmersion ι] [LocallyOfFiniteType (ι ≫ p)]
    (A : X.IdealSheafData) (r : ℕ) :
    (logDerivIdealSheafIterate k p ι.ker r A).comap ι
      ≤ derivIdealSheafIterate k (ι ≫ p) r (A.comap ι) :=
  logDerivIdealSheafIterate_comap_le_derivIdealSheafIterate k p ι A r
end FunctorialResolution.EmbeddedResolution
