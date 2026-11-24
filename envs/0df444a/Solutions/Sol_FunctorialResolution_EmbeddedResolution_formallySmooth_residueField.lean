-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.formallySmooth_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:20:12.843326+00:00
-- url     : https://prove2.me/submissions/0401c2b4-b732-4f00-ac75-2e18653c92f5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
private theorem formallySmooth_of_isAlgebraic (k : Type u) [Field k] [CharZero k] (L : Type u)
    [Field L] [Algebra k L] (A₀ : Type u) [CommRing A₀] [IsDomain A₀] [Algebra k A₀] [Algebra A₀ L]
    [IsScalarTower k A₀ L] [Algebra.FormallySmooth k A₀] [Algebra.IsAlgebraic A₀ L]
    (hinj : Function.Injective (algebraMap A₀ L)) :
    Algebra.FormallySmooth k L := by
  have hunit : ∀ y : nonZeroDivisors A₀, IsUnit (algebraMap A₀ L y) := by
    intro y
    refine isUnit_iff_ne_zero.mpr (fun hy => ?_)
    have h0 : (y : A₀) = 0 := hinj (by rw [hy, map_zero])
    exact nonZeroDivisors.coe_ne_zero y h0
  let algFL : Algebra (FractionRing A₀) L := (IsLocalization.lift hunit).toAlgebra
  have _twr1 : IsScalarTower k A₀ (FractionRing A₀) := inferInstance
  have _twr2 : IsScalarTower A₀ (FractionRing A₀) L :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsLocalization.lift_eq hunit a).symm)
  have _twr3 : IsScalarTower k (FractionRing A₀) L := by
    refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
    rw [IsScalarTower.algebraMap_apply k A₀ (FractionRing A₀) c,
      ← IsScalarTower.algebraMap_apply A₀ (FractionRing A₀) L,
      ← IsScalarTower.algebraMap_apply k A₀ L]
  have _fs1 : Algebra.FormallySmooth A₀ (FractionRing A₀) :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors A₀)
  have _fs2 : Algebra.FormallySmooth k (FractionRing A₀) :=
    Algebra.FormallySmooth.comp k A₀ (FractionRing A₀)
  have _hchar : CharZero (FractionRing A₀) :=
    charZero_of_injective_algebraMap (RingHom.injective (algebraMap k (FractionRing A₀)))
  have _halgF : Algebra.IsAlgebraic (FractionRing A₀) L := by
    refine ⟨fun a => ?_⟩
    obtain ⟨q, hq0, hqa⟩ := (Algebra.IsAlgebraic.isAlgebraic a : IsAlgebraic A₀ a)
    refine ⟨q.map (algebraMap A₀ (FractionRing A₀)), ?_, ?_⟩
    · exact (Polynomial.map_ne_zero_iff
        (IsFractionRing.injective A₀ (FractionRing A₀))).mpr hq0
    · rw [Polynomial.aeval_map_algebraMap]
      exact hqa
  have _hsep : Algebra.IsSeparable (FractionRing A₀) L := by
    refine ⟨fun a => ?_⟩
    exact (minpoly.irreducible
      ((Algebra.IsAlgebraic.isAlgebraic a : IsAlgebraic (FractionRing A₀) a).isIntegral)).separable
  have _fet : Algebra.FormallyEtale (FractionRing A₀) L :=
    Algebra.FormallyEtale.of_isSeparable ..
  have _fs3 : Algebra.FormallySmooth (FractionRing A₀) L := inferInstance
  exact Algebra.FormallySmooth.comp k (FractionRing A₀) L
private theorem formallySmooth_of_isTranscendenceBasis (k : Type u) [Field k] [CharZero k]
    (L : Type u) [Field L] [Algebra k L] {ι : Type u} {x : ι → L}
    (hx : IsTranscendenceBasis k x) : Algebra.FormallySmooth k L := by
  have hai : AlgebraicIndependent k x := hx.1
  have _fsA : Algebra.FormallySmooth k ↥(Algebra.adjoin k (Set.range x)) :=
    Algebra.FormallySmooth.of_equiv hai.aevalEquiv
  have _halg : Algebra.IsAlgebraic ↥(Algebra.adjoin k (Set.range x)) L := hx.isAlgebraic
  have _hdom : IsDomain ↥(Algebra.adjoin k (Set.range x)) := inferInstance
  exact formallySmooth_of_isAlgebraic k L ↥(Algebra.adjoin k (Set.range x))
    (fun a b h => Subtype.ext h)
private theorem formallySmooth_of_charZero (k : Type u) [Field k] [CharZero k] (L : Type u) [Field L]
    [Algebra k L] : Algebra.FormallySmooth k L := by
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis k L
  exact formallySmooth_of_isTranscendenceBasis k L hB
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X)
    [Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk x))]
    (_h : algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x)) =
      (IsLocalRing.residue (X.presheaf.stalk x)).comp (stalkAlgebraMap k p x)) :
    Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
  formallySmooth_of_charZero k (IsLocalRing.ResidueField (X.presheaf.stalk x))
end FunctorialResolution.EmbeddedResolution
