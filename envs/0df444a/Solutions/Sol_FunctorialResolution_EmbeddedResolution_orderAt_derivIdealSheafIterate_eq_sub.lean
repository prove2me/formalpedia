-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_derivIdealSheafIterate_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:55:44.063879+00:00
-- url     : https://prove2.me/submissions/fd642414-7c0d-46fd-86ed-be20383050c0

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_derivIdealSheafIterate
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isNoetherianRing_stalk
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_formallySmooth_stalk
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_finite_kaehlerDifferential_stalk
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_free_kaehlerDifferential_stalk
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isUnit_natCast_stalk
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_formallySmooth_residueField
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_local_parameters_and_dual_derivations
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_derivIdealIterate_of_isUnit_natCast
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_idealOrder


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (I : X.IdealSheafData)
    (x : X) {r : ℕ} (hr : orderAt I x = (r : ℕ∞)) {j : ℕ} (hj : j ≤ r) :
    orderAt (derivIdealSheafIterate k p j I) x = ((r - j : ℕ) : ℕ∞) := by
  let algst : Algebra k (X.presheaf.stalk x) := stalkAlgebra k p x
  have _hN : IsNoetherianRing (X.presheaf.stalk x) := isNoetherianRing_stalk k p x
  have _hFS : Algebra.FormallySmooth k (X.presheaf.stalk x) := formallySmooth_stalk k p x
  have _hFin : Module.Finite (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) :=
    finite_kaehlerDifferential_stalk k p x
  have _hFree : Module.Free (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) :=
    free_kaehlerDifferential_stalk k p x
  let algres : Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    ((IsLocalRing.residue (X.presheaf.stalk x)).comp (stalkAlgebraMap k p x)).toAlgebra
  have _tower : IsScalarTower k (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have _hFSres : Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    formallySmooth_residueField k p x rfl
  obtain ⟨h, y, δ, hspan, hδ⟩ := exists_local_parameters_and_dual_derivations k (X.presheaf.stalk x)
  have hI' : idealOrder (stalkIdeal I x) = (r : ℕ∞) := by
    rw [← orderAt_eq_idealOrder]; exact hr
  rw [orderAt_eq_idealOrder, stalkIdeal_derivIdealSheafIterate k p j I x]
  exact idealOrder_derivIdealIterate_of_isUnit_natCast k y δ hδ hspan
    (fun n hn => isUnit_natCast_stalk k p x hn) hI' hj
end FunctorialResolution.EmbeddedResolution
