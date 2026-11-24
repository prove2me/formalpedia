-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.pull_lift_typed_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:33.969797+00:00
-- url     : https://prove2.me/submissions/8df81fe9-dfa3-45ff-8ab6-9a4f5c495008

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Theorems.Thm_Formalism_FourierDecayAlt_P_pull_lift_typed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
namespace Formalism.FourierDecayAlt.P.Jx12
end Formalism.FourierDecayAlt.P.Jx12
namespace Formalism.FourierDecayAlt.P
private lemma unit_mul_mem_iff' {M : Type} [CommRing M] (R : Subring M) (c : Mˣ) (hc : (c : M) ∈ R)
    (hci : ((c⁻¹ : Mˣ) : M) ∈ R) (x : M) : (c : M) * x ∈ R ↔ x ∈ R := by
  constructor
  · intro h
    have h' := R.mul_mem hci h
    rwa [Units.inv_mul_cancel_left] at h'
  · intro h
    exact R.mul_mem hc h
private lemma mul_unit_mul_mem_iff {M : Type} [CommRing M] (R : Subring M) (c : Mˣ) (hc : (c : M) ∈ R)
    (hci : ((c⁻¹ : Mˣ) : M) ∈ R) (x y : M) : x * (c : M) * y ∈ R ↔ x * y ∈ R := by
  rw [show x * (c : M) * y = (c : M) * (x * y) by ring]
  exact unit_mul_mem_iff' R c hc hci _
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.PullLiftTypedUnit := by
  intro hT E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ R u c α ψ η Θ hR hc hci hu x
  refine Iff.trans ?_ (pull_lift_typed hT E g ν s hg hpd P hP hgP K o σ hσ R (c⁻¹ * u) α ψ η Θ hR
    (by rw [Units.val_mul, hu, Units.inv_mul_cancel_left]) x)
  show ((u⁻¹ : (K × K)ˣ) : K × K) * _ ∈ R ↔ (((c⁻¹ * u)⁻¹ : (K × K)ˣ) : K × K) * _ ∈ R
  rw [mul_inv_rev, inv_inv, Units.val_mul]
  exact (mul_unit_mul_mem_iff R c hc hci _ _).symm
end Formalism.FourierDecayAlt.P
