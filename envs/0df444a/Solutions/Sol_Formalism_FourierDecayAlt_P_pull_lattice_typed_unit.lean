-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.pull_lattice_typed_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:33.821804+00:00
-- url     : https://prove2.me/submissions/2006f8d6-7f46-43f4-b6fc-472f4de33613

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Theorems.Thm_Formalism_FourierDecayAlt_P_pull_lattice_typed

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
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.PullLatticeTypedUnit := by
  intro hT E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ R u c α ψ η Θ hR hc hci hu t
  refine Iff.trans ?_ (Formalism.FourierDecayAlt.P.pull_lattice_typed hT E g ν s hg hpd P hP hgP K o σ hσ R
    (c⁻¹ * u) α ψ η Θ hR (by rw [Units.val_mul, hu, Units.inv_mul_cancel_left]) t)
  show (u : K × K) * _ ∈ R ↔ ((c⁻¹ * u : (K × K)ˣ) : K × K) * _ ∈ R
  rw [hu, Units.val_mul, hu, Units.inv_mul_cancel_left, mul_assoc]
  exact unit_mul_mem_iff' R c hc hci _
end Formalism.FourierDecayAlt.P
