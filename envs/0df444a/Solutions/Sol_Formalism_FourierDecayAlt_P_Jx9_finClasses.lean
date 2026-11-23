-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx9.finClasses
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:59.247852+00:00
-- url     : https://prove2.me/submissions/96eef99c-b535-45c6-8359-ec2512b0838c

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx9
namespace Formalism.FourierDecayAlt.P.Jx9
theorem _root_.solution {X K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (hR : IsOpen (R : Set K)) (F' : Finset X) (Θ : K → X → X → ℂ)
    (h3 : ∃ L : Submodule R K, IsOpen (L : Set K) ∧ IsCompact (L : Set K) ∧
      ∀ x, x ∉ L → ∀ h ∈ F', ∀ h' ∈ F', Θ x h h' = 0) :
    {x : K ⧸ R.toAddSubgroup | ∃ h ∈ F', ∃ h' ∈ F', Θ (Quotient.out x) h h' ≠ 0}.Finite := by
  obtain ⟨L, _, hLc, hL⟩ := h3
  have : DiscreteTopology (K ⧸ R.toAddSubgroup) := QuotientAddGroup.discreteTopology hR
  have hc : IsCompact ((fun y : K => (y : K ⧸ R.toAddSubgroup)) '' (L : Set K)) :=
    hLc.image continuous_quot_mk
  refine hc.finite_of_discrete.subset ?_
  rintro x ⟨h, hh, h', hh', hne⟩
  refine ⟨Quotient.out x, ?_, Quotient.out_eq x⟩
  by_contra hx
  exact hne (hL _ hx h hh h' hh')
end Formalism.FourierDecayAlt.P.Jx9
