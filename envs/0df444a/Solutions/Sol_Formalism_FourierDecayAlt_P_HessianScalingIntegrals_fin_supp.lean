-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HessianScalingIntegrals.fin_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:17.616821+00:00
-- url     : https://prove2.me/submissions/7c4fbbb9-b745-434f-8347-197d56564e9d

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HessianScalingIntegrals

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HessianScalingIntegrals
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.HessianScalingIntegrals
theorem _root_.solution [TopologicalSpace K] [IsTopologicalRing K] (Λ L : AddSubgroup K)
    (hΛ : IsOpen (Λ : Set K)) (hL : IsCompact (L : Set K)) (d : ℕ) :
    {y : Fin d → K ⧸ Λ | ∀ i, (Quotient.out (y i) : K) ∈ L}.Finite := by
  have : DiscreteTopology (K ⧸ Λ) := QuotientAddGroup.discreteTopology hΛ
  have h1 : ((QuotientAddGroup.mk : K → K ⧸ Λ) '' (L : Set K)).Finite :=
    (hL.image QuotientAddGroup.continuous_mk).finite_of_discrete
  refine (Set.Finite.pi' (fun _ : Fin d => h1)).subset ?_
  intro y hy i
  exact ⟨_, hy i, QuotientAddGroup.out_eq' _⟩
end Formalism.FourierDecayAlt.P.HessianScalingIntegrals
