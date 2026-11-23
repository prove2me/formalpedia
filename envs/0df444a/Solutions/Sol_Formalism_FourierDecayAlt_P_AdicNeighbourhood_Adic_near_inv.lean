-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.Adic.near_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:54.911887+00:00
-- url     : https://prove2.me/submissions/9a32c4d6-7dd1-4eda-8623-ed6e143a91b1

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_Adic_unit_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdicNeighbourhood
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood
namespace Adic
theorem _root_.solution (h : Adic R ϖ) {a x : K} (ha : a ∈ I R (ϖ : K)) (hx : Near R a x) :
    ∃ v, x * v = 1 ∧ Near R a v ∧ v ∈ R := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨v, hv, e⟩ := h.unit_one ((ϖ : K) * a' * r) ⟨a' * r, R.mul_mem ha' hr, by ring⟩
  exact ⟨v, e, ⟨-(r * v), R.neg_mem (R.mul_mem hr hv), by linear_combination e⟩, hv⟩
end Adic
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
