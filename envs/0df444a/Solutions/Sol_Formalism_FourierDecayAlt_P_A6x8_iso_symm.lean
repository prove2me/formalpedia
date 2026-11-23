-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x8.iso_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:16.469102+00:00
-- url     : https://prove2.me/submissions/5443e7eb-6a55-40a4-a8b4-185f890e15c1

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x8
namespace Formalism.FourierDecayAlt.P.A6x8
theorem _root_.solution {K : Type} [CommRing K] (R : Subring K) {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K) (φ : coker R Z ≃ₗ[R] coker R Z') (hφ : φ ∈ isoZZ R Z Z') :
    φ.symm ∈ isoZZ R Z' Z := by
  refine ⟨by rw [← hφ.1]; simp, fun v' v hv => (hφ.2 v v' (by rw [← hv]; simp)).symm⟩
end Formalism.FourierDecayAlt.P.A6x8
