-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x5.preimage_pow_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:21.724064+00:00
-- url     : https://prove2.me/submissions/16d7388f-70a5-4faa-a170-163688dcd1d4

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_image_pow_eq_preimage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x5
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x5
theorem _root_.solution (ϖ : Kˣ) (N : ℕ) (S : Set K) :
    (fun x => (ϖ : K) ^ N * x) ⁻¹' S = (fun r => ((ϖ⁻¹ : Kˣ) : K) ^ N * r) '' S := by
  have := image_pow_eq_preimage ϖ⁻¹ N S
  rw [inv_inv] at this
  exact this.symm
end Formalism.FourierDecayAlt.P.A6x5
