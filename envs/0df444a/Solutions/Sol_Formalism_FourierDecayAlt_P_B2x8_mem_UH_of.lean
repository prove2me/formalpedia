-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.mem_UH_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:25:04.618441+00:00
-- url     : https://prove2.me/submissions/4c958ba0-5cbb-4313-a623-21f4f8df1e8e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_tk_herm_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_tk_herm_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution [DecidableEq ι] {g : Matrix ι ι ℂ} (hg : ∀ u v, herm H (g *ᵥ u) (g *ᵥ v) = herm H u v) : g ∈ UH H := by
  show gᴴ * H * g = H
  ext i j
  rw [← tk_herm_single (gᴴ * H * g) i j, ← tk_herm_conjTranspose, hg, tk_herm_single]
end Formalism.FourierDecayAlt.P.B2x8
