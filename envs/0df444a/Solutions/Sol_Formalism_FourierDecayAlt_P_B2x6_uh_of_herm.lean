-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x6.uh_of_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:13:57.290232+00:00
-- url     : https://prove2.me/submissions/3a3a353e-b470-4cde-abf2-f39dee7b59fe

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_bvec_right


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x6
theorem _root_.solution {m : ℕ} (H g : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ u w, herm H (g *ᵥ u) (g *ᵥ w) = herm H u w) : g ∈ UH H := by
  show gᴴ * H * g = H
  ext i j
  have h1 := h (Pi.single j 1) (Pi.single i 1)
  have h2 : ∀ u w, herm H (g *ᵥ u) (g *ᵥ w) = herm (gᴴ * H * g) u w := by
    intro u w
    rw [herm, herm, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  rw [h2, ggHerm_bvec_right, ggHerm_bvec_right] at h1
  simpa using h1
end Formalism.FourierDecayAlt.P.B2x6
