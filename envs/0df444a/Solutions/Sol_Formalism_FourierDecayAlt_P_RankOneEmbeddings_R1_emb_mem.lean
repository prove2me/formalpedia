-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.emb_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:24:21.962842+00:00
-- url     : https://prove2.me/submissions/1e466e80-f493-46c5-977a-651c7f0a90a9

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
theorem _root_.solution (UF : UWbFacts) {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hsu : ∀ ζ, (s ζ)ᴴ * Hb k * s ζ = Hb k) (ζ : ℂ) : embWb k r (s ζ) ∈ UWb k r := by
  rw [(UF k r).1]
  exact ⟨s ζ, hsu ζ, rfl⟩
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
