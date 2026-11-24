-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.secF_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:24:23.2236+00:00
-- url     : https://prove2.me/submissions/a4e67812-fd1d-42f1-bb78-844db12d6582

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_secF_on

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
theorem _root_.solution {z z' : Vc k r} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hsec : IsSection k r z z' μsec) : IsSection k r z z' (secF k r z z' μsec) := by
  have hs := hsec
  unfold IsSection at hs ⊢
  refine ⟨fun i j => (hs.1 i j).congr fun ζ hζ => ?_, fun ζ hζ => ?_⟩
  · show secF k r z z' μsec ζ i j = μsec ζ i j
    rw [secF_on (μsec := μsec) (show ζ ∈ Om k r z z' from hζ)]
  · rw [secF_on (μsec := μsec) (show ζ ∈ Om k r z z' from hζ)]
    exact hs.2 ζ hζ
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
