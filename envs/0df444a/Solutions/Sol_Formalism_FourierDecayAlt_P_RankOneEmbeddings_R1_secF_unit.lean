-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.secF_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:01:59.794833+00:00
-- url     : https://prove2.me/submissions/6d644863-54b0-4db8-b0ca-f5376b33ae90

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_secF_on
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_secF_off

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
    (hsec : IsSection k r z z' μsec) (ζ : ℂ) :
    (secF k r z z' μsec ζ)ᴴ * Hb k * secF k r z z' μsec ζ = Hb k := by
  have hs := hsec
  unfold IsSection at hs
  by_cases h : ζ ∈ Om k r z z'
  · rw [secF_on h]
    exact (hs.2 ζ h).1
  · rw [secF_off h]
    simp
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
