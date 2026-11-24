-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.frame_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:19:05.79281+00:00
-- url     : https://prove2.me/submissions/93ac723f-c40f-4466-a39b-e0214ac23f47

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_frame_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_trace_Hpk
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
variable {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (k r : ℕ) :
    ∃ (Ep : Matrix (Fin (2 * r + k + 1)) (Fin (k + r)) ℂ) (Em : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ),
      Frame (Hpk k r) Ep Em :=
  frame_fin (hpkFacts k r).1 (hpkFacts k r).2.1 (k + r) (r + 1) (by rw [Fintype.card_fin]; omega) (trace_Hpk k r)
end Formalism.FourierDecayAlt.P.HermitianFormFactor
