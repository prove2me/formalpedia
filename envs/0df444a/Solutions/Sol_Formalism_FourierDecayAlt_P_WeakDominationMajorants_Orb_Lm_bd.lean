-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.Lm_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:55:45.979843+00:00
-- url     : https://prove2.me/submissions/0ded65a5-f4d9-4070-afae-5b6845bbda7f

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_Zm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_one_le_X
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_isLU_Lm
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_isUU_Um
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_Zm_ent
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_L_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix
open Matrix
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakDominationMajorants Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
variable {k r : ℕ}
variable {Γ δ : ℝ} {g n n' : Mat k r}
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
theorem _root_.solution (hΓ : 1 ≤ Γ) (hδ : 0 < δ) (hg : g ∈ GV k r) (hgΓ : gN g ≤ Γ) (hld : ∀ b, δ ≤ ‖ld (Zm g) b‖)
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (a b : Fin r) :
    ‖Lm n a b‖ ≤ cL r Γ δ * gN (n⁻¹ * g * n') ^ r :=
  L_bd (Lm n) (Zm g) (Um n') (isLU_Lm hn) (isUU_Um hn') hΓ hδ (one_le_X hg hn hn')
    (fun a b => (Zm_ent g a b).trans hgΓ) hld (fun a b => by rw [← Zm_mul hn hn']; exact Zm_ent _ a b) a b
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
