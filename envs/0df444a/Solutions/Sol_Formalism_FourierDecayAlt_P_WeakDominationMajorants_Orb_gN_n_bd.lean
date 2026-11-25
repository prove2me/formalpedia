-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_n_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:27:57.193492+00:00
-- url     : https://prove2.me/submissions/11eecd4c-1468-4c88-a0da-0621e8fc780c

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_norm_inv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_closedN
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_n_mem_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_n_inv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_gN_le_of_ent
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_orbit_constant_thirteen_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_ninv_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_closedN
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_nonneg


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
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakDominationMajorants Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
variable {k r : ℕ}
variable {Γ δ : ℝ} {g n n' : Mat k r}
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
theorem _root_.solution (hΓ : 1 ≤ Γ) (hδ : 0 < δ) (hg : g ∈ GV k r) (hgΓ : gN g ≤ Γ) (hld : ∀ b, δ ≤ ‖ld (Zm g) b‖)
    (hdet : δ ≤ ‖(Zm g).det‖) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) :
    gN n ≤ ((2 * r + k + 1 : ℕ) : ℝ) * c13 k r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r + 1) := by
  have hinvG : n⁻¹ ∈ GV k r := n_mem_G (n_inv_mem hn)
  have hnn : n = (n⁻¹)⁻¹ := (Matrix.nonsing_inv_nonsing_inv n (closedN.unit n hn)).symm
  have hX : 0 ≤ gN (n⁻¹ * g * n') ^ (2 * r + 1) := by have := gN_nonneg (n⁻¹ * g * n'); positivity
  have := orbit_constant_thirteen_nonneg (k := k) (r := r) hΓ hδ
  have h := gN_le_of_ent n (c13 k r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r + 1)) (by positivity) (fun i j => by
    conv_lhs => rw [hnn]
    rw [norm_inv_apply hinvG]
    exact ninv_bd hΓ hδ hg hgΓ hld hdet hn hn' _ _)
  rw [mul_assoc]; exact h
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
