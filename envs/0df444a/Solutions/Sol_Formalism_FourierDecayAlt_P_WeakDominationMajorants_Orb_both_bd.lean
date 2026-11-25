-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.both_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:44:10.923975+00:00
-- url     : https://prove2.me/submissions/59865d56-9659-46f7-a867-1a46ea9bada9

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_closedN
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_x_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_gN_n_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_gN_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_Zm_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_ld_conjT
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_det_conjT
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_xinv_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_closedN
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_inv


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
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakDominationMajorants Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
theorem _root_.solution {Γ δ : ℝ} {g n n' : Mat k r} (hΓ : 1 ≤ Γ) (hδ : 0 < δ) (hg : g ∈ GV k r) (hgΓ : gN g ≤ Γ)
    (hld : ∀ b, δ ≤ ‖ld (Zm g) b‖) (hdet : δ ≤ ‖(Zm g).det‖) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) :
    gN n ≤ ((2 * r + k + 1 : ℕ) : ℝ) * c13 k r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r + 1) ∧
    gN n' ≤ ((2 * r + k + 1 : ℕ) : ℝ) * c13 k r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r + 1) := by
  refine ⟨gN_n_bd hΓ hδ hg hgΓ hld hdet hn hn', ?_⟩
  have hgi : g⁻¹ ∈ GV k r := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg
  have h := gN_n_bd (g := g⁻¹) (n := n') (n' := n) hΓ hδ hgi (by rw [gN_inv hg]; exact hgΓ)
    (fun b => by rw [Zm_inv hg, ld_conjT]; exact hld b) (by rw [Zm_inv hg, det_conjT]; exact hdet) hn' hn
  have hnn : (n⁻¹)⁻¹ = n := Matrix.nonsing_inv_nonsing_inv n (closedN.unit n hn)
  have e : n'⁻¹ * g⁻¹ * n = (n⁻¹ * g * n')⁻¹ := by rw [xinv_eq hn hn', hnn]
  rw [e, gN_inv (x_mem hg hn hn')] at h
  exact h
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
