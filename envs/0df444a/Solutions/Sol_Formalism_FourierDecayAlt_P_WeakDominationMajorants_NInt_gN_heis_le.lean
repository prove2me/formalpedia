-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationMajorants.NInt.gN_heis_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:01:06.599688+00:00
-- url     : https://prove2.me/submissions/977f3ca4-15a5-4d39-b715-93cc8c516d36

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_entry_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_hcol_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_hcol_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_hcol_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_hb_im
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_entry_le_gN
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_entry_le_gN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



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
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakDominationMajorants Formalism.FourierDecayAlt.P.WeakDominationMajorants.NInt
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.B2x6
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.NInt
theorem _root_.solution (x : HPar k r') (n' : Mat k r') :
    1 + ‖x‖ ≤ 2 * gN (heis0 k r' x * ιLev k 1 r' n') := by
  have e1 : ‖(heis0 k r' x * ιLev k 1 r' n') (iL k r') (iL k r')‖ = 1 := by
    rw [entry_L, hcol_L, norm_one]
  have h1 : (1 : ℝ) ≤ gN (heis0 k r' x * ιLev k 1 r' n') := by
    have := Formalism.FourierDecayAlt.P.Ux6.entry_le_gN (heis0 k r' x * ιLev k 1 r' n') (iL k r') (iL k r')
    rwa [e1] at this
  have h0 : 0 ≤ gN (heis0 k r' x * ιLev k 1 r' n') := le_trans zero_le_one h1
  have h2 : ‖x.1‖ ≤ gN (heis0 k r' x * ιLev k 1 r' n') := by
    refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
    have := Formalism.FourierDecayAlt.P.Ux6.entry_le_gN (heis0 k r' x * ιLev k 1 r' n') (lv k r' i) (iL k r')
    have e : (heis0 k r' x * ιLev k 1 r' n') (lv k r' i) (iL k r') = x.1 i := by
      rw [entry_L]
      have e := congrFun (hcol_res x) i
      simp only [res] at e
      exact e
    rwa [e] at this
  have h3 : ‖x.2‖ ≤ gN (heis0 k r' x * ιLev k 1 r' n') := by
    have := Formalism.FourierDecayAlt.P.Ux6.entry_le_gN (heis0 k r' x * ιLev k 1 r' n') (iF k r') (iL k r')
    rw [entry_L, hcol_F] at this
    refine le_trans ?_ this
    calc ‖x.2‖ = |(hb k r' x.1 x.2).im| := by rw [hb_im, Real.norm_eq_abs]
      _ ≤ ‖hb k r' x.1 x.2‖ := Complex.abs_im_le_norm _
  have hx : ‖x‖ = max ‖x.1‖ ‖x.2‖ := Prod.norm_def x
  rw [hx]
  have := max_le h2 h3
  linarith
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.NInt
