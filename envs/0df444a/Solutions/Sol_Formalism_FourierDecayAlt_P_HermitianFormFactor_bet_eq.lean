-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.bet_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:40:55.673331+00:00
-- url     : https://prove2.me/submissions/5dad1157-2d43-4a8d-bd60-725c8fca6e33

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_gN_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Ppos_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Pneg_eq

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
theorem _root_.solution {k r : ℕ} {Ep : Matrix (Fin (2 * r + k + 1)) P ℂ} {Em : Matrix (Fin (2 * r + k + 1)) Q ℂ}
    (F : Frame (Hpk k r) Ep Em) (g : Mat k r) : bet Ep Em g = gN (Ppos k r * g * Pneg k r) ^ 2 := by
  rw [gN_sq, Ppos_eq F, Pneg_eq F]
  unfold bet
  rw [show Ep * Epᴴ * g * (Em * Emᴴ) = Ep * (Epᴴ * g * Em) * Emᴴ by simp only [Matrix.mul_assoc]]
  generalize Epᴴ * g * Em = B
  have h : Ep * B * Emᴴ * (Ep * B * Emᴴ)ᴴ = Ep * (B * Bᴴ) * Epᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Emᴴ Em, F.mm, Matrix.one_mul]
  rw [h, Matrix.trace_mul_comm (Ep * (B * Bᴴ)) Epᴴ, ← Matrix.mul_assoc, F.pp, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
