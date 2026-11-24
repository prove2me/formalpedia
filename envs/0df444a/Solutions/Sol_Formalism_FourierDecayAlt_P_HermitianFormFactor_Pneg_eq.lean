-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Pneg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:17:00.878998+00:00
-- url     : https://prove2.me/submissions/61b11b7c-1478-4750-9c3c-f2dc42cbf437

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor

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
    (F : Frame (Hpk k r) Ep Em) : Pneg k r = Em * Emᴴ := by
  unfold Pneg
  rw [← F.sum, ← F.diff]
  have h : Ep * Epᴴ + Em * Emᴴ - (Ep * Epᴴ - Em * Emᴴ) = (2 : ℂ) • (Em * Emᴴ) := by
    rw [two_smul]; abel
  rw [h, smul_smul]
  norm_num
end Formalism.FourierDecayAlt.P.HermitianFormFactor
