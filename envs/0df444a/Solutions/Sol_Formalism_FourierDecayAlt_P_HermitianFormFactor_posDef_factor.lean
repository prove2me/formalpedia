-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.posDef_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:35:01.101546+00:00
-- url     : https://prove2.me/submissions/589a8f0a-144a-4151-8b5f-507389930630

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_mp

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
open scoped MatrixOrder
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution {T : Matrix Q Q ℂ} (hT : T.PosDef) : ∃ a : Matrix Q Q ℂ, IsUnit a.det ∧ T = aᴴ * a := by
  obtain ⟨a, ha⟩ : ∃ a : Matrix Q Q ℂ, T = aᴴ * a := by
    first
    | exact ⟨CFC.sqrt T, by
        have h0 : 0 ≤ T := Matrix.nonneg_iff_posSemidef.mpr hT.posSemidef
        have hs : (CFC.sqrt T)ᴴ = CFC.sqrt T := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)
        rw [hs, CFC.sqrt_mul_sqrt_self T h0]⟩
    | exact Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hT.posSemidef
    | exact Matrix.posSemidef_iff_eq_transpose_mul_self.mp hT.posSemidef
    | exact Matrix.PosSemidef.exists_eq_conjTranspose_mul_self hT.posSemidef
  refine ⟨a, ?_, ha⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  have hd := hT.det_pos
  rw [ha, Matrix.det_mul, h0, mul_zero] at hd
  exact lt_irrefl _ hd
end Formalism.FourierDecayAlt.P.HermitianFormFactor
