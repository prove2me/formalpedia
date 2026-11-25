-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.zb_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:49:09.1388+00:00
-- url     : https://prove2.me/submissions/d7db4b26-de36-4078-8795-c85711bf5a45

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpk_h
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_uh_inv_eq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
variable (z z' : Fin (2 * r + k + 1) → ℂ)
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution {g : Mx k r} (hg : g ∈ Glev k r i) : star (zetaL k r z z' i g) = zbF k r z z' i g := by
  have h1 : g⁻¹ * g = 1 := by
    rw [uh_inv_eq hg.1]
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hg.1
    calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hpk_sq']
  have h2 : g * g⁻¹ = 1 := mul_eq_one_comm.1 h1
  have hs : ∀ u w : Fin (2 * r + k + 1) → ℂ, star (herm (Hpk k r) u w) = herm (Hpk k r) w u := by
    intro u w
    unfold herm
    rw [← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, hpk_h, ← Matrix.dotProduct_mulVec]
  unfold zetaL zbF
  rw [hs, ← herm_UH hg.1 (g⁻¹ *ᵥ fvec k r z i), Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
end Formalism.FourierDecayAlt.P.Qx5
