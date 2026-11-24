-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.rk_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:27:51.376606+00:00
-- url     : https://prove2.me/submissions/4bd5a698-0244-46e1-89ec-4cbdb1a4479f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SettingConstruction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
variable [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.SettingConstruction
theorem _root_.solution (d : ι → ℂ) (θ β : ℂ) (x : ι → ℂ) : rk H d θ β *ᵥ x = θ • x + (β * herm H x d) • d := by
  have key : ∀ v : ι → ℂ, Matrix.vecMulVec d (star d) *ᵥ v = (star d ⬝ᵥ v) • d := by
    intro v; funext i
    simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [rk, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, key,
    Matrix.one_mulVec, smul_smul]
  rfl
end Formalism.FourierDecayAlt.P.SettingConstruction
