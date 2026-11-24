-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.nu_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:26:02.251583+00:00
-- url     : https://prove2.me/submissions/4f388df5-0fae-40db-9a76-9a1c42b6b4b9

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
variable (k : ℕ)
namespace Formalism.FourierDecayAlt.P.SettingConstruction
theorem _root_.solution (w s : ℂ) (x : Fin (k + 1) → ℂ) :
    nu k w s *ᵥ x = x + x 0 • ((star w - 1) • Pi.single 0 1 + s • Pi.single (Fin.last k) 1) +
      x (Fin.last k) • (s • Pi.single 0 1 + (w - 1) • Pi.single (Fin.last k) 1) := by
  have key : ∀ (a : Fin (k + 1) → ℂ) (j : Fin (k + 1)), Matrix.vecMulVec a (Pi.single j 1) *ᵥ x = x j • a := by
    intro a j; funext i
    simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.single_apply, mul_comm]
  rw [nu, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, key, key]
end Formalism.FourierDecayAlt.P.SettingConstruction
