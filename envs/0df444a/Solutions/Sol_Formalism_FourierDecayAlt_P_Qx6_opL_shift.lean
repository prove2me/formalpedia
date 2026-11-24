-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.opL_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:56:32.940329+00:00
-- url     : https://prove2.me/submissions/9a83bb0b-4060-4c28-a4e5-b1d339e7e9c7

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (a : Fin r) (j : Fin 6) {f : (Fin r → ℂ) → E} {c c' : Fin r → ℂ} (hc : c ∈ OmX r)
    (hc' : c' ∈ OmX r) (ha : c a = c' a) (hev : ∀ᶠ x in 𝓝 c', f x = f (x + (c - c'))) :
    opL a j f c = opL a j f c' := by
  have h0 : f c' = f c := by simpa using hev.self_of_nhds
  have hfd : fderiv ℝ f c' = fderiv ℝ f c := by
    have e : f =ᶠ[𝓝 c'] fun x => f (x + (c - c')) := hev
    rw [e.fderiv_eq, fderiv_comp_add_right]
    simp
  fin_cases j
  · show pOp a f c = pOp a f c'
    unfold pOp wirt
    rw [if_pos hc, if_pos hc', hfd, ha]
  · show c a • f c = c' a • f c'
    rw [h0, ha]
  · show (c a)⁻¹ • f c = (c' a)⁻¹ • f c'
    rw [h0, ha]
  · show pbOp a f c = pbOp a f c'
    unfold pbOp wirtBar
    rw [if_pos hc, if_pos hc', hfd, ha]
  · show star (c a) • f c = star (c' a) • f c'
    rw [h0, ha]
  · show (star (c a))⁻¹ • f c = (star (c' a))⁻¹ • f c'
    rw [h0, ha]
end Formalism.FourierDecayAlt.P.Qx6
