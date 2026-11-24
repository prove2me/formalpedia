-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.opL_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:25:02.451582+00:00
-- url     : https://prove2.me/submissions/84db2ecd-ffc3-4e78-94b2-c6d08d8413a5

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution (a : Fin r) (j : Fin 6) {f f' : (Fin r → ℂ) → E} (L : E →L[ℂ] E) {c : Fin r → ℂ}
    (hev : ∀ᶠ c' in 𝓝 c, f' c' = L (f c')) (hd : DifferentiableAt ℝ f c) :
    opL a j f' c = L (opL a j f c) := by
  have h0 : f' c = L (f c) := hev.self_of_nhds
  have hfd : ∀ v, fderiv ℝ f' c v = L (fderiv ℝ f c v) := by
    intro v
    have e : f' =ᶠ[𝓝 c] fun c' => (L.restrictScalars ℝ) (f c') := hev
    have e2 : HasFDerivAt (fun c' => (L.restrictScalars ℝ) (f c'))
        ((L.restrictScalars ℝ).comp (fderiv ℝ f c)) c := (L.restrictScalars ℝ).hasFDerivAt.comp c hd.hasFDerivAt
    rw [e.fderiv_eq, e2.fderiv]
    rfl
  fin_cases j
  · show pOp a f' c = L (pOp a f c)
    unfold pOp wirt
    split_ifs
    · simp only [hfd, map_smul, map_sub]
    · simp
  · show c a • f' c = L (c a • f c)
    rw [h0, map_smul]
  · show (c a)⁻¹ • f' c = L ((c a)⁻¹ • f c)
    rw [h0, map_smul]
  · show pbOp a f' c = L (pbOp a f c)
    unfold pbOp wirtBar
    split_ifs
    · simp only [hfd, map_smul, map_add]
    · simp
  · show star (c a) • f' c = L (star (c a) • f c)
    rw [h0, map_smul]
  · show (star (c a))⁻¹ • f' c = L ((star (c a))⁻¹ • f c)
    rw [h0, map_smul]
end Formalism.FourierDecayAlt.P.Qx3
