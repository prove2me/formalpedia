-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.pbOp_fsv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:29:22.853684+00:00
-- url     : https://prove2.me/submissions/aaafaf38-eb7a-4bb8-91a8-74b722a068c0

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Theorems.Thm_Formalism_FourierDecayAlt_P5_wirt_fsv_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (t : ℂ) (l : Fin m) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hd : c ∈ OmX m → DifferentiableAt ℝ φ c) (h0 : c ∉ OmX m → φ c = 0) :
    pbOp l (fun c' => fsv (-t) (c' l) • φ c') c =
      fsv (-t) (c l) • pbOp l φ c + conj t • fsv (-t) (c l) • (star (c l) • φ c) := by
  unfold pbOp
  by_cases h : c ∈ OmX m
  · rw [if_pos h, if_pos h, (wirt_fsv_smul (-t) l φ c (hd h)).2]
    simp only [map_neg, neg_neg, Complex.star_def]
    module
  · rw [if_neg h, if_neg h, h0 h]
    simp
end Formalism.FourierDecayAlt.P5
