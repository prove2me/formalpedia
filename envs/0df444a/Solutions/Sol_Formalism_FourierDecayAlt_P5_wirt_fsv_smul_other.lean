-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.wirt_fsv_smul_other
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:09:44.584084+00:00
-- url     : https://prove2.me/submissions/11bc3f73-6757-4a6b-9be4-8ef666759bc7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtFsvOther
import Theorems.Thm_Formalism_FourierDecayAlt_P5_hasFDerivAt_fsv_other

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
theorem _root_.solution (t : ℂ) {l l' : Fin m} (hl : l' ≠ l) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hφ : DifferentiableAt ℝ φ c) :
    wirt l' (fun c' => fsv t (c' l) • φ c') c = fsv t (c l) • wirt l' φ c ∧
    wirtBar l' (fun c' => fsv t (c' l) • φ c') c = fsv t (c l) • wirtBar l' φ c := by
  obtain ⟨D, hD, hD0⟩ := hasFDerivAt_fsv_other t l c
  have hf : fderiv ℝ (fun c' => fsv t (c' l) • φ c') c = fsv t (c l) • fderiv ℝ φ c + D.smulRight (φ c) :=
    (hD.smul hφ.hasFDerivAt).fderiv
  have e : ∀ v : ℂ, fderiv ℝ (fun c' => fsv t (c' l) • φ c') c (Pi.single l' v) =
      fsv t (c l) • fderiv ℝ φ c (Pi.single l' v) := by
    intro v
    rw [hf, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      hD0 l' hl v, zero_smul, add_zero]
  constructor
  · unfold Formalism.QuantumDeterminants.wirt
    rw [e, e, smul_comm Complex.I (fsv t (c l)), ← smul_sub, smul_comm]
  · unfold Formalism.QuantumDeterminants.wirtBar
    rw [e, e, smul_comm Complex.I (fsv t (c l)), ← smul_add, smul_comm]
end Formalism.FourierDecayAlt.P5
