-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.wirt_fsv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:06:39.741643+00:00
-- url     : https://prove2.me/submissions/b6c44489-1807-4e37-83d6-ab1604c4751a

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Theorems.Thm_Formalism_FourierDecayAlt_P5_hasFDerivAt_fsv

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
    (hφ : DifferentiableAt ℝ φ c) :
    wirt l (fun c' => fsv t (c' l) • φ c') c = fsv t (c l) • wirt l φ c + (t * fsv t (c l)) • φ c ∧
    wirtBar l (fun c' => fsv t (c' l) • φ c') c =
      fsv t (c l) • wirtBar l φ c + (-(conj t) * fsv t (c l)) • φ c := by
  obtain ⟨D, hD, h1, hI⟩ := hasFDerivAt_fsv t l c
  have hP : HasFDerivAt (fun c' => fsv t (c' l) • φ c') (fsv t (c l) • fderiv ℝ φ c + D.smulRight (φ c)) c :=
    hD.smul hφ.hasFDerivAt
  unfold wirt wirtBar
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, h1, hI, smul_add, smul_sub, smul_smul, ← mul_assoc, Complex.I_mul_I]
  constructor <;> module
end Formalism.FourierDecayAlt.P5
