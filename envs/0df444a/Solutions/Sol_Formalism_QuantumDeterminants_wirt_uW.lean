-- Prove2me | solution 1 for Formalism.QuantumDeterminants.wirt_uW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:40:54.1137+00:00
-- url     : https://prove2.me/submissions/643a2391-b457-4c84-85bb-f516cb821c7e

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_isOpen_OmX
import Theorems.Thm_Formalism_QuantumDeterminants_uW_hasLineDerivAt
import Theorems.Thm_Formalism_QuantumDeterminants_uW_contDiffOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
variable {m : ℕ}
namespace Formalism.QuantumDeterminants
theorem _root_.solution (l : Fin m) (x : Fin m → ℂ) (hx : x ∈ OmX m) : wirt l (uW l) x = 0 := by
  have hd : DifferentiableAt ℝ (uW l) x :=
    ((uW_contDiffOn l).differentiableOn (by simp)).differentiableAt ((isOpen_OmX m).mem_nhds hx)
  have hxl : x l ≠ 0 := hx l
  set K : ℂ := (((∏ k ∈ Finset.univ.erase l, Complex.normSq (x k))⁻¹ : ℝ) : ℂ) with hK
  unfold wirt
  rw [← hd.lineDeriv_eq_fderiv, ← hd.lineDeriv_eq_fderiv, (uW_hasLineDerivAt l x hxl 1).lineDeriv,
    (uW_hasLineDerivAt l x hxl Complex.I).lineDeriv]
  simp only [star_one, Complex.star_def, Complex.conj_I, smul_eq_mul]
  linear_combination (-(1 / 2) * K / ((starRingEnd ℂ) (x l)) ^ 2) * Complex.I_mul_I
end Formalism.QuantumDeterminants
