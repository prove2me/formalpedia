-- Prove2me | solution 1 for Formalism.MainNotions.S.Gauge.Cd.hilbert_schmidt_add_I_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:20:34.262806+00:00
-- url     : https://prove2.me/submissions/aabe691a-9b19-4793-85d5-fe7126c73dc7

import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_TraceMulConjTransposeReal
import Theorems.Thm_Formalism_MainNotions_S_Gauge_Cd_trace_mul_conjTranspose_real
import Theorems.Thm_Formalism_MainNotions_S_Gauge_Cd_hilbert_schmidt_eq_re_trace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Gauge Formalism.MainNotions.S.Gauge.Cd
variable {P Q : ℕ}
local notation "ι" => Fin P ⊕ Fin Q
namespace Formalism.MainNotions.S.Gauge.Cd
theorem _root_.solution {a b : Matrix ι ι ℂ} (ha : a ∈ Formalism.BasicNotions.lieU P Q) (hb : b ∈ Formalism.BasicNotions.lieU P Q) :
    hs2 (a + Complex.I • b) = hs2 a + hs2 b := by
  rw [hilbert_schmidt_eq_re_trace, hilbert_schmidt_eq_re_trace, hilbert_schmidt_eq_re_trace]
  have hT := trace_mul_conjTranspose_real ha hb
  have hT' : (Matrix.trace (a * bᴴ)).im = 0 := by
    have := congrArg Complex.im hT
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, smul_eq_mul, Complex.star_def, Complex.conj_I]
  have hba : Matrix.trace (b * aᴴ) = star (Matrix.trace (a * bᴴ)) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [hba, hT]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, hT']
  rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, hT']
  ring
end Formalism.MainNotions.S.Gauge.Cd
