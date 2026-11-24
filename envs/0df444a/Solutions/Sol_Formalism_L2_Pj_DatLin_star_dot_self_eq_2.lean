-- Prove2me | solution 2 for Formalism.L2.Pj.DatLin.star_dot_self_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:15:48.775748+00:00
-- url     : https://prove2.me/submissions/067664f9-76b0-492f-b855-8b64d8bd2012

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open Matrix Complex
variable {m : Type} [Fintype m] [DecidableEq m]
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution (w : m → ℂ) : star w ⬝ᵥ w = ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, Complex.star_def]
end Formalism.L2.Pj.DatLin
