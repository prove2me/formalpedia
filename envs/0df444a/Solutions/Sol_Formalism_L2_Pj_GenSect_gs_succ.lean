-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.gs_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:32.734846+00:00
-- url     : https://prove2.me/submissions/0b411bd3-aab8-483e-9d94-621ede8f3d1c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Theorems.Thm_Formalism_L2_Pj_GenSect_xv_of_Z

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ)
variable {K Ω D m}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution (x : Fin m → Ω) (j₀ : Fin m) (i : Fin D) (j : Fin m) :
    gs x j₀ (i.succ, j) = xv j₀ (i.succ, j) +
      if j = j₀ then -∑ k, xv j₀ (i.succ, k) * C (rr x j₀ k) else 0 := by
  by_cases h : j = j₀
  · have hz : Zs j₀ (i.succ, j) := by
      unfold Zs
      exact ⟨Fin.succ_ne_zero i, h⟩
    rw [gs, if_pos hz, xv_of_Z hz, if_pos h, zero_add]
    try rfl
  · have hz : ¬ Zs j₀ (i.succ, j) := by
      unfold Zs
      exact fun hz => h hz.2
    rw [gs, if_neg hz, if_neg h, add_zero]
end Formalism.L2.Pj.GenSect
