-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.incl_xv_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:36.480379+00:00
-- url     : https://prove2.me/submissions/12483b20-21f3-4670-96d7-841578edd093

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Theorems.Thm_Formalism_L2_Pj_GenSect_xv_of_not
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
theorem _root_.solution (j₀ : Fin m) (i : Fin D) (k : Fin m) :
    incl (Ω := Ω) j₀ (xv j₀ (i.succ, k)) = if k = j₀ then 0 else X (i.succ, k) := by
  by_cases h : k = j₀
  · have hz : Zs j₀ (i.succ, k) := by
      unfold Zs
      exact ⟨Fin.succ_ne_zero i, h⟩
    rw [xv_of_Z hz, map_zero, if_pos h]
  · have hz : ¬ Zs j₀ (i.succ, k) := by
      unfold Zs
      exact fun hz => h hz.2
    rw [xv_of_not hz, if_neg h, incl, rename_X]
    try rfl
end Formalism.L2.Pj.GenSect
