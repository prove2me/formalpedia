-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.integ_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:14:03.528395+00:00
-- url     : https://prove2.me/submissions/2f8fab8e-8da0-4527-86ce-514c558edc3b

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Theorems.Thm_Formalism_IndefR_Fin_Four_integ_congr
import Theorems.Thm_Formalism_IndefR_Fin_Four_integ_cmul
import Theorems.Thm_Formalism_IndefR_Fin_Four_integ_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Finset
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W : Type*} [AddCommGroup W]
variable {H : AddSubgroup W} (hfin : ∀ k, 0 < k → Finite (Qt k H))
include hfin
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {k : ℕ} (hk : 0 < k) {g : W → ℂ} (hg : IsInv k H g) {v : W} (hv : v ∈ H) {ζ : ℂ}
    (hζ : ζ ≠ 1) (htw : ∀ t ∈ H, g (t + v) = ζ * g t) : integ H g = 0 := by
  have h1 := integ_shift hfin hk hg hv
  rw [integ_congr hfin htw, integ_cmul hfin hk hg] at h1
  have : (ζ - 1) * integ H g = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hζ
  · exact h
end Formalism.IndefR.Fin.Four
