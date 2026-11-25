-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.JmuHC.fdegHC_addI_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:28:23.968824+00:00
-- url     : https://prove2.me/submissions/b58c617c-4b13-4e7b-b6bf-36bdf8229980

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJmuHC
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_JmuHC_numHC_addI_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.JmuHC
open Finset
variable {n : ℕ}
namespace Formalism.FourierDecayAlt.P.CutBP.JmuHC
theorem _root_.solution (x : Fin n → ℝ) (hinj : Function.Injective x) (hint : ∀ a b, ∃ m : ℤ, x a - x b = m)
    (I : Finset (Fin n)) :
    PI.UpqRep.fdegHC (fun i => x i + if i ∈ I then 1 else 0) ≤ (n : ℝ) ^ I.card * PI.UpqRep.fdegHC x := by
  unfold PI.UpqRep.fdegHC
  have hD : 0 ≤ ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) :=
    prod_nonneg fun a _ => prod_nonneg fun b hb => by
      have := (mem_filter.1 hb).2
      have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast this
      linarith
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right (numHC_addI_le x hinj hint I) hD
end Formalism.FourierDecayAlt.P.CutBP.JmuHC
