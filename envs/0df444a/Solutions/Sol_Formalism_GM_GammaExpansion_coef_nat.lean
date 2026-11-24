-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.coef_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:50.450468+00:00
-- url     : https://prove2.me/submissions/4a3604de-57b1-4167-8317-66ffa75ce247

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last


section
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {R σ : Type} [CommSemiring R]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ]
variable {r : ℕ} (w e : Fin r → σ)
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open Polynomial Finset
section
variable {k : Type} [Field k] [CharZero k]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open Finset
section
variable {k : Type} [Field k] [CharZero k]
private theorem descF_add_lemma_6 (A a b : ℕ) :
    A.descFactorial (a + b) = A.descFactorial a * (A - a).descFactorial b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, Nat.descFactorial_succ, ih, Nat.descFactorial_succ, Nat.sub_sub]
    ring
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {R σ : Type} [CommSemiring R]
end
section
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end
section
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
end
section
variable (p : ℕ) [Fact p.Prime]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM
open MvPolynomial Finset
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open Finset
variable {k : Type} [Field k] [CharZero k]
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (A o s j : ℕ) (hsj : s + j ≤ o) :
    A.choose o * o.factorial =
      (A - s - j).choose (o - s - j) * (o - s - j).factorial * ((A - s).choose j * j.factorial) *
        A.descFactorial s := by
  have e1 : ∀ n m : ℕ, n.choose m * m.factorial = n.descFactorial m := fun n m => by
    rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
  rw [e1, e1, e1]
  have ho : o = s + (j + (o - s - j)) := by omega
  conv_lhs => rw [ho]
  rw [descF_add_lemma_6, descF_add_lemma_6, Nat.sub_sub]
  ring
end Formalism.GM.GammaExpansion
