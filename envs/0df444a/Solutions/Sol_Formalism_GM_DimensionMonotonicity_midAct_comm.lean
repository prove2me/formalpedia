-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.midAct_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:09.082953+00:00
-- url     : https://prove2.me/submissions/fe8726f5-cf6b-4825-b6f5-9b7984e02789

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
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
namespace Formalism.GM.DimensionMonotonicity
open Finset
namespace GlW
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlW
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open Finset
variable {r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open Finset
namespace GlW
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlW
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open Finset
namespace GlW
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlW
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
section Ops
variable {K : Type} [CommRing K] {σ : Type} [DecidableEq σ]
end Ops
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
section W
variable {K : Type} [CommRing K] {σ : Type} [DecidableEq σ] {M : Type} [AddCommGroup M]
end W
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
private theorem top_comm_lemma (LL : Letters N) (i i' : Fin N) (hne : i ≠ i') (a b c d : Fin r)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    Formalism.GM.FrozenVariableComponents.top p LL i a b (Formalism.GM.FrozenVariableComponents.top p LL i' c d F) =
      Formalism.GM.FrozenVariableComponents.top p LL i' c d (Formalism.GM.FrozenVariableComponents.top p LL i a b F) := by
  have key : ∀ (x y x' y' : Fin N × Fin r), x.1 = i → y.1 = i → x'.1 = i' → y'.1 = i' →
      ∀ G : MvPolynomial (Fin N × Fin r) ℚ_[p],
      X x * pderiv y (X x' * pderiv y' G) = X x' * pderiv y' (X x * pderiv y G) := by
    intro x y x' y' hx hy hx' hy' G
    have h := XD_comm x y x' y' G
    rw [if_neg (fun h' => hne (by rw [← hy, h', hx'])), if_neg (fun h' => hne (by rw [← hx, ← h', hy'])),
      sub_zero, sub_eq_zero] at h
    exact h
  unfold Formalism.GM.FrozenVariableComponents.top
  by_cases hv : LL.vec i <;> by_cases hv' : LL.vec i' <;>
    simp only [hv, hv', if_true, if_false, ite_true, ite_false, Bool.false_eq_true, LinearMap.neg_apply,
      LinearMap.comp_apply, LinearMap.mulLeft_apply, map_neg, mul_neg, neg_neg, neg_inj] <;>
    first
      | exact key _ _ _ _ rfl rfl rfl rfl F
      | exact key (i, a) (i, b) (i', c) (i', d) rfl rfl rfl rfl F
      | exact key (i, a) (i, b) (i', d) (i', c) rfl rfl rfl rfl F
      | exact key (i, b) (i, a) (i', c) (i', d) rfl rfl rfl rfl F
      | exact key (i, b) (i, a) (i', d) (i', c) rfl rfl rfl rfl F
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
section Comparison₂
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
end Comparison₂
section Tie2
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
end Tie2
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution (LL : Letters N) (J j0 : ℕ) (c d c' d' : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    midAct p LL J j0 c d (glAct p LL J c' d' F) = glAct p LL J c' d' (midAct p LL J j0 c d F) := by
  unfold midAct glAct
  simp only [LinearMap.sum_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  by_cases h1 : J ≤ (i : ℕ) ∧ (i : ℕ) < j0
  · by_cases h2 : (i' : ℕ) < J
    · have hne : i ≠ i' := fun h => by subst h; omega
      rw [if_pos h1, if_pos h2]
      exact top_comm_lemma LL i i' hne c d c' d' F
    · simp [h2]
  · simp [h1]
end Formalism.GM.DimensionMonotonicity
