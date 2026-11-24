-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.glAct_pow_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:30.174362+00:00
-- url     : https://prove2.me/submissions/ae5eefa8-76c9-4277-9bd8-4b90782270dd

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
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
private theorem glAct_leib_lemma {N r : ℕ} {p : ℕ} [Fact p.Prime] (LL : Letters N) (j : ℕ) (c d : Fin r)
    (x y : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j c d (x * y) = x * glAct p LL j c d y + y * glAct p LL j c d x := by
  unfold glAct
  simp only [LinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Derivation.leibniz] <;> ring
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
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution {N r : ℕ} {p : ℕ} [Fact p.Prime] (LL : Letters N) (j : ℕ) (c d : Fin r)
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : glAct p LL j c d x = 0) (k : ℕ) :
    glAct p LL j c d (x ^ k) = 0 := by
  induction k with
  | zero => simpa using glAct_leib_lemma LL j c d (1 : MvPolynomial (Fin N × Fin r) ℚ_[p]) 1
  | succ k ih => rw [pow_succ, glAct_leib_lemma, ih, hx, mul_zero, mul_zero, add_zero]
end Formalism.GM.DimensionMonotonicity
