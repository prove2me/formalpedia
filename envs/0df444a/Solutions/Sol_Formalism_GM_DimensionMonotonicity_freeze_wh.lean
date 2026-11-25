-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.freeze_wh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:03:25.860869+00:00
-- url     : https://prove2.me/submissions/c134c5e8-0af5-4a8e-89fe-4a5f3411a0c0

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity_aeval_isWH__16e475c86f62
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_wv_snoc_last
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_freezeSub_wh
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



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution (LL : Letters K) (ρ : Fin r) (n : ℕ) (hn : LL.total ≤ n) (w : Fin r → ℤ)
    (f : MvPolynomial (Fin K × Fin r) ℚ_[p]) (hfP : f ∈ Pol p r LL) (hfw : f ∈ WtSpC p LL K univ w) :
    IsWeightedHomogeneous (wv (LL.snoc n) (K + 1)) (freeze p LL ρ n f) (w - (n : ℤ) • Pi.single ρ 1) := by
  classical
  let w' : Fin K × Fin r → (Fin r → ℤ) := fun v => wv LL K v - Pi.single ρ 1
  have hf' : IsWeightedHomogeneous w' f (w - (LL.total : ℤ) • Pi.single ρ 1) := by
    intro m hm
    have hm' : m ∈ f.support := mem_support_iff.mpr hm
    have e1 : Finsupp.weight (wv LL K) m = w := by
      funext c
      rw [weight_wv]
      have h0 : m ∈ {m : Fin K × Fin r →₀ ℕ | ∀ c ∈ (univ : Finset (Fin r)), wt LL K c m = w c} :=
        (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hfw hm'
      exact h0 c (Finset.mem_univ c)
    have e2 : ∑ v, m v = LL.total := by
      have := (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hfP hm'
      rw [Fintype.sum_prod_type, Letters.total]
      exact Finset.sum_congr rfl fun i _ => this i
    have e3 : Finsupp.weight w' m = Finsupp.weight (wv LL K) m - ((∑ v, m v : ℕ) : ℤ) • Pi.single ρ 1 := by
      rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
        Finsupp.sum_fintype _ _ (by simp)]
      simp only [w', smul_sub, Finset.sum_sub_distrib]
      congr 1
      rw [← Finset.sum_smul, natCast_zsmul]
    rw [e3, e1, e2]
  have h1 := aeval_isWH' w' (wv (LL.snoc n) (K + 1)) (freezeSub p LL ρ) (fun v => freezeSub_wh LL n ρ v) hf'
  have h2 := (isWeightedHomogeneous_X ℚ_[p] (wv (LL.snoc n) (K + 1)) (Fin.last K, ρ)).pow (n - LL.total)
  have h3 := h2.mul h1
  unfold freeze
  convert h3 using 1
  rw [wv_snoc_last]
  rw [show ((n : ℤ)) = ((n - LL.total : ℕ) : ℤ) + (LL.total : ℤ) by push_cast [Nat.cast_sub hn]; ring]
  rw [add_smul, smul_neg, ← natCast_zsmul]
  abel
end Formalism.GM.DimensionMonotonicity
