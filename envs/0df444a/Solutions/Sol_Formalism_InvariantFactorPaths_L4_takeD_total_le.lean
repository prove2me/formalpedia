-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.takeD_total_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:18:13.386441+00:00
-- url     : https://prove2.me/submissions/1aa7067e-7b21-4184-adac-48b2212e8991

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_FinalM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundUnconditionalOfSat
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
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
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
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {N : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (a : ℕ) (Yl n₀ dd : Fin T.t → ℕ)
    (hS : ∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i)
    (hdeg : ∀ x, (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))).deg x ≤ 2 * a)
    (n : Fin T.t → ℕ) (hn : ∀ i, n i ≤ n₀ i + dd i * (Yl i - 1)) (i : Fin T.t) :
    ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ 2 * a := by
  obtain ⟨hlt, -, -⟩ := hadm.2.1 i
  have htie : (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))).deg ⟨T.pos i + 1, hlt⟩
      = n₀ i + dd i * (Yl i - 1) := by
    have hex : ∃ j, T.pos j + 1 = T.pos i + 1 := ⟨i, rfl⟩
    simp only [Letters.setTies]
    rw [dif_pos hex]
    have hc := Classical.choose_spec hex
    have hj : Classical.choose hex = i := hadm.1.injective (by omega)
    rw [hj]
  have hS2 : T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ 2 * a := by
    have h1 := hdeg ⟨T.pos i + 1, hlt⟩
    rw [htie] at h1
    have h2 := hS i
    omega
  refine le_trans ?_ hS2
  unfold Letters.total TieData.S
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega : T.pos i + 1 ≤ N)) (fun _ _ _ => Nat.zero_le _))
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : j < T.pos i + 1 := Finset.mem_range.1 hj
  have hjN : j < N := by omega
  rw [dif_pos hj1, dif_pos hjN, if_pos (by simp; omega)]
  simp only [Letters.takeD, Letters.setTies, dif_pos hjN]
  split_ifs with h
  · exact hn _
  · exact le_rfl
end Formalism.InvariantFactorPaths.L4
