-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.wtX_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:07:35.590293+00:00
-- url     : https://prove2.me/submissions/537794d0-b4b1-46b6-956f-466a06ba84c4

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Vanish
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKillsDegreeZero
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dEarly_nonneg
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


section
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
section LatW
variable {p : ℕ} [Fact p.Prime] {K s : ℕ}
variable (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ)
private theorem mul_norm_sq_sum_le_re_inner_of_orthogonal_eigen {K r : ℕ} (LL : Letters (K + 1)) (m : Fin (K + 1) × Fin r →₀ ℕ) (c' : Fin r)
    (hv : LL.vec (Fin.last K) = true) (o : ℕ) (hm : MultiDeg (setLast LL o) m) :
    -dEarly LL ≤ ∑ i : Fin (K + 1), (if LL.vec i = true then (m (i, c') : ℤ) else -(m (i, c') : ℤ)) ∧
      ∑ i : Fin (K + 1), (if LL.vec i = true then (m (i, c') : ℤ) else -(m (i, c') : ℤ)) ≤ dEarly LL + o := by
  have hle : ∀ j : Fin K, m (Fin.castSucc j, c') ≤ LL.deg (Fin.castSucc j) := by
    intro j
    have hs : ∑ a, m (Fin.castSucc j, a) = LL.deg (Fin.castSucc j) := by
      have h := hm (Fin.castSucc j)
      simpa [setLast, Function.update_apply, (Fin.castSucc_lt_last j).ne] using h
    rw [← hs]
    exact Finset.single_le_sum (f := fun a => m (Fin.castSucc j, a)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c')
  have hlo : m (Fin.last K, c') ≤ o := by
    have hs : ∑ a, m (Fin.last K, a) = o := by
      have h := hm (Fin.last K)
      simpa [setLast] using h
    rw [← hs]
    exact Finset.single_le_sum (f := fun a => m (Fin.last K, a)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c')
  have hdE : dEarly LL = ∑ j : Fin K, (LL.deg (Fin.castSucc j) : ℤ) := by
    unfold dEarly
    rw [Fin.sum_univ_castSucc, if_pos rfl, add_zero]
    exact Finset.sum_congr rfl fun j _ => if_neg (Fin.castSucc_lt_last j).ne
  rw [hdE, Fin.sum_univ_castSucc, hv, if_pos rfl]
  have h1 : ∀ j : Fin K, -(LL.deg (Fin.castSucc j) : ℤ) ≤
      (if LL.vec (Fin.castSucc j) = true then (m (Fin.castSucc j, c') : ℤ) else -(m (Fin.castSucc j, c') : ℤ)) := by
    intro j
    have := hle j
    split_ifs <;> omega
  have h2 : ∀ j : Fin K,
      (if LL.vec (Fin.castSucc j) = true then (m (Fin.castSucc j, c') : ℤ) else -(m (Fin.castSucc j, c') : ℤ)) ≤
        (LL.deg (Fin.castSucc j) : ℤ) := by
    intro j
    have := hle j
    split_ifs <;> omega
  have s1 := Finset.sum_le_sum (s := univ) fun j _ => h1 j
  have s2 := Finset.sum_le_sum (s := univ) fun j _ => h2 j
  rw [Finset.sum_neg_distrib] at s1
  have h3 : (0 : ℤ) ≤ m (Fin.last K, c') := by positivity
  have h4 : (m (Fin.last K, c') : ℤ) ≤ o := by exact_mod_cast hlo
  constructor <;> linarith
end LatW
end Formalism.InvariantFactorPaths.L4
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K s : ℕ}
variable (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (hv : LL.vec (Fin.last K) = true) (m : Fin (K + 1) × Fin (s + 1) →₀ ℕ) (o : ℕ)
    (ho : (o : ℤ) ≤ c + dEarly LL) (hm : MultiDeg (setLast LL o) m) (i : Fin (s + 1)) :
    -dEarly LL ≤ wtX LL c m i ∧ wtX LL c m i ≤ 2 * dEarly LL + c := by
  have hd0 := dEarly_nonneg LL
  induction i using Fin.cases with
  | zero =>
    simp only [wtX, Fin.cases_zero]
    have h := hm (Fin.last K)
    have hl : ∑ a, m (Fin.last K, a) = o := by simpa [setLast] using h
    have hz : (∑ a, (m (Fin.last K, a) : ℤ)) = (o : ℤ) := by exact_mod_cast hl
    rw [hz]
    constructor <;> omega
  | succ i' =>
    simp only [wtX, Fin.cases_succ, wt, Fin.is_lt, ↓reduceIte]
    have h := mul_norm_sq_sum_le_re_inner_of_orthogonal_eigen LL m (Fin.castSucc i') hv o hm
    constructor <;> linarith [h.1, h.2]
end Formalism.InvariantFactorPaths.L4
