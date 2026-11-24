-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.LatticeBasis.exists_family
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:33.315866+00:00
-- url     : https://prove2.me/submissions/e27ed605-dd28-4ba9-9e06-7a3dff905e01

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatticeBasisPolynomial
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_LatticeBasis_mem_intPol_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_LatticeBasis_exists_unit_coeff
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M
open Formalism.InvariantFactorPaths.PW.LatticeBasis
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.PW.LatticeBasis
theorem _root_.solution (d : ℕ) : ∀ (U : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])), FiniteDimensional ℚ_[p] U →
    Module.finrank ℚ_[p] U = d →
    ∃ (k : ℕ) (b : Fin k → MvPolynomial σ ℚ_[p]), LinearIndependent ℚ_[p] b ∧
      Submodule.span ℚ_[p] (Set.range b) = U ∧ (∀ i, b i ∈ IntPol p σ) ∧
      ∀ x ∈ U, x ∈ IntPol p σ → ∃ c : Fin k → ℚ_[p], (∀ i, ‖c i‖ ≤ 1) ∧ x = ∑ i, c i • b i := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro U hfd hd
    by_cases hU : U = ⊥
    · subst hU
      refine ⟨0, Fin.elim0, linearIndependent_empty_type, by simp, fun i => i.elim0, ?_⟩
      intro x hx _
      exact ⟨Fin.elim0, fun i => i.elim0, by simpa using hx⟩
    · obtain ⟨x₀, hx₀U, m, hm1, hx₀I⟩ := exists_unit_coeff U hU
      set U' : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p]) := U ⊓ LinearMap.ker (lcoeff ℚ_[p] m) with hU'
      have hle : U' ≤ U := inf_le_left
      have hx₀U' : x₀ ∉ U' := by
        intro h
        have : x₀.coeff m = 0 := by simpa using (Submodule.mem_inf.mp h).2
        rw [hm1] at this
        exact one_ne_zero this
      have hlt : U' < U := lt_of_le_of_ne hle (fun h => hx₀U' (h ▸ hx₀U))
      have hfd' : FiniteDimensional ℚ_[p] U' := Submodule.finiteDimensional_of_le hle
      have hrk : Module.finrank ℚ_[p] U' < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨k, b, hli, hsp, hbI, hco⟩ := ih _ hrk U' hfd' rfl
      have hsplit : ∀ x ∈ U, x - x.coeff m • x₀ ∈ U' := by
        intro x hx
        refine Submodule.mem_inf.mpr ⟨U.sub_mem hx (U.smul_mem _ hx₀U), ?_⟩
        simp [hm1]
      refine ⟨k + 1, Fin.cons x₀ b, ?_, ?_, ?_, ?_⟩
      · rw [linearIndependent_finCons]
        exact ⟨hli, by rw [hsp]; exact hx₀U'⟩
      · rw [Fin.range_cons, Submodule.span_insert, hsp]
        apply le_antisymm
        · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₀U) hle
        · intro x hx
          have : x = x.coeff m • x₀ + (x - x.coeff m • x₀) := by abel
          rw [this]
          exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) (hsplit x hx)
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hx₀I
        · simpa using hbI j
      · intro x hx hxI
        have hc : ‖x.coeff m‖ ≤ 1 := (mem_intPol_iff x).mp hxI m
        have hI' : x - x.coeff m • x₀ ∈ IntPol p σ := by
          rw [mem_intPol_iff]
          intro n
          rw [coeff_sub, coeff_smul, smul_eq_mul, sub_eq_add_neg]
          refine (Padic.nonarchimedean _ _).trans (max_le ((mem_intPol_iff x).mp hxI n) ?_)
          rw [norm_neg, norm_mul]
          exact mul_le_one₀ hc (norm_nonneg _) ((mem_intPol_iff x₀).mp hx₀I n)
        obtain ⟨c, hc1, hxc⟩ := hco _ (hsplit x hx) hI'
        refine ⟨Fin.cons (x.coeff m) c, ?_, ?_⟩
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using hc
          · simpa using hc1 j
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← hxc]
          abel
end Formalism.InvariantFactorPaths.PW.LatticeBasis
