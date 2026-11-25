-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.abs_prod_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:13:38.178737+00:00
-- url     : https://prove2.me/submissions/e262afed-b415-4bd7-bb7e-3c4409e74f5f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeBotOfIsMaximal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumOfMean
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_vF_lt_of_notMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
private theorem abs_prod_sub_prod_le_of_bounded_differences {ι : Type*} (S : Finset ι) (x y C d : ι → ℝ)
    (hx : ∀ i ∈ S, |x i| ≤ C i) (hy : ∀ i ∈ S, |y i| ≤ C i)
    (hd : ∀ i ∈ S, x i ≠ y i → 1 ≤ d i) (hd0 : ∀ i ∈ S, 0 ≤ d i) :
    |∏ i ∈ S, x i - ∏ i ∈ S, y i| ≤ 2 * (∏ i ∈ S, C i) * ∑ i ∈ S, d i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Finset.prod_insert hp, Finset.sum_insert hp]
    have ih' := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi)) (fun i hi => hy i (Finset.mem_insert_of_mem hi))
      (fun i hi => hd i (Finset.mem_insert_of_mem hi)) (fun i hi => hd0 i (Finset.mem_insert_of_mem hi))
    have hxp := hx p (Finset.mem_insert_self p s)
    have hyp := hy p (Finset.mem_insert_self p s)
    have hdp := hd0 p (Finset.mem_insert_self p s)
    have hCp : 0 ≤ C p := le_trans (abs_nonneg _) hxp
    have hys : |∏ i ∈ s, y i| ≤ ∏ i ∈ s, C i := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i hi => hy i (Finset.mem_insert_of_mem hi)
    have hdiff : |x p - y p| ≤ 2 * C p * d p := by
      by_cases h : x p = y p
      · rw [h, sub_self, abs_zero]
        exact mul_nonneg (by linarith) hdp
      · have h1 := hd p (Finset.mem_insert_self p s) h
        have h2 : |x p - y p| ≤ 2 * C p := by
          rw [abs_le] at hxp hyp ⊢
          constructor <;> linarith
        calc |x p - y p| ≤ 2 * C p := h2
          _ ≤ 2 * C p * d p := le_mul_of_one_le_right (by linarith) h1
    calc |x p * ∏ i ∈ s, x i - y p * ∏ i ∈ s, y i|
        = |x p * (∏ i ∈ s, x i - ∏ i ∈ s, y i) + (x p - y p) * ∏ i ∈ s, y i| := by
          congr 1
          ring
      _ ≤ |x p * (∏ i ∈ s, x i - ∏ i ∈ s, y i)| + |(x p - y p) * ∏ i ∈ s, y i| := abs_add_le _ _
      _ = |x p| * |∏ i ∈ s, x i - ∏ i ∈ s, y i| + |x p - y p| * |∏ i ∈ s, y i| := by
          rw [abs_mul, abs_mul]
      _ ≤ C p * (2 * (∏ i ∈ s, C i) * ∑ i ∈ s, d i) + (2 * C p * d p) * ∏ i ∈ s, C i :=
          add_le_add (mul_le_mul hxp ih' (abs_nonneg _) hCp)
            (mul_le_mul hdiff hys (abs_nonneg _) (mul_nonneg (by linarith) hdp))
      _ = 2 * (C p * ∏ i ∈ s, C i) * (d p + ∑ i ∈ s, d i) := by ring
end Formalism.HermitianLattices.Ext.L3.BoxSum
end
end

set_option autoImplicit false
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (a : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → 𝓞 F → ℝ) (C : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℝ)
    (c : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℕ) (hbd : ∀ 𝔭 ∈ S, ∀ n, |a 𝔭 n| ≤ C 𝔭)
    (hcg : ∀ 𝔭 ∈ S, ∀ (n n' : 𝓞 F) (k : ℕ), n ≠ 0 → vF 𝔭.1 n + c 𝔭 ≤ k → n - n' ∈ 𝔭.1 ^ k →
      a 𝔭 n = a 𝔭 n') (k : ℕ) {n : 𝓞 F} (hn : n ≠ 0) :
    |∏ 𝔭 ∈ S, a 𝔭 n - ∏ 𝔭 ∈ S, a 𝔭 (Quotient.out (Ideal.Quotient.mk (𝔭.1 ^ k) n))| ≤
      2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, (if n ∈ 𝔭.1 ^ (k + 1 - c 𝔭) then 1 else 0) := by
  refine abs_prod_sub_prod_le_of_bounded_differences S _ _ C _ (fun 𝔭 h𝔭 => hbd 𝔭 h𝔭 n) (fun 𝔭 h𝔭 => hbd 𝔭 h𝔭 _) (fun 𝔭 h𝔭 hne => ?_)
    (fun 𝔭 _ => by split_ifs <;> norm_num)
  by_contra hlt
  have hni : n ∉ 𝔭.1 ^ (k + 1 - c 𝔭) := by
    intro hm
    rw [if_pos hm] at hlt
    exact hlt le_rfl
  have hv := BoxSum.vF_lt_of_notMem hni
  have hk : vF 𝔭.1 n + c 𝔭 ≤ k := by omega
  apply hne
  refine hcg 𝔭 h𝔭 n _ k hn hk ?_
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
end Formalism.HermitianLattices.Ext.L3.BoxSum
