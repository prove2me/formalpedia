-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.tendsto_sum_of_mean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:01:00.130533+00:00
-- url     : https://prove2.me/submissions/85f2b205-2789-48e1-b001-7e5f95aa76da

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeBotOfIsMaximal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumOfMean
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_abs_prod_sub_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_tendsto_err
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_finite_box_inter
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_ne_zero_of_mem_boxSet
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_tendsto_sum_ideal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_tendsto_sum_periodic
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
private theorem finsum_boxSet_inf_eq_sum_ite_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) (b I : Ideal (𝓞 F))
    (g : 𝓞 F → ℝ) (hb : {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b}.Finite) :
    ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b ⊓ I}, g n =
      ∑ n ∈ hb.toFinset, if n ∈ I then g n else 0 := by
  classical
  have hfin : {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b ⊓ I}.Finite := finite_box_inter hK hF T _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_setOf_eq, Submodule.mem_inf]
  tauto
private theorem local_density_error_le_of_bounded_congruent (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (a : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → 𝓞 F → ℝ) (C : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℝ)
    (c : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℕ) (hbd : ∀ 𝔭 ∈ S, ∀ n, |a 𝔭 n| ≤ C 𝔭)
    (hcg : ∀ 𝔭 ∈ S, ∀ (n n' : 𝓞 F) (k : ℕ), n ≠ 0 → vF 𝔭.1 n + c 𝔭 ≤ k → n - n' ∈ 𝔭.1 ^ k →
      a 𝔭 n = a 𝔭 n') (b : Ideal (𝓞 F)) (T w : ℝ) (hw : 0 ≤ w) (k : ℕ) :
    |w * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ S, a 𝔭 n -
      w * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
          ∏ 𝔭 ∈ S, a 𝔭 (Quotient.out (Ideal.Quotient.mk (𝔭.1 ^ k) n))| ≤
      2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, w * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b ⊓ 𝔭.1 ^ (k + 1 - c 𝔭)},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := by
  classical
  have hfin : {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b}.Finite := finite_box_inter hK hF T _
  simp_rw [finsum_boxSet_inf_eq_sum_ite_mem hK hF T b _ _ hfin]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, ← mul_sub,
    ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hw]
  have hWn : ∀ n : 𝓞 F, 0 ≤ (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := fun n => by positivity
  calc w * |∑ n ∈ hfin.toFinset, ((Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ S, a 𝔭 n -
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
          ∏ 𝔭 ∈ S, a 𝔭 (Quotient.out (Ideal.Quotient.mk (𝔭.1 ^ k) n)))|
      ≤ w * ∑ n ∈ hfin.toFinset, (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
          (2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, (if n ∈ 𝔭.1 ^ (k + 1 - c 𝔭) then 1 else 0)) := by
        refine mul_le_mul_of_nonneg_left (le_trans (Finset.abs_sum_le_sum_abs _ _)
          (Finset.sum_le_sum fun n hn => ?_)) hw
        rw [← mul_sub, abs_mul, abs_of_nonneg (hWn n)]
        exact mul_le_mul_of_nonneg_left (abs_prod_sub_le S a C c hbd hcg k
          (ne_zero_of_mem_boxSet (hfin.mem_toFinset.1 hn).1)) (hWn n)
    _ = 2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, w * ∑ n ∈ hfin.toFinset,
          (if n ∈ 𝔭.1 ^ (k + 1 - c 𝔭) then (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) else 0) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun 𝔭 _ => Finset.sum_congr rfl fun n _ => ?_
        split_ifs <;> ring
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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {m : ℕ} (hm : 1 ≤ m)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (a : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → 𝓞 F → ℝ) (C : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℝ)
    (c : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℕ) (hbd : ∀ 𝔭 ∈ S, ∀ n, |a 𝔭 n| ≤ C 𝔭)
    (hcg : ∀ 𝔭 ∈ S, ∀ (n n' : 𝓞 F) (k : ℕ), n ≠ 0 → vF 𝔭.1 n + c 𝔭 ≤ k → n - n' ∈ 𝔭.1 ^ k →
      a 𝔭 n = a 𝔭 n')
    (hmean : ∀ 𝔭 ∈ S, Tendsto (fun k : ℕ => (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ)) *
      ∑ᶠ n' : 𝓞 F ⧸ 𝔭.1 ^ k, a 𝔭 (Quotient.out n')) atTop (𝓝 1))
    {b : Ideal (𝓞 F)} (hb : b ≠ ⊥) (hbS : ∀ 𝔭 ∈ S, b ⊔ 𝔭.1 = ⊤) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ S, a 𝔭 n)
      atTop (𝓝 ((m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm b : ℝ))) := by
  classical
  obtain ⟨L1, hL1⟩ : ∃ L1 : ℝ, L1 = (m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
      Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) := ⟨_, rfl⟩
  rw [← hL1]
  have hL1n : 0 ≤ L1 := by
    rw [hL1]
    exact div_nonneg (zpow_nonneg (Nat.cast_nonneg _) _) (Real.sqrt_nonneg _)
  have hw : ∀ j : ℕ, 0 ≤ ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) := fun j =>
    zpow_nonneg (sq_nonneg _) _
  have hC0 : 0 ≤ 2 * ∏ 𝔭 ∈ S, C 𝔭 :=
    mul_nonneg (by norm_num) (Finset.prod_nonneg fun 𝔭 h𝔭 => le_trans (abs_nonneg _) (hbd 𝔭 h𝔭 0))
  have hpos : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭.1 ≠ ⊥ := fun 𝔭 =>
    Ring.ne_bot_of_isMaximal_of_not_isField 𝔭.2 (NumberField.RingOfIntegers.not_isField F)
  have hIne : ∀ (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (e : ℕ), b ⊓ 𝔭.1 ^ e ≠ ⊥ := by
    intro 𝔭 e h
    have h1 : b * 𝔭.1 ^ e ≤ b ⊓ 𝔭.1 ^ e := Ideal.mul_le_inf
    rw [h, le_bot_iff, ← Ideal.zero_eq_bot] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact hb (by rwa [Ideal.zero_eq_bot] at h2)
    · exact hpos 𝔭 (by rw [← Ideal.zero_eq_bot]; exact pow_eq_zero_iff'.1 h2 |>.1)
  have hNle : ∀ (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (e : ℕ),
      L1 / (Ideal.absNorm (b ⊓ 𝔭.1 ^ e) : ℝ) ≤ L1 / (Ideal.absNorm 𝔭.1 : ℝ) ^ e := by
    intro 𝔭 e
    have hd : Ideal.absNorm (𝔭.1 ^ e) ∣ Ideal.absNorm (b ⊓ 𝔭.1 ^ e) :=
      Ideal.absNorm_dvd_absNorm_of_le inf_le_right
    have hn0 : Ideal.absNorm (b ⊓ 𝔭.1 ^ e) ≠ 0 := fun h => hIne 𝔭 e (Ideal.absNorm_eq_zero_iff.1 h)
    have hp0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => hpos 𝔭 (Ideal.absNorm_eq_zero_iff.1 h)
    have hle : Ideal.absNorm 𝔭.1 ^ e ≤ Ideal.absNorm (b ⊓ 𝔭.1 ^ e) := by
      rw [← map_pow]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd
    refine div_le_div_of_nonneg_left hL1n (by positivity) ?_
    exact_mod_cast hle
  have hμ : Tendsto (fun k : ℕ => L1 / (Ideal.absNorm b : ℝ) * ∏ 𝔭 ∈ S, ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ)) *
      ∑ᶠ n' : 𝓞 F ⧸ 𝔭.1 ^ k, a 𝔭 (Quotient.out n'))) atTop (𝓝 (L1 / (Ideal.absNorm b : ℝ) * 1)) := by
    have := tendsto_finset_prod S hmean
    simp only [Finset.prod_const_one] at this
    exact this.const_mul _
  have hErr := tendsto_err S (2 * ∏ 𝔭 ∈ S, C 𝔭) L1 c
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K1, hK1⟩ := Metric.tendsto_atTop.1 hμ (ε / 4) (by linarith)
  obtain ⟨K2, hK2⟩ := Metric.tendsto_atTop.1 hErr (ε / 4) (by linarith)
  obtain ⟨k, hk1, hk2⟩ : ∃ k, K1 ≤ k ∧ K2 ≤ k := ⟨max K1 K2, le_max_left _ _, le_max_right _ _⟩
  have g1 := hK1 k hk1
  have g2 := hK2 k hk2
  rw [Real.dist_eq, mul_one] at g1
  rw [Real.dist_eq, sub_zero] at g2
  have hP := tendsto_sum_periodic hK hF hm k (fun 𝔭 q => a 𝔭 (Quotient.out q)) S b hb hbS 0
  simp only [sub_zero] at hP
  rw [← hL1] at hP
  have hE : Tendsto (fun j : ℕ => 2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
      ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b ⊓ 𝔭.1 ^ (k + 1 - c 𝔭)},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1)) atTop
      (𝓝 (2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, L1 / (Ideal.absNorm (b ⊓ 𝔭.1 ^ (k + 1 - c 𝔭)) : ℝ))) := by
    refine Tendsto.const_mul _ (tendsto_finset_sum S fun 𝔭 _ => ?_)
    have := tendsto_sum_ideal hK hF hm (hIne 𝔭 (k + 1 - c 𝔭))
    rwa [← hL1] at this
  obtain ⟨J1, hJ1⟩ := Metric.tendsto_atTop.1 hP (ε / 4) (by linarith)
  obtain ⟨J2, hJ2⟩ := Metric.tendsto_atTop.1 hE (ε / 4) (by linarith)
  refine ⟨max J1 J2, fun j hj => ?_⟩
  have d1 := hJ1 j (le_of_max_le_left hj)
  have d2 := hJ2 j (le_of_max_le_right hj)
  rw [Real.dist_eq] at d1 d2 ⊢
  have hcmp : 2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, L1 / (Ideal.absNorm (b ⊓ 𝔭.1 ^ (k + 1 - c 𝔭)) : ℝ) ≤
      2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, L1 / (Ideal.absNorm 𝔭.1 : ℝ) ^ (k + 1 - c 𝔭) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun 𝔭 _ => hNle 𝔭 _) hC0
  have key := local_density_error_le_of_bounded_congruent hK hF m S a C c hbd hcg b ((j : ℝ) ^ 2) _ (hw j) k
  have t1 := abs_sub_le (((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
      ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ S, a 𝔭 n)
    (((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
      ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
          ∏ 𝔭 ∈ S, a 𝔭 (Quotient.out (Ideal.Quotient.mk (𝔭.1 ^ k) n)))
    (L1 / (Ideal.absNorm b : ℝ))
  have t2 := abs_sub_le (((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
      ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
          ∏ 𝔭 ∈ S, a 𝔭 (Quotient.out (Ideal.Quotient.mk (𝔭.1 ^ k) n)))
    (L1 / (Ideal.absNorm b : ℝ) * ∏ 𝔭 ∈ S, ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ)) *
      ∑ᶠ n' : 𝓞 F ⧸ 𝔭.1 ^ k, a 𝔭 (Quotient.out n')))
    (L1 / (Ideal.absNorm b : ℝ))
  have d2' := (abs_lt.1 d2).2
  have g2' := (abs_lt.1 g2).2
  linarith
end Formalism.HermitianLattices.Ext.L3.BoxSum
