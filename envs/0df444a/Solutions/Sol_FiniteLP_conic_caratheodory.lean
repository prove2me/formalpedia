-- Prove2me | solution 1 for FiniteLP.conic_caratheodory
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:45.571799+00:00
-- url     : https://prove2.me/submissions/9a209c3b-4f57-489e-a254-674773370ae5

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Theorems.Thm_FiniteLP_toE_apply
attribute [local simp] FiniteLP.toE_apply

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators InnerProductSpace
open Finset
open FiniteLP
set_option maxHeartbeats 2000000
namespace FiniteLP
theorem _root_.solution {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (v : κ → EuclideanSpace ℝ ι) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k) :
    ∃ (d : κ → ℝ) (s : Finset κ), (∀ k, 0 ≤ d k) ∧ (∀ k ∉ s, d k = 0) ∧
      LinearIndepOn ℝ v s ∧ (∑ k ∈ s, d k • v k) = ∑ k, c k • v k := by
  -- Among all finsets `s` and coefficient functions `d : κ → ℝ` with `d ≥ 0`, `d = 0` off `s`, and `∑ k ∈ s, d k • v k = ∑ k, c k • v k`, choose one whose support (as a finset) has minimal cardinality.
  obtain ⟨s, hs⟩ : ∃ s : Finset κ, (∃ d : κ → ℝ, (∀ k, 0 ≤ d k) ∧ (∀ k ∉ s, d k = 0) ∧ (∑ k ∈ s, d k • v k = ∑ k, c k • v k)) ∧ ∀ t : Finset κ, (∃ d : κ → ℝ, (∀ k, 0 ≤ d k) ∧ (∀ k ∉ t, d k = 0) ∧ (∑ k ∈ t, d k • v k = ∑ k, c k • v k)) → s.card ≤ t.card := by
    apply_rules [ Set.exists_min_image ];
    · exact Set.toFinite _;
    · exact ⟨ Finset.univ, ⟨ c, hc, fun k hk => False.elim <| hk <| Finset.mem_univ _, by simp +decide ⟩ ⟩;
  by_cases h_lin_dep : ¬ LinearIndepOn ℝ v s;
  · obtain ⟨d, hd_nonneg, hd_zero, hd_sum⟩ := hs.left
    obtain ⟨a, ha_nonzero, ha_support, ha_sum⟩ : ∃ a : κ → ℝ, (∃ k ∈ s, a k ≠ 0) ∧ (∀ k ∉ s, a k = 0) ∧ (∑ k ∈ s, a k • v k = 0) ∧ (∃ k ∈ s, a k > 0) := by
      obtain ⟨a, ha_nonzero, ha_sum⟩ : ∃ a : κ → ℝ, (∃ k ∈ s, a k ≠ 0) ∧ (∀ k ∉ s, a k = 0) ∧ (∑ k ∈ s, a k • v k = 0) := by
        rw [ linearIndepOn_iff' ] at h_lin_dep;
        push Not at h_lin_dep;
        obtain ⟨ t, g, ht, hg, i, hi, hi' ⟩ := h_lin_dep; use fun k => if k ∈ t then g k else 0; simp_all +decide [ Finset.sum_ite ] ;
        exact ⟨ ⟨ i, ht hi, hi, hi' ⟩, fun k hk₁ hk₂ => False.elim <| hk₁ <| ht hk₂, by rw [ Finset.inter_eq_right.mpr ht, hg ] ⟩;
      by_cases h_neg : ∀ k ∈ s, a k ≤ 0;
      · use fun k => -a k;
        simp_all +decide [ neg_smul ];
        exact ha_nonzero.imp fun k hk => ⟨ hk.1, lt_of_le_of_ne ( h_neg k hk.1 ) hk.2 ⟩;
      · exact ⟨ a, ha_nonzero, ha_sum.1, ha_sum.2, by push Not at h_neg; exact h_neg ⟩;
    -- Choose $\theta > 0$ such that $d - \theta a$ is nonnegative and supported on a strictly smaller set than $s$.
    obtain ⟨θ, hθ_pos, hθ_min⟩ : ∃ θ > 0, (∀ k ∈ s, d k - θ * a k ≥ 0) ∧ (∃ k ∈ s, d k - θ * a k = 0) := by
      -- Choose $\theta$ to be the minimum of $d_k / a_k$ over all $k \in s$ where $a_k > 0$.
      obtain ⟨k₀, hk₀⟩ : ∃ k₀ ∈ s, a k₀ > 0 ∧ ∀ k ∈ s, a k > 0 → d k / a k ≥ d k₀ / a k₀ := by
        have h_min : ∃ k₀ ∈ Finset.filter (fun k => a k > 0) s, ∀ k ∈ Finset.filter (fun k => a k > 0) s, d k / a k ≥ d k₀ / a k₀ := by
          exact Finset.exists_min_image _ _ ⟨ ha_sum.2.choose, Finset.mem_filter.mpr ⟨ ha_sum.2.choose_spec.1, ha_sum.2.choose_spec.2 ⟩ ⟩;
        exact ⟨ h_min.choose, Finset.mem_filter.mp h_min.choose_spec.1 |>.1, Finset.mem_filter.mp h_min.choose_spec.1 |>.2, fun k hk hk' => h_min.choose_spec.2 k ( Finset.mem_filter.mpr ⟨ hk, hk' ⟩ ) ⟩;
      refine' ⟨ d k₀ / a k₀, div_pos ( lt_of_le_of_ne ( hd_nonneg k₀ ) ( Ne.symm _ ) ) hk₀.2.1, _, k₀, hk₀.1, _ ⟩;
      · intro h; simp_all +decide;
        have := hs.2 ( s.erase k₀ ) ( fun k => if k = k₀ then 0 else d k ) ?_ ?_ ?_
        · rw [Finset.card_erase_of_mem hk₀.1] at this
          have := Finset.card_pos.mpr ⟨k₀, hk₀.1⟩
          omega
        · intro k; split_ifs <;> simp [hd_nonneg]
        · intro k hk
          split_ifs with h'
          · rfl
          · simp only [Finset.mem_erase, h', ne_eq, not_false_eq_true, true_and] at hk
            exact hd_zero k hk
        · have hcongr : ∀ k ∈ s.erase k₀, (if k = k₀ then 0 else d k) • v k = d k • v k :=
            fun k hk => by simp [Finset.ne_of_mem_erase hk]
          rw [Finset.sum_congr rfl hcongr, Finset.sum_erase _ (by simp [h])]
          exact hd_sum
      · intro k hk; by_cases hk' : a k > 0 <;> simp_all +decide;
        · exact le_div_iff₀ hk' |>.1 ( hk₀.2.2 k hk hk' );
        · exact le_trans ( mul_nonpos_of_nonneg_of_nonpos ( div_nonneg ( hd_nonneg _ ) hk₀.2.1.le ) hk' ) ( hd_nonneg _ );
      · rw [ div_mul_cancel₀ _ hk₀.2.1.ne', sub_self ];
    -- Let $t = s.filter (fun k => d k - θ * a k ≠ 0)$ be the support of $d - θ a$.
    set t := s.filter (fun k => d k - θ * a k ≠ 0) with ht_def;
    -- Then $d - \theta a$ is nonnegative, supported on $t$, and $\sum_{k \in t} (d k - \theta a k) • v k = \sum_{k \in s} d k • v k$.
    have h_t_support : ∀ k, 0 ≤ d k - θ * a k := by
      exact fun k => if hk : k ∈ s then hθ_min.1 k hk else by simp +decide [ hd_zero k hk, ha_support k hk ] ;
    have h_t_zero : ∀ k ∉ t, d k - θ * a k = 0 := by
      grind
    have h_t_sum : ∑ k ∈ t, (d k - θ * a k) • v k = ∑ k, c k • v k := by
      convert congr_arg ( fun x => x - θ • ∑ k ∈ s, a k • v k ) hd_sum using 1;
      · rw [ Finset.sum_filter_of_ne ];
        · simp +decide [ sub_smul, Finset.smul_sum, Finset.sum_sub_distrib, smul_smul ];
        · exact fun k hk hk' => fun hk'' => hk' <| by rw [ hk'', zero_smul ] ;
      · simp +decide [ ha_sum.1 ];
    contrapose! hs;
    refine' fun h => ⟨ t, ⟨ fun k => d k - θ * a k, h_t_support, h_t_zero, h_t_sum ⟩, _ ⟩;
    refine' Finset.card_lt_card _;
    grind;
  · exact ⟨ hs.1.choose, s, hs.1.choose_spec.1, hs.1.choose_spec.2.1, Classical.not_not.mp h_lin_dep, hs.1.choose_spec.2.2 ⟩
end FiniteLP
