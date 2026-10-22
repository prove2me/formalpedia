-- Prove2me | solution 1 for FinNetProp.Mitosis.part_I
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T16:09:33.069117+00:00
-- url     : https://prove2.me/submissions/efba132d-9f88-4c7d-a9a9-cb81ee12a0aa

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting
import Theorems.Thm_FinNetProp_Mitosis_eisenberg_noe_unique
import Theorems.Thm_FinNetProp_Mitosis_part_I_limited_liability
import Theorems.Thm_FinNetProp_Mitosis_part_I_priority_of_creditors
import Theorems.Thm_FinNetProp_Mitosis_part_I_limit_solution
import Theorems.Thm_FinNetProp_Mitosis_eq_A_1_split_solution

namespace FinNetProp.Mitosis

open Finset Filter Topology

lemma fnpI_le_L (G : FinNet) (P : ℕ → ℕ → ℝ) (hP : IsPropSolution G P) (a c : ℕ) :
    P a c ≤ G.L a c := by
  by_cases h : a ∈ G.N ∧ c ∈ G.N
  · rw [hP.2 a h.1 c h.2]; exact min_le_right _ _
  · rw [hP.1.2.2 a c (by tauto)]; exact G.L_nonneg a c

lemma fnpI_unique (G : FinNet) (P Q : ℕ → ℕ → ℝ) (hP : IsPropSolution G P)
    (hQ : IsPropSolution G Q) : P = Q :=
  (eisenberg_noe_unique G).unique hP hQ

lemma fnpI_cont (b : BankruptcyRule) (hb : ∀ F : FinNet, IsPropSolution F (b F)) :
    RuleContinuous b := by
  intro Fs F hconv i j
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨hN, hz, hL⟩ := hconv
  set G : ℕ → FinNet := fun n => Fs (ns n) with hG
  have hGconv : NetConverges G F :=
    ⟨hns.eventually hN, fun a => (hz a).comp hns, fun a c => (hL a c).comp hns⟩
  -- finite-dimensional vectors
  let ι := (↥F.N) × (↥F.N)
  let v : ℕ → ι → ℝ := fun n p => b (G n) p.1.1 p.2.1
  let w : ℕ → ι → ℝ := fun n p => (G n).L p.1.1 p.2.1
  have hw : Tendsto w atTop (𝓝 (fun p : ι => F.L p.1.1 p.2.1)) :=
    tendsto_pi_nhds.2 fun p => hGconv.2.2 p.1.1 p.2.1
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto w hw)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (w 0) ⟨0, rfl⟩)
  have hvB : ∀ n, v n ∈ Metric.closedBall (0 : ι → ℝ) C := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hC0]
    intro p
    have h1 : 0 ≤ v n p := (b.mem (G n)).1 _ _
    have h2 : v n p ≤ w n p := fnpI_le_L (G n) (b (G n)) (hb _) _ _
    have h3 : ‖w n p‖ ≤ C := (norm_le_pi_norm (w n) p).trans (hC (w n) ⟨n, rfl⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    rw [Real.norm_eq_abs] at h3
    exact h2.trans ((le_abs_self _).trans h3)
  obtain ⟨u, -, φ, hφ, hlimv⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hvB
  classical
  let Pbar : ℕ → ℕ → ℝ := fun a c =>
    if h : a ∈ F.N ∧ c ∈ F.N then u (⟨a, h.1⟩, ⟨c, h.2⟩) else 0
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hGφ : NetConverges (fun n => G (φ n)) F :=
    ⟨hφt.eventually hGconv.1, fun a => (hGconv.2.1 a).comp hφt,
      fun a c => (hGconv.2.2 a c).comp hφt⟩
  have hcoord : ∀ a c, Tendsto (fun n => b (G (φ n)) a c) atTop (𝓝 (Pbar a c)) := by
    intro a c
    by_cases h : a ∈ F.N ∧ c ∈ F.N
    · have := (tendsto_pi_nhds.1 hlimv) (⟨a, h.1⟩, ⟨c, h.2⟩)
      simp only [Pbar, dif_pos h]
      exact this
    · simp only [Pbar, dif_neg h]
      apply tendsto_const_nhds.congr'
      filter_upwards [hGφ.1] with n hn
      exact ((b.mem (G (φ n))).2.2 a c (by rw [hn]; tauto)).symm
  have hsol := part_I_limit_solution (fun n => G (φ n)) F hGφ (fun n => b (G (φ n)))
    (fun n => hb _) Pbar hcoord
  have hEq : Pbar = b F := fnpI_unique F Pbar (b F) hsol (hb F)
  refine ⟨φ, ?_⟩
  have := hcoord i j
  rw [hEq] at this
  exact this

lemma fnpI_mitosis (b : BankruptcyRule) (hb : ∀ F : FinNet, IsPropSolution F (b F)) :
    InvariantToMitosis b := by
  classical
  intro F j hj K hK F' hF'
  have hsp := eq_A_1_split_solution F (b F) (hb F) j hj K hK F' hF'
  have hbF' : b F' = splitPay F.N (b F) j K := fnpI_unique F' _ _ (hb F') hsp
  set m : ℝ := (K.card : ℝ) + 1 with hm
  have hmpos : 0 < m := by positivity
  have hjK : j ∉ K := fun h => Finset.disjoint_left.1 hK h hj
  have hcardJ : ((insert j K).card : ℝ) = m := by
    rw [Finset.card_insert_of_notMem hjK]; push_cast; ring
  have hJE : ∀ x, x ∈ insert j K → x ∉ F.N.erase j := by
    intro x hx hxE
    rcases Finset.mem_insert.1 hx with h | h
    · exact (Finset.mem_erase.1 hxE).1 h
    · exact Finset.disjoint_left.1 hK h (Finset.mem_erase.1 hxE).2
  rw [hbF']
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have : ∀ k ∈ insert j K, splitPay F.N (b F) j K k i = b F j i / m := by
      intro k hk; simp only [splitPay]; rw [if_pos ⟨hk, hi⟩]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcardJ]
    field_simp
  · intro i hi
    have : ∀ k ∈ insert j K, splitPay F.N (b F) j K i k = b F i j / m := by
      intro k hk; simp only [splitPay]
      rw [if_neg (fun h => hJE i h.1 hi), if_pos ⟨hi, hk⟩]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcardJ]
    field_simp
  · intro h hh i hi
    simp only [splitPay]
    rw [if_neg (fun h' => hJE h h'.1 hh), if_neg (fun h' => hJE i h'.2 hi), if_pos ⟨hh, hi⟩]

theorem fnp_part_I (b : BankruptcyRule) (hb : ∀ F : FinNet, IsPropSolution F (b F)) :
    ClaimsBounded b ∧ LimitedLiability b ∧ PriorityOfCreditors b ∧ RuleContinuous b ∧
      Impartial b ∧ InvariantToMitosis b := by
  refine ⟨?_, ?_, ?_, fnpI_cont b hb, ?_, fnpI_mitosis b hb⟩
  · intro F i _ j _
    exact fnpI_le_L F (b F) (hb F) i j
  · intro F
    exact part_I_limited_liability F (b F) (hb F)
  · intro F
    exact part_I_priority_of_creditors F (b F) (hb F)
  · intro F i hi j hj k hk hjk
    rw [(hb F).2 i hi j hj, (hb F).2 i hi k hk, hjk]
    unfold relLiab
    rw [hjk]

end FinNetProp.Mitosis

theorem solution (b : FinNetProp.Mitosis.BankruptcyRule)
    (hb : ∀ F : FinNetProp.Mitosis.FinNet, FinNetProp.Mitosis.IsPropSolution F (b F)) :
    FinNetProp.Mitosis.ClaimsBounded b ∧ FinNetProp.Mitosis.LimitedLiability b ∧
      FinNetProp.Mitosis.PriorityOfCreditors b ∧ FinNetProp.Mitosis.RuleContinuous b ∧
      FinNetProp.Mitosis.Impartial b ∧ FinNetProp.Mitosis.InvariantToMitosis b :=
  FinNetProp.Mitosis.fnp_part_I b hb
