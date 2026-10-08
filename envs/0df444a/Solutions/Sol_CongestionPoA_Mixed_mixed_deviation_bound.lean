-- Prove2me | solution 1 for CongestionPoA.Mixed.mixed_deviation_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T19:29:56.439534+00:00
-- url     : https://prove2.me/submissions/c33894d5-d4a5-433c-b47a-6ad92d6331fc

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_CongestionPoA_Mixed_Model



namespace CongestionPoA.Mixed

open Finset

theorem cm_marg {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    (σ : ∀ i, S i → ℝ) (hσ : ∀ i, ∑ t, σ i t = 1) (j : ι) (h : S j → ℝ) :
    ∑ s : (∀ i, S i), AGT.profileProb σ s * h (s j) = ∑ t, σ j t * h t := by
  have key : ∀ s : (∀ i, S i), AGT.profileProb σ s * h (s j)
      = ∏ i, (Function.update σ j (fun t => σ j t * h t)) i (s i) := by
    intro s
    unfold AGT.profileProb
    rw [← Finset.mul_prod_erase Finset.univ (fun i => σ i (s i)) (Finset.mem_univ j),
      ← Finset.mul_prod_erase Finset.univ (fun i => (Function.update σ j (fun t => σ j t * h t)) i (s i)) (Finset.mem_univ j)]
    have hp : ∏ i ∈ Finset.univ.erase j, (Function.update σ j (fun t => σ j t * h t)) i (s i)
        = ∏ i ∈ Finset.univ.erase j, σ i (s i) :=
      Finset.prod_congr rfl (fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
    rw [hp, Function.update_self]
    ring
  simp_rw [key]
  rw [← Fintype.prod_sum]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  have hp : ∏ i ∈ Finset.univ.erase j, ∑ t, (Function.update σ j (fun t => σ j t * h t)) i t
      = ∏ i ∈ Finset.univ.erase j, (1:ℝ) :=
    Finset.prod_congr rfl (fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi), hσ i])
  rw [hp, Function.update_self]
  simp

theorem cm_total {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    (σ : ∀ i, S i → ℝ) (hσ : ∀ i, ∑ t, σ i t = 1) :
    ∑ s : (∀ i, S i), AGT.profileProb σ s = 1 := by
  unfold AGT.profileProb
  rw [← Fintype.prod_sum]
  simp [hσ]

theorem cm_sumcost {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (f : E → ℝ) :
    ∑ i, ∑ e ∈ A i, f e = ∑ e, (CongestionPoA.AsymSum.load A e : ℝ) * f e := by
  have : ∀ i, ∑ e ∈ A i, f e = ∑ e, if e ∈ A i then f e else 0 := fun i => by
    rw [← Finset.sum_filter]; congr 1; ext; simp
  simp_rw [this]
  rw [Finset.sum_comm]
  congr 1; ext e
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rfl


open CongestionPoA.AsymSum in
theorem cm_load_eq {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (e : E) :
    (load A e : ℝ) = ∑ j, if e ∈ A j then (1:ℝ) else 0 := by
  unfold load
  rw [Finset.card_filter]; push_cast; rfl

theorem cm_lin {α E J : Type*} [Fintype α] (w : α → ℝ) (T : Finset E) (U : Finset J)
    (a b : E → ℝ) (g : E → J → α → ℝ) :
    ∑ s, w s * ∑ e ∈ T, (a e * (1 + ∑ j ∈ U, g e j s) + b e)
      = ∑ e ∈ T, (a e * ((∑ s, w s) + ∑ j ∈ U, ∑ s, w s * g e j s) + b e * ∑ s, w s) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Finset.sum_comm (s := U)]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_one]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl (fun _ _ => by ring)
    · exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  · exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem cm_dev {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (a b : E → ℝ) (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlat : ∀ e k, G.latency e k = a e * k + b e)
    (σ : ∀ i, ↥(G.strategies i) → ℝ) (hσ : IsMixedNash G σ)
    (P : ι → Finset E) (hP : CongestionPoA.AsymSum.IsProfile G P) (i : ι) :
    expCost G σ i ≤ ∑ e ∈ P i, (a e * (expLoad G σ e + 1) + b e) := by
  classical
  obtain ⟨hprof, hnash⟩ := hσ
  set p0 : ↥(G.strategies i) := ⟨P i, hP i⟩ with hp0
  set τ : ↥(G.strategies i) → ℝ := fun t => if t = p0 then 1 else 0 with hτ
  have hτl : AGT.IsLottery τ := ⟨fun t => by simp only [hτ]; split_ifs <;> norm_num, by simp [hτ]⟩
  have hdev := hnash i τ hτl
  set σ' := Function.update σ i τ with hσ'
  have hsum : ∀ j, ∑ t, σ j t = 1 := fun j => (hprof j).2
  have hsum' : ∀ j, ∑ t, σ' j t = 1 := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [hσ', Function.update_self]; exact hτl.2
    · rw [hσ', Function.update_of_ne hj]; exact hsum j
  have hnn' : ∀ s, 0 ≤ AGT.profileProb σ' s := by
    intro s; unfold AGT.profileProb
    apply Finset.prod_nonneg; intro j _
    by_cases hj : j = i
    · subst hj; rw [hσ', Function.update_self]; exact hτl.1 _
    · rw [hσ', Function.update_of_ne hj]; exact (hprof j).1 _
  -- indicator
  let I : E → ∀ j, ↥(G.strategies j) → ℝ := fun e j t => if e ∈ t.1 then 1 else 0
  have h1 : expCost G σ i ≤ ∑ s : (∀ j, ↥(G.strategies j)), AGT.profileProb σ' s *
      CongestionPoA.AsymSum.cost G (fun j => (s j).1) i := by
    unfold AGT.expectedPayoff payoff at hdev
    unfold expCost
    simp only [mul_neg, Finset.sum_neg_distrib, neg_le_neg_iff] at hdev
    exact hdev
  let F : (∀ j, ↥(G.strategies j)) → ℝ := fun s =>
    ∑ e ∈ P i, (a e * (1 + ∑ j ∈ Finset.univ.erase i, I e j (s j)) + b e)
  have h2 : ∑ s : (∀ j, ↥(G.strategies j)), AGT.profileProb σ' s *
      CongestionPoA.AsymSum.cost G (fun j => (s j).1) i
      ≤ ∑ s : (∀ j, ↥(G.strategies j)), AGT.profileProb σ' s * F s := by
    apply Finset.sum_le_sum; intro s _
    by_cases hs : s i = p0
    · apply mul_le_mul_of_nonneg_left _ (hnn' s)
      unfold CongestionPoA.AsymSum.cost
      have : (s i).1 = P i := by rw [hs]
      beta_reduce
      rw [this]
      simp only [F, I]
      apply Finset.sum_le_sum; intro e _
      rw [hlat, cm_load_eq]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have hI : (if e ∈ (s i).1 then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      have := ha e
      nlinarith
    · have : AGT.profileProb σ' s = 0 := by
        unfold AGT.profileProb
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        rw [hσ', Function.update_self, hτ]; simp [hs]
      rw [this]; simp
  have h3 : ∑ s : (∀ j, ↥(G.strategies j)), AGT.profileProb σ' s * F s
      = ∑ e ∈ P i, (a e * (1 + ∑ j ∈ Finset.univ.erase i,
          ∑ s : (∀ j, ↥(G.strategies j)), AGT.profileProb σ s * I e j (s j)) + b e) := by
    have := cm_lin (fun s => AGT.profileProb σ' s) (P i) (Finset.univ.erase i) a b
      (fun e j s => I e j (s j))
    simp only [F]
    rw [this, cm_total σ' hsum']
    refine Finset.sum_congr rfl (fun e _ => ?_)
    congr 3
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' := Finset.ne_of_mem_erase hj
    rw [cm_marg σ' hsum' j (I e j), cm_marg σ hsum j (I e j), hσ', Function.update_of_ne hj']
    simp
  have h4 : ∀ e, ∑ j ∈ Finset.univ.erase i,
      ∑ s : (∀ j, ↥(G.strategies j)), AGT.profileProb σ s * I e j (s j) ≤ expLoad G σ e := by
    intro e
    have hE : expLoad G σ e = ∑ j, ∑ s : (∀ j, ↥(G.strategies j)), AGT.profileProb σ s * I e j (s j) := by
      unfold expLoad
      simp_rw [cm_load_eq, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hE]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    intro j _ _
    rw [cm_marg σ hsum j (I e j)]
    apply Finset.sum_nonneg; intro t _
    apply mul_nonneg ((hprof j).1 t)
    simp only [I]; split_ifs <;> norm_num
  calc expCost G σ i ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := h3
    _ ≤ _ := by
      apply Finset.sum_le_sum; intro e _
      have := h4 e; have := ha e
      nlinarith

end CongestionPoA.Mixed

open CongestionPoA.Mixed


theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (a b : E → ℝ) (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlat : ∀ e k, G.latency e k = a e * k + b e)
    (σ : ∀ i, ↥(G.strategies i) → ℝ) (hσ : IsMixedNash G σ)
    (P : ι → Finset E) (hP : CongestionPoA.AsymSum.IsProfile G P) (i : ι) :
    expCost G σ i ≤ ∑ e ∈ P i, (a e * (expLoad G σ e + 1) + b e) := by
  exact cm_dev G a b ha hb hlat σ hσ P hP i
