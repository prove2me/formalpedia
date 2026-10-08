-- Prove2me | solution 1 for CongestionPoA.Mixed.mixed_poa_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T19:32:30.164168+00:00
-- url     : https://prove2.me/submissions/e3d065f8-5d01-4720-8777-5f4dea9cb430

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


theorem cm_pointwise (p : ℕ) (z X a b s : ℝ) (hs : s = Real.sqrt 5) (hz : 0 ≤ z) (hX : z ^ 2 ≤ X)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (p:ℝ) * (a * (z + 1) + b) ≤ (5 + s) / 4 * ((p:ℝ) * (a * p + b)) + (s - 1) / 4 * (a * X + b * z) := by
  have s5 : s ^ 2 = 5 := by rw [hs]; exact Real.sq_sqrt (by norm_num)
  have s2 : 2 < s := by rw [hs]; rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have s3 : s < 3 := by nlinarith
  have hpp : (0:ℝ) ≤ (p:ℝ) * p - p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; simp
    · have : (1:ℝ) ≤ p := by exact_mod_cast h
      nlinarith
  have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg p
  set μ := (s - 1) / 4 with hμ
  have hμ0 : 0 < μ := by rw [hμ]; linarith
  -- key: μ X - p z + λ p² - p ≥ 0
  have key : 0 ≤ μ * X - p * z + (5 + s) / 4 * (p * p) - p := by
    have h4 : 4 * μ * (μ * z ^ 2 - p * z + (5 + s) / 4 * (p * p) - p) = (2 * μ * z - p) ^ 2 + 4 * μ * (p * p - p) := by
      rw [hμ]; ring_nf; rw [s5]; ring_nf
    have : 0 ≤ μ * z ^ 2 - p * z + (5 + s) / 4 * (p * p) - p := by
      have h5 : 0 ≤ 4 * μ * (μ * z ^ 2 - p * z + (5 + s) / 4 * (p * p) - p) := by
        rw [h4]; positivity
      nlinarith
    nlinarith
  have hbz : 0 ≤ b * z := mul_nonneg hb hz
  have : (p:ℝ) * (a * (z + 1) + b) = a * (p * z + p) + b * p := by ring
  rw [this]
  have h1 : a * (p * z + p) ≤ a * ((5 + s) / 4 * (p * p) + μ * X) := by
    apply mul_le_mul_of_nonneg_left _ ha; linarith
  have h2 : b * p ≤ (5 + s) / 4 * (b * p) := by
    have : 0 ≤ b * p := mul_nonneg hb hp0
    nlinarith
  nlinarith [mul_nonneg hμ0.le hbz]


theorem cm_goal {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (hlin : CongestionPoA.AsymSum.IsLinear G)
    (σ : ∀ i, ↥(G.strategies i) → ℝ) (hσ : IsMixedNash G σ)
    (P : ι → Finset E) (hP : CongestionPoA.AsymSum.IsProfile G P) :
    mixedSumCost G σ ≤ (3 + Real.sqrt 5) / 2 * CongestionPoA.AsymSum.sumCost G P := by
  obtain ⟨a, b, ha, hb, hlat⟩ := hlin
  have hprof := hσ.1
  have hsum : ∀ j, ∑ t, σ j t = 1 := fun j => (hprof j).2
  have hnn : ∀ s, 0 ≤ AGT.profileProb σ s := by
    intro s; unfold AGT.profileProb
    exact Finset.prod_nonneg (fun j _ => (hprof j).1 _)
  let n : (∀ j, ↥(G.strategies j)) → E → ℝ := fun s e =>
    (CongestionPoA.AsymSum.load (fun j => (s j).1) e : ℝ)
  let X : E → ℝ := fun e => ∑ s : (∀ j, ↥(G.strategies j)), AGT.profileProb σ s * (n s e) ^ 2
  let z : E → ℝ := fun e => expLoad G σ e
  have hS : mixedSumCost G σ = ∑ e, (a e * X e + b e * z e) := by
    unfold mixedSumCost expCost
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hc : ∀ s : (∀ j, ↥(G.strategies j)), ∑ i, CongestionPoA.AsymSum.cost G (fun j => (s j).1) i
        = ∑ e, (a e * (n s e) ^ 2 + b e * n s e) := by
      intro s
      unfold CongestionPoA.AsymSum.cost
      rw [cm_sumcost (fun j => (s j).1)
        (fun e => G.latency e (CongestionPoA.AsymSum.load (fun j => (s j).1) e))]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      simp only [hlat, n]; ring
    simp_rw [hc, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    simp only [X, z, expLoad, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun _ _ => by ring)
    · exact Finset.sum_congr rfl (fun _ _ => by simp only [n]; ring)
  have hD : mixedSumCost G σ ≤ ∑ e, (CongestionPoA.AsymSum.load P e : ℝ) * (a e * (z e + 1) + b e) := by
    calc mixedSumCost G σ ≤ ∑ i, ∑ e ∈ P i, (a e * (expLoad G σ e + 1) + b e) := by
          unfold mixedSumCost
          exact Finset.sum_le_sum (fun i _ => cm_dev G a b ha hb hlat σ hσ P hP i)
      _ = _ := cm_sumcost P _
  have hO : CongestionPoA.AsymSum.sumCost G P
      = ∑ e, (CongestionPoA.AsymSum.load P e : ℝ) * (a e * (CongestionPoA.AsymSum.load P e : ℝ) + b e) := by
    unfold CongestionPoA.AsymSum.sumCost CongestionPoA.AsymSum.cost
    rw [cm_sumcost]
    simp only [hlat]
  have hz : ∀ e, 0 ≤ z e := by
    intro e
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (hnn s) (Nat.cast_nonneg _))
  have hX : ∀ e, z e ^ 2 ≤ X e := by
    intro e
    have h0 : 0 ≤ ∑ s : (∀ j, ↥(G.strategies j)), AGT.profileProb σ s * (n s e - z e) ^ 2 :=
      Finset.sum_nonneg (fun s _ => mul_nonneg (hnn s) (sq_nonneg _))
    have hexp : ∑ s : (∀ j, ↥(G.strategies j)), AGT.profileProb σ s * (n s e - z e) ^ 2
        = X e - 2 * z e * z e + z e ^ 2 * ∑ s : (∀ j, ↥(G.strategies j)), AGT.profileProb σ s := by
      have : ∀ s : (∀ j, ↥(G.strategies j)), AGT.profileProb σ s * (n s e - z e) ^ 2
          = AGT.profileProb σ s * (n s e) ^ 2 - 2 * z e * (AGT.profileProb σ s * n s e)
            + z e ^ 2 * AGT.profileProb σ s := fun s => by ring
      simp_rw [this]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl
    rw [hexp, cm_total σ hsum] at h0
    nlinarith
  set s5 := Real.sqrt 5 with hs5
  have hsq : s5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have s2 : 2 < s5 := by nlinarith [Real.sqrt_nonneg 5]
  have hpt : ∀ e, (CongestionPoA.AsymSum.load P e : ℝ) * (a e * (z e + 1) + b e)
      ≤ (5 + s5) / 4 * ((CongestionPoA.AsymSum.load P e : ℝ) * (a e * (CongestionPoA.AsymSum.load P e : ℝ) + b e))
        + (s5 - 1) / 4 * (a e * X e + b e * z e) :=
    fun e => cm_pointwise _ _ _ _ _ s5 rfl (hz e) (hX e) (ha e) (hb e)
  have hsumpt := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hpt e)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hO, ← hS] at hsumpt
  have hfin : mixedSumCost G σ * (5 - s5) ≤ (5 + s5) * CongestionPoA.AsymSum.sumCost G P := by
    nlinarith
  have heq : (3 + s5) / 2 * (5 - s5) = 5 + s5 := by nlinarith
  have hpos : 0 < 5 - s5 := by nlinarith
  rw [← heq] at hfin
  nlinarith

end CongestionPoA.Mixed

open CongestionPoA.Mixed


theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (hlin : CongestionPoA.AsymSum.IsLinear G)
    (σ : ∀ i, ↥(G.strategies i) → ℝ) (hσ : IsMixedNash G σ)
    (P : ι → Finset E) (hP : CongestionPoA.AsymSum.IsProfile G P) :
    mixedSumCost G σ ≤ (3 + Real.sqrt 5) / 2 * CongestionPoA.AsymSum.sumCost G P := by
  exact cm_goal G hlin σ hσ P hP
