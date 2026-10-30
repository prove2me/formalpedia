-- Prove2me | solution 1 for GaoCascadePricing.UCB.lemma_4
-- status  : ACCEPTED   (disprove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:49:52.321435+00:00
-- url     : https://prove2.me/submissions/bdf75c41-6a5e-4810-b12d-f071a1eb1eb3

import Definitions.Def_GaoCascadePricing_UCB_EstimationEvent

open scoped BigOperators
open GaoCascadePricing.UCB

namespace DG4

def obs (i : Fin 7202) : Observation 3 :=
  if i.val = 0 then ![2, 4, 0] else if i.val = 1 then ![2, 2, 3]
  else if i.val % 2 = 0 then ![2, 1, 0] else ![5, 1, 0]

def pp : Action 3 1 := fun _ => 0

def hist : History 3 1 7202 := fun i => (pp, obs i)

lemma count_hist (P : Action 3 1 → Observation 3 → Prop) (Q : Fin 7202 → Prop) [DecidablePred Q]
    (hPQ : ∀ i, P (hist i).1 (hist i).2 ↔ Q i) :
    count hist P = (Finset.univ.filter Q).card := by
  unfold count
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hq : Q i
  · have := (hPQ i).2 hq
    simp [this, hq]
  · have : ¬ P (hist i).1 (hist i).2 := fun hp => hq ((hPQ i).1 hp)
    simp [this, hq]

lemma pk (j : Fin 3) (k : Fin 1) : pp j = k := Subsingleton.elim _ _

lemma c_ne0 : ne hist 0 0 = 7202 := by
  unfold ne
  rw [count_hist _ (fun i => obs i 0 ≠ 0) (by intro i; simp [hist, examined, pp])]
  decide +kernel

lemma c_nc0 : nc hist 0 0 = 3600 := by
  unfold nc
  rw [count_hist _ (fun i => (obs i 0 = 3 ∨ obs i 0 = 4 ∨ obs i 0 = 5)) (by intro i; simp [hist, clicked, pp])]
  decide +kernel

lemma c_nb0 : nb hist 0 0 = 0 := by
  unfold nb
  rw [count_hist _ (fun i => obs i 0 = 3) (by intro i; simp [hist, bought, pp])]
  decide +kernel

lemma c_ne1 : ne hist 1 0 = 7202 := by
  unfold ne
  rw [count_hist _ (fun i => obs i 1 ≠ 0) (by intro i; simp [hist, examined, pp])]
  decide +kernel

lemma c_nc1 : nc hist 1 0 = 1 := by
  unfold nc
  rw [count_hist _ (fun i => (obs i 1 = 3 ∨ obs i 1 = 4 ∨ obs i 1 = 5)) (by intro i; simp [hist, clicked, pp])]
  decide +kernel

lemma c_nb1 : nb hist 1 0 = 0 := by
  unfold nb
  rw [count_hist _ (fun i => obs i 1 = 3) (by intro i; simp [hist, bought, pp])]
  decide +kernel

lemma c_ne2 : ne hist 2 0 = 1 := by
  unfold ne
  rw [count_hist _ (fun i => obs i 2 ≠ 0) (by intro i; simp [hist, examined, pp])]
  decide +kernel

lemma c_nc2 : nc hist 2 0 = 1 := by
  unfold nc
  rw [count_hist _ (fun i => (obs i 2 = 3 ∨ obs i 2 = 4 ∨ obs i 2 = 5)) (by intro i; simp [hist, clicked, pp])]
  decide +kernel

lemma c_nb2 : nb hist 2 0 = 1 := by
  unfold nb
  rw [count_hist _ (fun i => obs i 2 = 3) (by intro i; simp [hist, bought, pp])]
  decide +kernel

lemma c_ng0 : ng hist 0 = 3602 := by
  unfold ng
  rw [count_hist _ (fun i => (obs i 0 = 1 ∨ obs i 0 = 2)) (by intro i; simp [hist, nonclick, pp])]
  decide +kernel

lemma c_ngs0 : ngs hist 0 = 3602 := by
  unfold ngs
  rw [count_hist _ (fun i => ((obs i 0 = 1 ∨ obs i 0 = 2) ∧ (obs i 0 = 2 ∨ obs i 0 = 5))) (by intro i; simp [hist, nonclick, continued, pp])]
  decide +kernel

lemma c_nz0 : nz hist 0 = 3600 := by
  unfold nz
  rw [count_hist _ (fun i => (obs i 0 = 4 ∨ obs i 0 = 5)) (by intro i; simp [hist, declined, pp])]
  decide +kernel

lemma c_nzs0 : nzs hist 0 = 3600 := by
  unfold nzs
  rw [count_hist _ (fun i => ((obs i 0 = 4 ∨ obs i 0 = 5) ∧ (obs i 0 = 2 ∨ obs i 0 = 5))) (by intro i; simp [hist, declined, continued, pp])]
  decide +kernel

lemma c_ng1 : ng hist 1 = 7201 := by
  unfold ng
  rw [count_hist _ (fun i => (obs i 1 = 1 ∨ obs i 1 = 2)) (by intro i; simp [hist, nonclick, pp])]
  decide +kernel

lemma c_ngs1 : ngs hist 1 = 1 := by
  unfold ngs
  rw [count_hist _ (fun i => ((obs i 1 = 1 ∨ obs i 1 = 2) ∧ (obs i 1 = 2 ∨ obs i 1 = 5))) (by intro i; simp [hist, nonclick, continued, pp])]
  decide +kernel

lemma c_nz1 : nz hist 1 = 1 := by
  unfold nz
  rw [count_hist _ (fun i => (obs i 1 = 4 ∨ obs i 1 = 5)) (by intro i; simp [hist, declined, pp])]
  decide +kernel

lemma c_nzs1 : nzs hist 1 = 0 := by
  unfold nzs
  rw [count_hist _ (fun i => ((obs i 1 = 4 ∨ obs i 1 = 5) ∧ (obs i 1 = 2 ∨ obs i 1 = 5))) (by intro i; simp [hist, declined, continued, pp])]
  decide +kernel


def mkt : Market 3 1 where
  products_pos := by norm_num
  prices_pos := by norm_num
  price := fun _ => 0
  price_nonneg := fun _ => le_rfl
  price_strictMono := fun a b h => absurd h (by rw [Subsingleton.elim a b]; exact lt_irrefl _)

noncomputable def th : Cascade 3 1 where
  beta _ _ := 1 / 2
  alpha _ _ := 1 / 2
  gamma j := if j.val = 0 then 1 / 1000 else if j.val = 1 then 1 / 2 else 0
  zeta j := if j.val = 0 then 1 / 1000 else if j.val = 1 then 1 / 2 else 0

lemma th_valid : th.Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j k; simp [th]; norm_num
  · intro j k; simp [th]; norm_num
  · intro j; fin_cases j <;> simp [th] <;> norm_num
  · intro j; fin_cases j <;> simp [th] <;> norm_num
  · intro j hj; fin_cases j <;> simp [th] at hj ⊢

noncomputable def pol : Policy 3 1 := fun _ _ => PMF.pure pp

lemma pol_ok : IsUCBCascade mkt pol := by
  intro n h _ p _ q
  have : q = p := Subsingleton.elim _ _
  rw [this]

lemma init_ok : Initialized hist := by
  refine ⟨?_, ?_⟩
  · intro j k
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    fin_cases j
    · simp only [Fin.zero_eta]; rw [c_ne0, c_nc0]; norm_num
    · simp only [Fin.mk_one]; rw [c_ne1, c_nc1]; norm_num
    · show 0 < ne hist 2 0 ∧ 0 < nc hist 2 0
      rw [c_ne2, c_nc2]; norm_num
  · intro j hj
    fin_cases j
    · simp only [Fin.zero_eta]; rw [c_ng0, c_nz0]; norm_num
    · simp only [Fin.mk_one]; rw [c_ng1, c_nz1]; norm_num
    · simp at hj

lemma cw_pos (o : Observation 3) (ho : o = ![2, 4, 0] ∨ o = ![2, 2, 3] ∨ o = ![2, 1, 0] ∨ o = ![5, 1, 0]) :
    0 < customerWeight th pp o := by
  unfold customerWeight
  rw [Fin.prod_univ_three]
  have a1 : active o 1 := by
    right; refine ⟨0, rfl, ?_⟩
    rcases ho with rfl | rfl | rfl | rfl <;> simp [continued]
  have a0 : active o 0 := Or.inl rfl
  rcases ho with rfl | rfl | rfl | rfl
  · have a2 : ¬ active ![2, 4, 0] 2 := by
      simp [active, continued]
      intro x hx; fin_cases x <;> simp_all
    simp [a0, a1, a2, localWeight, th, pp]
    norm_num
  · have a2 : active ![2, 2, 3] 2 := by
      right; refine ⟨1, rfl, ?_⟩; simp [continued]
    simp [a0, a1, a2, localWeight, th, pp]
    norm_num
  · have a2 : ¬ active ![2, 1, 0] 2 := by
      simp [active, continued]
      intro x hx; fin_cases x <;> simp_all
    simp [a0, a1, a2, localWeight, th, pp]
    norm_num
  · have a2 : ¬ active ![5, 1, 0] 2 := by
      simp [active, continued]
      intro x hx; fin_cases x <;> simp_all
    simp [a0, a1, a2, localWeight, th, pp]
    norm_num

lemma obs_cases (i : Fin 7202) :
    obs i = ![2, 4, 0] ∨ obs i = ![2, 2, 3] ∨ obs i = ![2, 1, 0] ∨ obs i = ![5, 1, 0] := by
  unfold obs
  split_ifs <;> simp

lemma weight_pos : 0 < historyWeight th pol hist := by
  unfold historyWeight
  apply Finset.prod_pos
  intro i _
  have h1 : ((pol i.val (historyPrefix hist i)) (hist i).1).toReal = 1 := by
    simp [pol, hist, pp]
  rw [h1, one_mul]
  exact cw_pos _ (obs_cases i)

noncomputable def LL : ℝ := Real.sqrt (2 * Real.log 7203)

lemma log_big : 1 < Real.log 7203 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

lemma LL_ge : 1 ≤ LL := by
  unfold LL
  have := log_big
  rw [Real.le_sqrt' (by norm_num)]
  nlinarith

lemma LL_nn : 0 ≤ LL := by linarith [LL_ge]

lemma rad_nn (t m : ℕ) : 0 ≤ radius t m := Real.sqrt_nonneg _

lemma rad_eq (m : ℕ) : radius (7202 + 1) m = LL / Real.sqrt m := by
  have h1 : ((7202 + 1 : ℕ) : ℝ) = 7203 := by norm_num
  unfold radius LL
  rw [h1, Real.sqrt_div (by have := log_big; positivity)]

lemma rad_le (m : ℕ) (hm : 3600 ≤ m) : radius (7202 + 1) m ≤ LL / 60 := by
  rw [rad_eq]
  apply div_le_div_of_nonneg_left LL_nn (by norm_num)
  rw [Real.le_sqrt' (by norm_num)]
  have : (3600 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

lemma rad_one : radius (7202 + 1) 1 = LL := by
  rw [rad_eq]; simp

lemma bonus_nn {J K n : ℕ} (h : History J K n) (p : Action J K) (j : Fin J) :
    0 ≤ bonus h p j := by
  simp only [bonus, radius]
  positivity

lemma m1 (m : ℕ) : min (radius (7202 + 1) m) 1 ≤ 1 := min_le_right _ _
lemma m0 (m : ℕ) : 0 ≤ min (radius (7202 + 1) m) 1 := le_min (rad_nn _ _) zero_le_one

lemma b0_le : bonus hist pp 0 ≤ LL / 15 := by
  have e1 : ne hist 0 (pp 0) = 7202 := c_ne0
  have e2 : nc hist 0 (pp 0) = 3600 := c_nc0
  have e3 : ng hist 0 = 3602 := c_ng0
  have e4 : nz hist 0 = 3600 := c_nz0
  have hj : ((0 : Fin 3).val + 1 < 3) := by decide
  unfold bonus
  rw [if_pos hj, if_pos hj, e1, e2, e3, e4]
  have r1 := rad_le 7202 (by norm_num)
  have r2 := rad_le 3600 (by norm_num)
  have r3 := rad_le 3602 (by norm_num)
  have l1 := min_le_left (radius (7202 + 1) 7202) 1
  have l2 := min_le_left (radius (7202 + 1) 3600) 1
  have l3 := min_le_left (radius (7202 + 1) 3602) 1
  linarith

lemma b1_bounds : LL ≤ bonus hist pp 1 ∧ bonus hist pp 1 ≤ 4 * LL := by
  have e1 : ne hist 1 (pp 1) = 7202 := c_ne1
  have e2 : nc hist 1 (pp 1) = 1 := c_nc1
  have e3 : ng hist 1 = 7201 := c_ng1
  have e4 : nz hist 1 = 1 := c_nz1
  have hj : ((1 : Fin 3).val + 1 < 3) := by decide
  unfold bonus
  rw [if_pos hj, if_pos hj, e1, e2, e3, e4, rad_one]
  have a1 := m0 7202
  have a2 : 0 ≤ min LL 1 := le_min LL_nn zero_le_one
  have a3 := m0 7201
  have b1 := m1 7202
  have b2 : min LL 1 ≤ 1 := min_le_right _ _
  have b3 := m1 7201
  have := LL_ge
  constructor <;> linarith

lemma b2_le : bonus hist pp 2 ≤ 2 * LL := by
  have e1 : ne hist 2 (pp 2) = 1 := c_ne2
  have e2 : nc hist 2 (pp 2) = 1 := c_nc2
  have hj : ¬ ((2 : Fin 3).val + 1 < 3) := by decide
  unfold bonus
  rw [if_neg hj, if_neg hj, e1, e2]
  have b2 := m1 1
  have := LL_ge
  linarith

lemma cont_est0 : continuation (estimate hist) pp 0 = 1 := by
  have e1 : ne hist 0 0 = 7202 := c_ne0
  unfold continuation estimate
  show (1 - (nc hist 0 0 : ℝ) / ne hist 0 0) * (if (0 : Fin 3).val + 1 < 3 then (ngs hist 0 : ℝ) / ng hist 0 else 0)
    + (nc hist 0 0 : ℝ) / ne hist 0 0 * (1 - (nb hist 0 0 : ℝ) / nc hist 0 0) *
      (if (0 : Fin 3).val + 1 < 3 then (nzs hist 0 : ℝ) / nz hist 0 else 0) = 1
  have hj : ((0 : Fin 3).val + 1 < 3) := by decide
  rw [if_pos hj, if_pos hj, c_nc0, c_ne0, c_ngs0, c_ng0, c_nzs0, c_nz0, c_nb0]
  norm_num

lemma cont_est1_nn : 0 ≤ continuation (estimate hist) pp 1 := by
  unfold continuation estimate
  show 0 ≤ (1 - (nc hist 1 0 : ℝ) / ne hist 1 0) * (if (1 : Fin 3).val + 1 < 3 then (ngs hist 1 : ℝ) / ng hist 1 else 0)
    + (nc hist 1 0 : ℝ) / ne hist 1 0 * (1 - (nb hist 1 0 : ℝ) / nc hist 1 0) *
      (if (1 : Fin 3).val + 1 < 3 then (nzs hist 1 : ℝ) / nz hist 1 else 0)
  have hj : ((1 : Fin 3).val + 1 < 3) := by decide
  rw [if_pos hj, if_pos hj, c_nc1, c_ne1, c_ngs1, c_ng1, c_nzs1, c_nz1, c_nb1]
  norm_num

lemma reach0 {J K : ℕ} (θ : Cascade J K) (p : Action J K) (j : Fin J) (hj : j.val = 0) :
    reach θ p j = 1 := by
  unfold reach
  have : Finset.Iio j = ∅ := by
    ext x; simp only [Finset.mem_Iio, Finset.notMem_empty, iff_false, not_lt]
    rw [Fin.le_def]; omega
  rw [this]; simp

lemma reach1 {K : ℕ} (θ : Cascade 3 K) (p : Action 3 K) : reach θ p 1 = continuation θ p 0 := by
  unfold reach
  have : Finset.Iio (1 : Fin 3) = {0} := by decide
  rw [this]; simp

lemma reach2 {K : ℕ} (θ : Cascade 3 K) (p : Action 3 K) :
    reach θ p 2 = continuation θ p 0 * continuation θ p 1 := by
  unfold reach
  have : Finset.Iio (2 : Fin 3) = {0, 1} := by decide
  rw [this]; simp

lemma th_c0 : continuation th pp 0 = 3 / 4000 := by
  simp [continuation, th, pp]; norm_num

lemma th_c1 : continuation th pp 1 = 3 / 8 := by
  simp [continuation, th, pp]; norm_num

lemma key : ¬ (weightedBonus (estimate hist) hist pp ≤ 4 * ((3 : ℕ) : ℝ) * weightedBonus th hist pp) := by
  unfold weightedBonus
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  rw [reach0 _ _ 0 rfl, reach0 _ _ 0 rfl, reach1, reach1, reach2, reach2, cont_est0, th_c0, th_c1]
  obtain ⟨hb1l, hb1u⟩ := b1_bounds
  have hb0 := b0_le
  have hb2 := b2_le
  have n0 := bonus_nn hist pp 0
  have n2 := bonus_nn hist pp 2
  have n1 := cont_est1_nn
  have p2 : 0 ≤ 1 * continuation (estimate hist) pp 1 * bonus hist pp 2 := mul_nonneg (by linarith) n2
  have := LL_ge
  push_cast
  intro h
  nlinarith

end DG4

open GaoCascadePricing.UCB in
theorem solution : ¬ (∀ {J K : ℕ} (M : Market J K)
    (π : Policy J K) (hπ : IsUCBCascade M π)
    (θ : Cascade J K) (hθ : θ.Valid) (n : ℕ) (h : History J K n)
    (hpossible : 0 < historyWeight θ π h) (hinit : Initialized h) (p : Action J K),
    weightedBonus (estimate h) h p ≤ 4 * (J : ℝ) * weightedBonus θ h p) := by
  intro H
  exact DG4.key (H DG4.mkt DG4.pol DG4.pol_ok DG4.th DG4.th_valid 7202 DG4.hist
    DG4.weight_pos DG4.init_ok DG4.pp)
