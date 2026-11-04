-- Prove2me | solution 1 for BayesProphet.MultiSec.cond_disagreement_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T05:49:20.651143+00:00
-- url     : https://prove2.me/submissions/18912edb-4f56-484c-8b11-d139188db12a

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_OnlineProblem
import Definitions.Def_BayesProphet_MultiSec_MultiSecretary
import Theorems.Thm_BayesProphet_MultiSec_offline_satisfaction
import Theorems.Thm_BayesProphet_MultiSec_binomial_chernoff_hoeffding
namespace BayesProphet.MultiSec.CondAux
open BayesProphet.MultiSec OnlineProblem

variable {n : ℕ} (r : Fin n → ℝ)

lemma mem_feas_reject (b : ℕ) : Action.reject ∈ (secretaryProblem r).feasible b := by
  simp [secretaryProblem]

lemma mem_feas_accept (b : ℕ) (hb : 1 ≤ b) : Action.accept ∈ (secretaryProblem r).feasible b := by
  simp [secretaryProblem]; omega

lemma feas_zero (a : Action) (ha : a ∈ (secretaryProblem r).feasible 0) : a = Action.reject := by
  cases a
  · simp [secretaryProblem] at ha
  · rfl

lemma iSup_feas (b : ℕ) (f : Action → ℝ) :
    (⨆ a : (secretaryProblem r).feasible b, f a) =
      if b = 0 then f Action.reject else max (f Action.accept) (f Action.reject) := by
  have hrej := mem_feas_reject r b
  have : Nonempty ((secretaryProblem r).feasible b) := ⟨⟨_, hrej⟩⟩
  have hbdd : BddAbove (Set.range fun a : (secretaryProblem r).feasible b => f a) := by
    refine ⟨max (f Action.accept) (f Action.reject), ?_⟩
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    cases a <;> simp
  split_ifs with hb
  · subst hb
    apply le_antisymm
    · apply ciSup_le
      rintro ⟨a, ha⟩
      cases a
      · exact absurd ha (by simp [secretaryProblem])
      · exact le_rfl
    · exact le_ciSup hbdd (⟨_, hrej⟩ : (secretaryProblem r).feasible 0)
  · have hacc := mem_feas_accept r b (by omega)
    apply le_antisymm
    · apply ciSup_le; rintro ⟨a, ha⟩; cases a <;> simp
    · exact max_le (le_ciSup hbdd (⟨_, hacc⟩ : (secretaryProblem r).feasible b))
        (le_ciSup hbdd (⟨_, hrej⟩ : (secretaryProblem r).feasible b))

lemma offVal_succ (θ : ℕ → Fin n) (t b : ℕ) :
    (secretaryProblem r).offVal θ (t + 1) b =
      if b = 0 then (secretaryProblem r).offVal θ t b
      else max (r (θ (t + 1)) + (secretaryProblem r).offVal θ t (b - 1))
        ((secretaryProblem r).offVal θ t b) := by
  have h := iSup_feas r b (fun a => (secretaryProblem r).reward a b (θ (t + 1)) +
      (secretaryProblem r).offVal θ t ((secretaryProblem r).trans a b (θ (t + 1))))
  rw [OnlineProblem.offVal, h]
  simp [secretaryProblem]

lemma offVal_zero_budget (θ : ℕ → Fin n) (t : ℕ) : (secretaryProblem r).offVal θ t 0 = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [offVal_succ]; simp [ih]

lemma offVal_succ_pos (θ : ℕ → Fin n) (t b : ℕ) (hb : 1 ≤ b) :
    (secretaryProblem r).offVal θ (t + 1) b =
      max (r (θ (t + 1)) + (secretaryProblem r).offVal θ t (b - 1))
        ((secretaryProblem r).offVal θ t b) := by
  rw [offVal_succ, if_neg (by omega)]

@[simp] lemma sp_reward_accept (b : ℕ) (j : Fin n) :
    (secretaryProblem r).reward Action.accept b j = r j := rfl
@[simp] lemma sp_reward_reject (b : ℕ) (j : Fin n) :
    (secretaryProblem r).reward Action.reject b j = 0 := rfl
@[simp] lemma sp_trans_accept (b : ℕ) (j : Fin n) :
    (secretaryProblem r).trans Action.accept b j = b - 1 := rfl
@[simp] lemma sp_trans_reject (b : ℕ) (j : Fin n) :
    (secretaryProblem r).trans Action.reject b j = b := rfl

section Expect
variable {n : ℕ} [NeZero n]

lemma arrivalSeq_snoc (m : ℕ) (y : Fin m → Fin n) (c : Fin n) :
    arrivalSeq (Fin.snoc y c : Fin (m + 1) → Fin n) =
      Function.update (arrivalSeq y) (m + 1) c := by
  funext τ
  by_cases h : τ = m + 1
  · subst h
    rw [Function.update_self]
    unfold arrivalSeq
    rw [dif_pos ⟨by omega, le_rfl⟩]
    have : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := by ext; simp
    rw [this, Fin.snoc_last]
  · rw [Function.update_of_ne h]
    unfold arrivalSeq
    by_cases h2 : 1 ≤ τ ∧ τ ≤ m
    · rw [dif_pos ⟨h2.1, by omega⟩, dif_pos h2]
      have : (⟨τ - 1, by omega⟩ : Fin (m + 1)) = Fin.castSucc ⟨τ - 1, by omega⟩ := rfl
      rw [this, Fin.snoc_castSucc]
    · rw [dif_neg h2, dif_neg (by omega)]

lemma expect_succ (p : Fin n → ℝ) (m : ℕ) (F : (ℕ → Fin n) → ℝ) :
    expect p (m + 1) F =
      ∑ c, p c * expect p m (fun θ => F (Function.update θ (m + 1) c)) := by
  unfold expect
  rw [← (Fin.snocEquiv (fun _ : Fin (m + 1) => Fin n)).sum_comp, Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [show (Fin.snocEquiv fun _ : Fin (m + 1) => Fin n) (c, y) = Fin.snoc y c from rfl]
  rw [Fin.prod_univ_castSucc, Fin.snoc_last, arrivalSeq_snoc]
  simp only [Fin.snoc_castSucc]
  ring

lemma expect_mono (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (m : ℕ) (F G : (ℕ → Fin n) → ℝ)
    (h : ∀ θ, F θ ≤ G θ) : expect p m F ≤ expect p m G := by
  unfold expect
  refine Finset.sum_le_sum (fun x _ => ?_)
  exact mul_le_mul_of_nonneg_left (h _) (Finset.prod_nonneg (fun i _ => hp _))

lemma count_binom (p : Fin n → ℝ) (hsum : ∑ c, p c = 1) (q : Fin n → Prop) [DecidablePred q]
    (m : ℕ) (g : ℕ → ℝ) :
    ∑ y : Fin m → Fin n, (∏ i, p (y i)) * g ((Finset.univ.filter (fun i => q (y i))).card) =
      ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * (∑ c ∈ Finset.univ.filter q, p c) ^ k *
        (1 - ∑ c ∈ Finset.univ.filter q, p c) ^ (m - k) * g k := by
  set α := ∑ c ∈ Finset.univ.filter q, p c with hα
  have hcompl : ∑ c ∈ Finset.univ.filter (fun c => ¬ q c), p c = 1 - α := by
    rw [hα, ← hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ q]; ring
  have key : ∀ s : Finset (Fin m), ∑ y : Fin m → Fin n,
      (∏ i, p (y i)) * (if Finset.univ.filter (fun i => q (y i)) = s then (1 : ℝ) else 0) =
      α ^ s.card * (1 - α) ^ (m - s.card) := by
    intro s
    have h1 : ∀ y : Fin m → Fin n, (∏ i, p (y i)) *
        (if Finset.univ.filter (fun i => q (y i)) = s then (1 : ℝ) else 0) =
        ∏ i, (p (y i) * if (q (y i) ↔ i ∈ s) then (1 : ℝ) else 0) := by
      intro y
      rw [Finset.prod_mul_distrib, Fintype.prod_boole]
      congr 2
      apply propext
      simp [Finset.ext_iff]
    simp_rw [h1]
    rw [← Fintype.prod_sum (fun i c => p c * if (q c ↔ i ∈ s) then (1 : ℝ) else 0)]
    have h2 : ∀ i : Fin m, ∑ c, (p c * if (q c ↔ i ∈ s) then (1 : ℝ) else 0) =
        if i ∈ s then α else 1 - α := by
      intro i
      split_ifs with hi
      · simp [hi, hα, Finset.sum_filter]
      · simp [hi, ← hcompl, Finset.sum_filter]
    simp_rw [h2]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have e1 : (Finset.univ.filter (fun i : Fin m => i ∈ s)).card = s.card := by
      congr 1; ext; simp
    have e2 : (Finset.univ.filter (fun i : Fin m => ¬ i ∈ s)).card = m - s.card := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), e1]
      simp
    rw [e1, e2]
  have hg : ∀ y : Fin m → Fin n, g ((Finset.univ.filter (fun i => q (y i))).card) =
      ∑ s : Finset (Fin m), (if Finset.univ.filter (fun i => q (y i)) = s then (1 : ℝ) else 0) *
        g s.card := by
    intro y
    simp [ite_mul]
  simp_rw [hg, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h3 : ∀ s : Finset (Fin m), ∑ y : Fin m → Fin n, (∏ i, p (y i)) *
      ((if Finset.univ.filter (fun i => q (y i)) = s then (1 : ℝ) else 0) * g s.card) =
      α ^ s.card * (1 - α) ^ (m - s.card) * g s.card := by
    intro s
    rw [← key s, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    ring
  simp_rw [h3]
  have h4 := Finset.sum_powerset_apply_card
    (fun k => α ^ k * (1 - α) ^ (m - k) * g k) (x := (Finset.univ : Finset (Fin m)))
  rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at h4
  rw [h4]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [nsmul_eq_mul]; ring

end Expect

section Main
variable {n : ℕ} [NeZero n]

lemma arrivalSeq_val {m : ℕ} (y : Fin m → Fin n) (i : Fin m) : arrivalSeq y (i.val + 1) = y i := by
  unfold arrivalSeq
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1

lemma count_reindex {m : ℕ} (q : Fin n → Prop) [DecidablePred q] (y : Fin m → Fin n) :
    ((Finset.Ico 1 (m + 1)).filter (fun τ => q (arrivalSeq y τ))).card =
      (Finset.univ.filter (fun i => q (y i))).card := by
  symm
  apply Finset.card_bij (fun i _ => i.val + 1)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [arrivalSeq_val]; exact hi
  · intro a _ b _ h
    exact Fin.ext (by simpa using h)
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_Ico] at hτ
    refine ⟨⟨τ - 1, by omega⟩, ?_, by simp; omega⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := arrivalSeq_val y ⟨τ - 1, by omega⟩
    simp only at this
    rw [show τ - 1 + 1 = τ by omega] at this
    rw [← this]; exact hτ.2

lemma expect_count (p : Fin n → ℝ) (hsum : ∑ c, p c = 1) (q : Fin n → Prop) [DecidablePred q]
    (m : ℕ) (g : ℕ → ℝ) :
    expect p m (fun θ => g ((Finset.Ico 1 (m + 1)).filter (fun τ => q (θ τ))).card) =
      ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * (∑ c ∈ Finset.univ.filter q, p c) ^ k *
        (1 - ∑ c ∈ Finset.univ.filter q, p c) ^ (m - k) * g k := by
  unfold expect
  simp_rw [count_reindex q]
  exact count_binom p hsum q m g

lemma sum_filter_le_one (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hsum : ∑ c, p c = 1)
    (q : Fin n → Prop) [DecidablePred q] :
    0 ≤ ∑ c ∈ Finset.univ.filter q, p c ∧ ∑ c ∈ Finset.univ.filter q, p c ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun i _ => (hp i).le), ?_⟩
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => (hp i).le)

lemma cumProb_eq (p : Fin n → ℝ) (j : Fin n) :
    cumProb p j = (∑ c ∈ Finset.univ.filter (fun c => c < j), p c) + p j := by
  unfold cumProb
  have : Finset.univ.filter (fun i => i ≤ j) = insert j (Finset.univ.filter (fun c => c < j)) := by
    ext x; simp [le_iff_lt_or_eq, or_comm]
  rw [this, Finset.sum_insert (by simp), add_comm]

lemma binom_le_filter (m : ℕ) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (hPQ : ∀ k, P k → Q k) :
    ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * α ^ k * (1 - α) ^ (m - k) *
        (if P k then 1 else 0) ≤
      ∑ k ∈ (Finset.range (m + 1)).filter Q, (m.choose k : ℝ) * α ^ k * (1 - α) ^ (m - k) := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k; simp only [Finset.mem_filter]; exact fun h => ⟨h.1, hPQ k h.2⟩
  · intro k _ _
    have : 0 ≤ 1 - α := by linarith
    positivity

lemma exp_cmp (m : ℕ) (hm : 1 ≤ m) (pj : ℝ) :
    Real.exp (-2 * ((m + 1) * pj / (2 * m)) ^ 2 * m) ≤
      Real.exp (-(pj ^ 2 * ((m + 1 : ℕ) : ℝ) / 2)) := by
  apply Real.exp_le_exp.mpr
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have e : -2 * ((m + 1) * pj / (2 * m)) ^ 2 * m = -(((m + 1) * pj) ^ 2 / (2 * m)) := by
    field_simp
  rw [e]
  push_cast
  rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ m + 1) (sq_nonneg pj)]

end Main

end BayesProphet.MultiSec.CondAux

open BayesProphet.MultiSec BayesProphet.MultiSec.CondAux OnlineProblem in
theorem solution {n : ℕ} [NeZero n] (p r : Fin n → ℝ) (hp : ∀ j, 0 < p j)
    (hsum : ∑ j, p j = 1) (hr : Antitone r) (hr₀ : ∀ j, 0 ≤ r j)
    (j : Fin n) (t b : ℕ) (ht : 1 ≤ t) :
    ((j : ℕ) = 0 → condDisagreeProb p r j t b = 0) ∧
    ((j : ℕ) ≠ 0 → condDisagreeProb p r j t b ≤ Real.exp (-(p j ^ 2 * t / 2))) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  set G : (ℕ → Fin n) → ℝ := fun θ => (secretaryProblem r).disagreeInd
      (Function.update θ (m + 1) j) (m + 1)
      (fluidBayesSelector p (m + 1) (Function.update θ (m + 1) j) b) b with hG
  have hred : condDisagreeProb p r j (m + 1) b = expect p m G := by
    unfold condDisagreeProb
    rw [expect_succ]
    have : ∀ c, p c * expect p m (fun θ => if Function.update θ (m + 1) c (m + 1) = j then
        (secretaryProblem r).disagreeInd (Function.update θ (m + 1) c) (m + 1)
          (fluidBayesSelector p (m + 1) (Function.update θ (m + 1) c) b) b else 0) =
        if c = j then p j * expect p m G else 0 := by
      intro c
      simp only [Function.update_self]
      split_ifs with hc
      · subst hc; rfl
      · simp [expect]
    rw [Finset.sum_congr rfl (fun c _ => this c), Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    field_simp [(hp j).ne']
  have hzero : (∀ θ, G θ = 0) → expect p m G = 0 := by
    intro h; unfold expect; simp [h]
  have hupd_j : ∀ θ : ℕ → Fin n, Function.update θ (m + 1) j (m + 1) = j := fun θ => by simp
  have hupd_ne : ∀ (θ : ℕ → Fin n) τ, τ ∈ Finset.Ico 1 (m + 1) →
      Function.update θ (m + 1) j τ = θ τ := by
    intro θ τ hτ
    rw [Function.update_of_ne]; simp at hτ; omega
  rcases Nat.eq_zero_or_pos b with hb0 | hb
  · -- budget zero: Online rejects and Offline agrees
    subst hb0
    have h0 : ∀ θ, G θ = 0 := by
      intro θ
      simp only [hG, fluidBayesSelector, if_true, disagreeInd, Disagree]
      rw [if_neg]
      simp only [sp_reward_reject, sp_trans_reject, Nat.add_sub_cancel, offVal_zero_budget]
      simp
    rw [hred, hzero h0]
    exact ⟨fun _ => rfl, fun _ => (Real.exp_pos _).le⟩
  have hsat := fun θ => offline_satisfaction r hr₀ (Function.update θ (m + 1) j) (m + 1) b
    (by omega) hb
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · -- the best type is always accepted and Offline agrees
    have h0 : ∀ θ, G θ = 0 := by
      intro θ
      have hacc : fluidBayesSelector p (m + 1) (Function.update θ (m + 1) j) b = Action.accept := by
        simp only [fluidBayesSelector, hupd_j, hj]; simp <;> omega
      simp only [hG, hacc, disagreeInd]
      rw [if_neg]
      rw [(hsat θ).2, hupd_j, not_le]
      have : (Finset.Ico 1 (m + 1)).filter
          (fun τ => r j < r (Function.update θ (m + 1) j τ)) = ∅ := by
        apply Finset.filter_false_of_mem
        intro τ _
        apply not_lt.mpr
        apply hr
        exact Fin.le_def.mpr (by omega)
      rw [this]; simp <;> omega
    rw [hred, hzero h0]
  · have hpj := hp j
    obtain ⟨hα0, hα1⟩ := sum_filter_le_one p hp hsum (fun c => c < j)
    obtain ⟨hβ0, hβ1⟩ := sum_filter_le_one p hp hsum (fun c => c ≤ j)
    have hcum := cumProb_eq p j
    have hcum' : cumProb p j = ∑ c ∈ Finset.univ.filter (fun c => c ≤ j), p c := rfl
    have hmpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    rw [hred]
    by_cases hA : cumProb p j - p j / 2 ≤ (b : ℝ) / ((m + 1 : ℕ) : ℝ)
    · -- Online accepts
      have hacc : ∀ θ, fluidBayesSelector p (m + 1) (Function.update θ (m + 1) j) b =
          Action.accept := by
        intro θ
        simp only [fluidBayesSelector, hupd_j, hj, hA]; simp <;> omega
      have hGle : ∀ θ, G θ ≤ (fun θ => (fun k : ℕ => if b ≤ k then (1 : ℝ) else 0)
          ((Finset.Ico 1 (m + 1)).filter (fun τ => θ τ < j)).card) θ := by
        intro θ
        simp only [hG, hacc, disagreeInd]
        split_ifs with h1 h2
        · exact le_rfl
        · exfalso; apply h2
          rw [(hsat θ).2, hupd_j] at h1
          refine le_trans h1 (Finset.card_le_card ?_)
          intro τ
          simp only [Finset.mem_filter]
          rintro ⟨hτ, hlt⟩
          refine ⟨hτ, ?_⟩
          rw [hupd_ne θ τ hτ] at hlt
          by_contra hc
          exact absurd (hr (not_lt.mp hc)) (not_le.mpr hlt)
        · exact zero_le_one
        · exact le_rfl
      refine le_trans (expect_mono p (fun i => (hp i).le) m _ _ hGle) ?_
      refine le_trans (le_of_eq (expect_count p hsum (fun c => c < j) m
        (fun k => if b ≤ k then 1 else 0))) ?_
      set α := ∑ c ∈ Finset.univ.filter (fun c => c < j), p c with hα
      rcases Nat.eq_zero_or_pos m with hm0 | hm
      · subst hm0
        simp only [zero_add, Finset.sum_range_one]
        rw [if_neg (by omega)]; simp only [mul_zero]; exact (Real.exp_pos _).le
      have hb' : ((m + 1 : ℕ) : ℝ) * (α + p j / 2) ≤ b := by
        rw [hcum] at hA
        rw [le_div_iff₀ hmpos] at hA
        linarith
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      refine le_trans (binom_le_filter m α hα0 hα1 _
        (fun k : ℕ => (m : ℝ) * ((m + 1) * p j / (2 * m)) ≤ (k : ℝ) - m * α) ?_) ?_
      · intro k hk
        have hk' : (b : ℝ) ≤ k := by exact_mod_cast hk
        have e : (m : ℝ) * ((m + 1) * p j / (2 * m)) = (m + 1) * p j / 2 := by
          field_simp
        rw [e]; push_cast at hb'; nlinarith
      · refine le_trans (binomial_chernoff_hoeffding m α ((m + 1) * p j / (2 * m)) hα0 hα1
          (by positivity)).2 ?_
        exact exp_cmp m hm (p j)
    · -- Online rejects
      push Not at hA
      have hrej : ∀ θ, fluidBayesSelector p (m + 1) (Function.update θ (m + 1) j) b =
          Action.reject := by
        intro θ
        have hA' := not_le.mpr hA
        simp only [fluidBayesSelector, hupd_j, hj, hA']; simp <;> omega
      have hGle : ∀ θ, G θ ≤ (fun θ => (fun k : ℕ => if k < b then (1 : ℝ) else 0)
          ((Finset.Ico 1 (m + 1)).filter (fun τ => θ τ ≤ j)).card) θ := by
        intro θ
        simp only [hG, hrej, disagreeInd]
        split_ifs with h1 h2
        · exact le_rfl
        · exfalso; apply h2
          rw [(hsat θ).1, hupd_j] at h1
          refine lt_of_le_of_lt (Finset.card_le_card ?_) h1.2
          intro τ
          simp only [Finset.mem_filter]
          rintro ⟨hτ, hle⟩
          refine ⟨hτ, ?_⟩
          rw [hupd_ne θ τ hτ]
          exact hr hle
        · exact zero_le_one
        · exact le_rfl
      refine le_trans (expect_mono p (fun i => (hp i).le) m _ _ hGle) ?_
      refine le_trans (le_of_eq (expect_count p hsum (fun c => c ≤ j) m
        (fun k => if k < b then 1 else 0))) ?_
      set β := ∑ c ∈ Finset.univ.filter (fun c => c ≤ j), p c with hβ
      have hb' : (b : ℝ) < ((m + 1 : ℕ) : ℝ) * (β - p j / 2) := by
        rw [hcum'] at hA
        rw [div_lt_iff₀ hmpos] at hA
        linarith
      have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
      rcases Nat.eq_zero_or_pos m with hm0 | hm
      · exfalso
        subst hm0
        push_cast at hb'
        linarith
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      refine le_trans (binom_le_filter m β hβ0 hβ1 _
        (fun k : ℕ => (k : ℝ) - m * β ≤ -((m : ℝ) * ((m + 1) * p j / (2 * m)))) ?_) ?_
      · intro k hk
        have hk' : (k : ℝ) + 1 ≤ b := by exact_mod_cast hk
        have e : (m : ℝ) * ((m + 1) * p j / (2 * m)) = (m + 1) * p j / 2 := by
          field_simp
        rw [e]; push_cast at hb'; nlinarith
      · refine le_trans (binomial_chernoff_hoeffding m β ((m + 1) * p j / (2 * m)) hβ0 hβ1
          (by positivity)).1 ?_
        exact exp_cmp m hm (p j)
