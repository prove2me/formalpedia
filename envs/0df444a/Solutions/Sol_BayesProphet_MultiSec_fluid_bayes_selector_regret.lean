-- Prove2me | solution 1 for BayesProphet.MultiSec.fluid_bayes_selector_regret
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T05:55:34.3232+00:00
-- url     : https://prove2.me/submissions/48390375-9978-47cb-bda7-dd46718bd462

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_OnlineProblem
import Definitions.Def_BayesProphet_MultiSec_MultiSecretary
import Theorems.Thm_BayesProphet_MultiSec_cond_disagreement_bound
import Theorems.Thm_BayesProphet_MultiSec_total_disagreement_bound
namespace BayesProphet.MultiSec.MainAux
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

/-- count of future arrivals (times `1..m`) with reward `> v` -/
@[simp] lemma sp_reward_accept (b : ℕ) (j : Fin n) :
    (secretaryProblem r).reward Action.accept b j = r j := rfl
@[simp] lemma sp_reward_reject (b : ℕ) (j : Fin n) :
    (secretaryProblem r).reward Action.reject b j = 0 := rfl
@[simp] lemma sp_trans_accept (b : ℕ) (j : Fin n) :
    (secretaryProblem r).trans Action.accept b j = b - 1 := rfl
@[simp] lemma sp_trans_reject (b : ℕ) (j : Fin n) :
    (secretaryProblem r).trans Action.reject b j = b := rfl

noncomputable def cntGt (θ : ℕ → Fin n) (m : ℕ) (v : ℝ) : ℕ :=
  ((Finset.Ico 1 (m + 1)).filter (fun τ => v < r (θ τ))).card

noncomputable def cntGe (θ : ℕ → Fin n) (m : ℕ) (v : ℝ) : ℕ :=
  ((Finset.Ico 1 (m + 1)).filter (fun τ => v ≤ r (θ τ))).card

lemma cnt_succ_aux (θ : ℕ → Fin n) (m : ℕ) (q : ℕ → Prop) [DecidablePred q] :
    ((Finset.Ico 1 (m + 2)).filter q).card =
      ((Finset.Ico 1 (m + 1)).filter q).card + if q (m + 1) then 1 else 0 := by
  have : Finset.Ico 1 (m + 2) = insert (m + 1) (Finset.Ico 1 (m + 1)) := by
    ext x; simp; omega
  rw [this, Finset.filter_insert]
  have hn : (m + 1) ∉ Finset.filter q (Finset.Ico 1 (m + 1)) := by simp
  split_ifs with h
  · rw [Finset.card_insert_of_notMem hn]
  · simp

lemma cntGt_succ (θ : ℕ → Fin n) (m : ℕ) (v : ℝ) :
    cntGt r θ (m + 1) v = cntGt r θ m v + if v < r (θ (m + 1)) then 1 else 0 :=
  cnt_succ_aux θ m _

lemma cntGe_succ (θ : ℕ → Fin n) (m : ℕ) (v : ℝ) :
    cntGe r θ (m + 1) v = cntGe r θ m v + if v ≤ r (θ (m + 1)) then 1 else 0 :=
  cnt_succ_aux θ m _

lemma real_key (x A d1 d2 : ℝ) (h : d2 ≤ d1) :
    max (x + (A + d1)) (A + d1 + d2) - max (x + A) (A + d1) = max d2 (min x d1) := by
  rcases le_total x d2 with h1 | h1 <;> rcases le_total x d1 with h2 | h2 <;>
    simp only [max_def, min_def] <;> split_ifs <;> linarith

/-- The marginal value of the `b`-th unit of budget. -/
noncomputable def Dl (θ : ℕ → Fin n) (m b : ℕ) : ℝ :=
  (secretaryProblem r).offVal θ m b - (secretaryProblem r).offVal θ m (b - 1)

lemma main_ind (θ : ℕ → Fin n) (m : ℕ) : ∀ b, 1 ≤ b →
    0 ≤ Dl r θ m b ∧ (∀ v : ℝ, 0 ≤ v → (v < Dl r θ m b ↔ b ≤ cntGt r θ m v)) ∧
      (∀ v : ℝ, 0 < v → (v ≤ Dl r θ m b ↔ b ≤ cntGe r θ m v)) := by
  induction m with
  | zero =>
    intro b hb
    have h0 : ∀ c, (secretaryProblem r).offVal θ 0 c = 0 := fun _ => rfl
    have hg : ∀ v, cntGt r θ 0 v = 0 := fun v => by simp [cntGt]
    have hge : ∀ v, cntGe r θ 0 v = 0 := fun v => by simp [cntGe]
    simp only [Dl, h0, hg, hge, sub_self, le_refl, true_and]
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · constructor
      · intro h; linarith
      · intro h; omega
    · constructor
      · intro h; linarith
      · intro h; omega
  | succ m ih =>
    intro b hb
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    rcases Nat.eq_zero_or_pos c with hc | hc
    · subst hc
      obtain ⟨i0, i1, i2⟩ := ih 1 le_rfl
      have hD : Dl r θ (m + 1) 1 = max (r (θ (m + 1))) (Dl r θ m 1) := by
        simp only [Dl, offVal_succ_pos r θ m 1 le_rfl, Nat.sub_self, offVal_zero_budget]
        simp
      rw [hD]
      refine ⟨le_trans i0 (le_max_right _ _), fun v hv => ?_, fun v hv => ?_⟩
      · rw [lt_max_iff, i1 v hv, cntGt_succ]
        by_cases h : v < r (θ (m + 1))
        · simp only [h, if_true, true_or, true_and, true_iff]; omega
        · simp only [h, if_false, false_or, false_and, or_false, add_zero]
      · rw [le_max_iff, i2 v hv, cntGe_succ]
        by_cases h : v ≤ r (θ (m + 1))
        · simp only [h, if_true, true_or, true_and, true_iff]; omega
        · simp only [h, if_false, false_or, false_and, or_false, add_zero]
    · obtain ⟨c, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
      obtain ⟨i0, i1, i2⟩ := ih (c + 1) (by omega)
      obtain ⟨j0, j1, j2⟩ := ih (c + 2) (by omega)
      have hconc : Dl r θ m (c + 2) ≤ Dl r θ m (c + 1) := by
        by_contra hlt
        push Not at hlt
        have := (j1 _ i0).1 hlt
        have := (i1 _ i0).2 (by omega)
        exact lt_irrefl _ this
      have hD : Dl r θ (m + 1) (c + 2) = max (Dl r θ m (c + 2)) (min (r (θ (m + 1))) (Dl r θ m (c + 1))) := by
        have e := real_key (r (θ (m + 1))) ((secretaryProblem r).offVal θ m c) (Dl r θ m (c + 1))
          (Dl r θ m (c + 2)) hconc
        simp only [Dl] at e ⊢
        rw [offVal_succ_pos r θ m (c + 1 + 1) (by omega),
          offVal_succ_pos r θ m (c + 1 + 1 - 1) (by omega)]
        have e1 : c + 1 + 1 - 1 = c + 1 := by omega
        have e2 : c + 1 - 1 = c := by omega
        have e3 : c + 2 - 1 = c + 1 := by omega
        rw [e1, e2]
        rw [e3, e2] at e
        rw [← e]
        congr 1 <;> congr 1 <;> ring
      rw [hD]
      refine ⟨le_trans j0 (le_max_left _ _), fun v hv => ?_, fun v hv => ?_⟩
      · rw [lt_max_iff, lt_min_iff, j1 v hv, i1 v hv, cntGt_succ]
        by_cases h : v < r (θ (m + 1))
        · simp only [h, if_true, true_or, true_and, true_iff]; omega
        · simp only [h, if_false, false_or, false_and, or_false, add_zero]
      · rw [le_max_iff, le_min_iff, j2 v hv, i2 v hv, cntGe_succ]
        by_cases h : v ≤ r (θ (m + 1))
        · simp only [h, if_true, true_or, true_and, true_iff]; omega
        · simp only [h, if_false, false_or, false_and, or_false, add_zero]

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

end Expect

section General
variable {S Θ A : Type*} (P : OnlineProblem S Θ A)

lemma offVal_local (θ θ' : ℕ → Θ) : ∀ t s, (∀ τ, τ ≤ t → θ τ = θ' τ) →
    P.offVal θ t s = P.offVal θ' t s
  | 0, _, _ => rfl
  | t + 1, s, h => by
    simp only [OnlineProblem.offVal]
    rw [h (t + 1) le_rfl]
    congr 1; funext a
    rw [offVal_local θ θ' t _ (fun τ hτ => h τ (by omega))]

lemma stateAux_local (π : Policy S Θ A) (T : ℕ) (s₀ : S) (θ θ' : ℕ → Θ)
    (hπ : ∀ t, ∀ θ θ' : ℕ → Θ, θ t = θ' t → π t θ = π t θ')
    (h : ∀ τ, τ ≤ T → θ τ = θ' τ) : ∀ k, P.stateAux π T s₀ θ k = P.stateAux π T s₀ θ' k
  | 0 => rfl
  | k + 1 => by
    simp only [OnlineProblem.stateAux]
    rw [stateAux_local π T s₀ θ θ' hπ h k, hπ (T - k) θ θ' (h _ (by omega)), h (T - k) (by omega)]

lemma regret_local (π : Policy S Θ A) (T : ℕ) (s₀ : S) (θ θ' : ℕ → Θ)
    (hπ : ∀ t, ∀ θ θ' : ℕ → Θ, θ t = θ' t → π t θ = π t θ')
    (h : ∀ τ, τ ≤ T → θ τ = θ' τ) : P.regret π T s₀ θ = P.regret π T s₀ θ' := by
  unfold OnlineProblem.regret OnlineProblem.onlineValue OnlineProblem.onlineState
  rw [offVal_local P θ θ' T s₀ h]
  congr 1
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have ht' := (Finset.mem_Icc.mp ht).2
  rw [stateAux_local P π T s₀ θ θ' hπ h, hπ t θ θ' (h t ht'), h t ht']

lemma stateAux_shift (π : Policy S Θ A) (T : ℕ) (s : S) (θ : ℕ → Θ) : ∀ k,
    P.stateAux π (T + 1) s θ (k + 1) =
      P.stateAux π T (P.trans (π (T + 1) θ s) s (θ (T + 1))) θ k
  | 0 => by simp [OnlineProblem.stateAux]
  | k + 1 => by
    rw [OnlineProblem.stateAux, stateAux_shift π T s θ k, OnlineProblem.stateAux]
    rw [show T + 1 - (k + 1) = T - k by omega]

lemma regret_succ (π : Policy S Θ A) (T : ℕ) (s : S) (θ : ℕ → Θ) :
    P.regret π (T + 1) s θ =
      P.margComp θ (T + 1) (π (T + 1) θ s) s +
        P.regret π T (P.trans (π (T + 1) θ s) s (θ (T + 1))) θ := by
  unfold OnlineProblem.regret OnlineProblem.margComp
  have hv : P.onlineValue π (T + 1) s θ =
      P.reward (π (T + 1) θ s) s (θ (T + 1)) +
        P.onlineValue π T (P.trans (π (T + 1) θ s) s (θ (T + 1))) θ := by
    unfold OnlineProblem.onlineValue
    rw [Finset.sum_Icc_succ_top (by omega), add_comm]
    congr 1
    · simp [OnlineProblem.onlineState, OnlineProblem.stateAux]
    · refine Finset.sum_congr rfl (fun t ht => ?_)
      have ht' := (Finset.mem_Icc.mp ht).2
      unfold OnlineProblem.onlineState
      rw [show T + 1 - t = (T - t) + 1 by omega, stateAux_shift]
  rw [hv, Nat.add_sub_cancel]
  ring

end General

section Main
variable {n : ℕ} [NeZero n]

lemma fbs_local (p : Fin n → ℝ) : ∀ t, ∀ θ θ' : ℕ → Fin n, θ t = θ' t →
    fluidBayesSelector p t θ = fluidBayesSelector p t θ' := by
  intro t θ θ' h
  funext b
  simp only [fluidBayesSelector, h]

lemma expect_add (p : Fin n → ℝ) (T : ℕ) (F G : (ℕ → Fin n) → ℝ) :
    expect p T (fun θ => F θ + G θ) = expect p T F + expect p T G := by
  unfold expect; rw [← Finset.sum_add_distrib]; congr 1; funext x; ring

lemma expect_smul (p : Fin n → ℝ) (T : ℕ) (c : ℝ) (F : (ℕ → Fin n) → ℝ) :
    expect p T (fun θ => c * F θ) = c * expect p T F := by
  unfold expect; rw [Finset.mul_sum]; congr 1; funext x; ring

lemma expect_finsum (p : Fin n → ℝ) (T : ℕ) (F : Fin n → (ℕ → Fin n) → ℝ) :
    expect p T (fun θ => ∑ j, F j θ) = ∑ j, expect p T (F j) := by
  unfold expect; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]

lemma margComp_le (r : Fin n → ℝ) (hr₀ : ∀ j, 0 ≤ r j) (θ : ℕ → Fin n) (T b : ℕ) (a : Action)
    (ha : a = Action.accept → 1 ≤ b) :
    (secretaryProblem r).margComp θ (T + 1) a b ≤
      Finset.univ.sup' Finset.univ_nonempty r *
        (secretaryProblem r).disagreeInd θ (T + 1) a b := by
  classical
  set R := Finset.univ.sup' Finset.univ_nonempty r with hR
  have hRj : ∀ j, r j ≤ R := fun j => Finset.le_sup' r (Finset.mem_univ j)
  have hR0 : 0 ≤ R := le_trans (hr₀ 0) (hRj 0)
  unfold OnlineProblem.disagreeInd
  split_ifs with hd
  · rw [mul_one]
    unfold OnlineProblem.margComp
    rw [Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos b with hb0 | hb
    · subst hb0
      have : a = Action.reject := by
        cases a
        · exact absurd (ha rfl) (by omega)
        · rfl
      subst this
      simp only [sp_reward_reject, sp_trans_reject, offVal_zero_budget]
      linarith
    · obtain ⟨i0, i1, -⟩ := main_ind r θ T b hb
      have hcnt : cntGt r θ T R = 0 := by
        unfold cntGt
        rw [Finset.card_eq_zero]
        apply Finset.filter_false_of_mem
        intro τ _; exact not_lt.mpr (hRj _)
      have hΔ : Dl r θ T b ≤ R := by
        by_contra hc; push Not at hc
        have := (i1 R hR0).1 hc; omega
      unfold Dl at i0 hΔ
      rw [offVal_succ_pos r θ T b hb]
      have hx := hr₀ (θ (T + 1))
      have hxR := hRj (θ (T + 1))
      cases a
      · simp only [sp_reward_accept, sp_trans_accept]
        apply sub_le_iff_le_add.mpr
        apply max_le <;> linarith
      · simp only [sp_reward_reject, sp_trans_reject]
        apply sub_le_iff_le_add.mpr
        apply max_le <;> linarith
  · rw [mul_zero]
    unfold OnlineProblem.margComp
    unfold OnlineProblem.Disagree at hd
    push Not at hd
    linarith

end Main

end BayesProphet.MultiSec.MainAux

open BayesProphet.MultiSec BayesProphet.MultiSec.MainAux OnlineProblem in
theorem solution {n : ℕ} [NeZero n] (p r : Fin n → ℝ) (hp : ∀ j, 0 < p j)
    (hsum : ∑ j, p j = 1) (hr : Antitone r) (hr₀ : ∀ j, 0 ≤ r j) (T B : ℕ) :
    expectedRegret p r T B ≤
        Finset.univ.sup' Finset.univ_nonempty r * ∑ j ∈ Finset.univ.erase (0 : Fin n), 2 / p j ∧
    Finset.univ.sup' Finset.univ_nonempty r * ∑ j ∈ Finset.univ.erase (0 : Fin n), 2 / p j ≤
        2 * ((n : ℝ) - 1) * Finset.univ.sup' Finset.univ_nonempty r /
          Finset.univ.inf' Finset.univ_nonempty p := by
  classical
  set R := Finset.univ.sup' Finset.univ_nonempty r with hR
  have hR0 : 0 ≤ R := le_trans (hr₀ 0) (Finset.le_sup' r (Finset.mem_univ 0))
  set g : ℕ → ℝ := fun t => ∑ j ∈ Finset.univ.erase (0 : Fin n),
    p j * Real.exp (-(p j ^ 2 * t / 2)) with hg
  -- the disagreement probability at time-to-go `t` with a fixed budget
  have hstep : ∀ t b, 1 ≤ t → expect p t (fun θ => (secretaryProblem r).disagreeInd θ t
      (fluidBayesSelector p t θ b) b) ≤ g t := by
    intro t b ht
    have e : expect p t (fun θ => (secretaryProblem r).disagreeInd θ t
        (fluidBayesSelector p t θ b) b) = disagreeProb p r t b := by
      unfold disagreeProb condDisagreeProb
      have hcancel : ∀ (x : ℝ) (j : Fin n), p j * (x / p j) = x := fun x j => by
        field_simp [(hp j).ne']
      simp only [hcancel]
      rw [← expect_finsum]
      congr 1; funext θ
      simp [Finset.sum_ite_eq]
    rw [e]
    unfold disagreeProb
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin n))]
    rw [(cond_disagreement_bound p r hp hsum hr hr₀ 0 t b ht).1 (by simp), mul_zero, zero_add]
    apply Finset.sum_le_sum
    intro j hj
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h; apply (Finset.mem_erase.mp hj).1; exact Fin.ext (by simpa using h)
    exact mul_le_mul_of_nonneg_left
      ((cond_disagreement_bound p r hp hsum hr hr₀ j t b ht).2 hj0) (hp j).le
  have hsumaux : ∀ (X : Fin n → ℝ) (Y : ℝ),
      ∑ c, p c * (R * X c + Y) = R * ∑ c, p c * X c + Y := by
    intro X Y
    have : ∀ c, p c * (R * X c + Y) = R * (p c * X c) + p c * Y := fun c => by ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hsum, one_mul]
  -- induction on the horizon
  have hmain : ∀ T B, expectedRegret p r T B ≤ R * ∑ t ∈ Finset.Icc 1 T, g t := by
    intro T
    induction T with
    | zero =>
      intro B
      simp [expectedRegret, expect, OnlineProblem.regret, OnlineProblem.onlineValue,
        OnlineProblem.offVal]
    | succ T ih =>
      intro B
      set F : (ℕ → Fin n) → ℝ := fun θ => (secretaryProblem r).disagreeInd θ (T + 1)
        (fluidBayesSelector p (T + 1) θ B) B with hF
      have hc : ∀ c, expect p T (fun θ => (secretaryProblem r).regret (fluidBayesSelector p)
          (T + 1) B (Function.update θ (T + 1) c)) ≤
          R * expect p T (fun θ => F (Function.update θ (T + 1) c)) +
            R * ∑ t ∈ Finset.Icc 1 T, g t := by
        intro c
        set a := fluidBayesSelector p (T + 1) (fun _ => c) B with ha_def
        have ha : ∀ θ : ℕ → Fin n,
            fluidBayesSelector p (T + 1) (Function.update θ (T + 1) c) B = a := by
          intro θ
          rw [fbs_local p (T + 1) _ (fun _ => c) (by simp)]
        have hfeas : a = Action.accept → 1 ≤ B := by
          intro h
          by_contra hB
          have hB0 : B = 0 := by omega
          simp [ha_def, fluidBayesSelector, hB0] at h
        have hpt : ∀ θ : ℕ → Fin n, (secretaryProblem r).regret (fluidBayesSelector p) (T + 1) B
            (Function.update θ (T + 1) c) ≤
            R * F (Function.update θ (T + 1) c) +
              (secretaryProblem r).regret (fluidBayesSelector p) T
                ((secretaryProblem r).trans a B c) θ := by
          intro θ
          rw [regret_succ, hF]
          simp only
          rw [ha θ, Function.update_self]
          rw [regret_local _ _ T _ (Function.update θ (T + 1) c) θ (fbs_local p)
            (fun τ hτ => by rw [Function.update_of_ne (by omega)])]
          have := margComp_le r hr₀ (Function.update θ (T + 1) c) T B a hfeas
          linarith
        refine le_trans (expect_mono p (fun i => (hp i).le) T _ _ hpt) ?_
        rw [expect_add, expect_smul]
        exact add_le_add le_rfl (ih _)
      unfold expectedRegret
      rw [expect_succ]
      refine le_trans (Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hc c)
        (hp c).le)) ?_
      rw [hsumaux (fun c => expect p T (fun θ => F (Function.update θ (T + 1) c))),
        ← expect_succ, Finset.sum_Icc_succ_top (by omega), mul_add, add_comm]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hstep (T + 1) B (by omega)) hR0)
  refine ⟨?_, ?_⟩
  · refine le_trans (hmain T B) ?_
    have htot := (total_disagreement_bound p r hp hsum hr hr₀ T (fun _ => 0)).2
    have hswap : ∑ t ∈ Finset.Icc 1 T, g t = ∑ j ∈ Finset.univ.erase (0 : Fin n),
        p j * ∑ t ∈ Finset.Icc 1 T, Real.exp (-(p j ^ 2 * t / 2)) := by
      simp only [hg, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hswap]
    apply mul_le_mul_of_nonneg_left _ hR0
    refine le_trans htot (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro j _
    have := (hp j).ne'
    field_simp
  · set pm := Finset.univ.inf' Finset.univ_nonempty p with hpm_def
    have hpm : 0 < pm := by
      obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty p
      rw [hpm_def, hj]; exact hp j
    have hle : ∀ j, pm ≤ p j := fun j => Finset.inf'_le p (Finset.mem_univ j)
    have hsum2 : ∑ j ∈ Finset.univ.erase (0 : Fin n), 2 / p j ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin n), 2 / pm :=
      Finset.sum_le_sum (fun j _ => div_le_div_of_nonneg_left (by norm_num) hpm (hle j))
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum2
    have hn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (NeZero.one_le)]; simp
    rw [hn] at hsum2
    calc R * ∑ j ∈ Finset.univ.erase (0 : Fin n), 2 / p j ≤ R * (((n : ℝ) - 1) * (2 / pm)) :=
          mul_le_mul_of_nonneg_left hsum2 hR0
      _ = 2 * ((n : ℝ) - 1) * R / pm := by field_simp
