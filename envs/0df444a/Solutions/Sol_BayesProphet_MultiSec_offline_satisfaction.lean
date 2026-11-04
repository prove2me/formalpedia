-- Prove2me | solution 1 for BayesProphet.MultiSec.offline_satisfaction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T05:43:59.558924+00:00
-- url     : https://prove2.me/submissions/fb4f4d1d-c2bc-4a34-9606-dfe974ffc79b

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_OnlineProblem
import Definitions.Def_BayesProphet_MultiSec_MultiSecretary

namespace BayesProphet.MultiSec.OffSatAux
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

end BayesProphet.MultiSec.OffSatAux

open BayesProphet.MultiSec BayesProphet.MultiSec.OffSatAux in
theorem solution {n : ℕ} (r : Fin n → ℝ) (hr₀ : ∀ j, 0 ≤ r j)
    (θ : ℕ → Fin n) (t b : ℕ) (ht : 1 ≤ t) (hb : 1 ≤ b) :
    ((secretaryProblem r).Disagree θ t Action.reject b ↔
        0 < r (θ t) ∧ ((Finset.Ico 1 t).filter (fun τ => r (θ t) ≤ r (θ τ))).card < b) ∧
    ((secretaryProblem r).Disagree θ t Action.accept b ↔
        b ≤ ((Finset.Ico 1 t).filter (fun τ => r (θ t) < r (θ τ))).card) := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  obtain ⟨i0, i1, i2⟩ := main_ind r θ m b hb
  have hV := offVal_succ_pos r θ m b hb
  simp only [OnlineProblem.Disagree, Nat.add_sub_cancel]
  simp only [sp_reward_accept, sp_reward_reject, sp_trans_accept, sp_trans_reject, hV]
  have hx := hr₀ (θ (m + 1))
  unfold Dl at i0 i1 i2
  constructor
  · simp only [zero_add, lt_max_iff, lt_self_iff_false, or_false]
    rcases hx.lt_or_eq with hpos | hzero
    · have := i2 _ hpos
      unfold cntGe at this
      constructor
      · intro h
        refine ⟨hpos, ?_⟩
        by_contra hc; push Not at hc
        have := this.2 hc; linarith
      · rintro ⟨-, h⟩
        by_contra hc; push Not at hc
        have := this.1 (by linarith); omega
    · rw [← hzero]
      constructor
      · intro h; linarith
      · rintro ⟨h, -⟩; exact absurd h (lt_irrefl _)
  · simp only [lt_max_iff, lt_self_iff_false, false_or]
    have := i1 _ hx
    unfold cntGt at this
    rw [← this]
    constructor <;> intro h <;> linarith
