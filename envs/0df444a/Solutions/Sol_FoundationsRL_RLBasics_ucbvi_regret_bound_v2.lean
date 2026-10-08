-- Prove2me | solution 1 for FoundationsRL.RLBasics.ucbvi_regret_bound_v2
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T19:01:42.243881+00:00
-- url     : https://prove2.me/submissions/a41ed371-2a32-4423-81af-942da1a981ec

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI_v2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Cex3b
open FoundationsRL.RLBasics

section Gen
variable {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]

/-- state sequence of a trajectory tail `ρ` started at `s`. -/
def st {n : ℕ} (s : S) (ρ : Fin n → A × S) (i : Fin n) : S :=
  if h : i.1 = 0 then s else (ρ ⟨i.1 - 1, by omega⟩).2

lemma st_succ {n : ℕ} (s : S) (x : A × S) (ρ : Fin n → A × S) (i : Fin n) :
    st s (Fin.cons x ρ : Fin (n + 1) → A × S) i.succ = st x.2 ρ i := by
  unfold st
  simp only [Fin.val_succ, Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel]
  by_cases hi : i.1 = 0
  · rw [dif_pos hi]
    have : (⟨i.1, by omega⟩ : Fin (n + 1)) = 0 := Fin.ext hi
    rw [this, Fin.cons_zero]
  · rw [dif_neg hi]
    have : (⟨i.1, by omega⟩ : Fin (n + 1)) = (⟨i.1 - 1, by omega⟩ : Fin n).succ := by
      ext; simp; omega
    rw [this, Fin.cons_succ]

lemma st_zero {n : ℕ} (s : S) (ρ : Fin (n + 1) → A × S) : st s ρ 0 = s := by
  simp [st]

lemma sum_cons {X : Type} [Fintype X] {n : ℕ} (F : (Fin (n + 1) → X) → ℝ) :
    ∑ ρ : Fin (n + 1) → X, F ρ = ∑ x : X, ∑ ρ' : Fin n → X, F (Fin.cons x ρ') := by
  rw [← (Fin.consEquiv (fun _ => X)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma tail_sum (K : ℕ → S → A × S → ℝ) (hK : ∀ k s, ∑ x, K k s x = 1) :
    ∀ (n : ℕ) (off : ℕ) (s : S),
      ∑ ρ : Fin n → A × S, ∏ i : Fin n, K (off + i.1) (st s ρ i) (ρ i) = 1 := by
  intro n
  induction n with
  | zero => intro off s; simp
  | succ n ih =>
    intro off s
    rw [sum_cons]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, st_zero, st_succ,
      Fin.val_zero, Fin.val_succ, add_zero]
    calc ∑ x : A × S, ∑ ρ' : Fin n → A × S,
          K off s x * ∏ i : Fin n, K (off + (i.1 + 1)) (st x.2 ρ' i) (ρ' i)
        = ∑ x : A × S, K off s x *
            ∑ ρ' : Fin n → A × S, ∏ i : Fin n, K ((off + 1) + i.1) (st x.2 ρ' i) (ρ' i) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun ρ _ => ?_)
          congr 1
          refine Finset.prod_congr rfl (fun i _ => ?_)
          congr 1; omega
      _ = 1 := by simp [ih, hK]

lemma first_sum (K : ℕ → S → A × S → ℝ) (hK : ∀ k s, ∑ x, K k s x = 1) (n : ℕ)
    (s : S) (w : A × S → ℝ) :
    ∑ ρ : Fin (n + 1) → A × S, w (ρ 0) * ∏ i : Fin (n + 1), K i.1 (st s ρ i) (ρ i) =
      ∑ x : A × S, w x * K 0 s x := by
  rw [sum_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, st_zero, st_succ,
    Fin.val_zero, Fin.val_succ]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have := tail_sum K hK n 1 x.2
  calc ∑ ρ' : Fin n → A × S, w x * (K 0 s x * ∏ i : Fin n, K (i.1 + 1) (st x.2 ρ' i) (ρ' i))
      = w x * K 0 s x * ∑ ρ' : Fin n → A × S, ∏ i : Fin n, K (1 + i.1) (st x.2 ρ' i) (ρ' i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun ρ _ => ?_)
        rw [mul_assoc]; congr 2
        refine Finset.prod_congr rfl (fun i _ => ?_)
        congr 1; omega
    _ = w x * K 0 s x := by rw [this, mul_one]

variable {H : ℕ}

lemma stateAt_eq (τ : Trajectory S A H) (i : Fin H) : stateAt τ i.1 = st τ.1 τ.2 i := by
  unfold st
  rcases i with ⟨i, hi⟩
  cases i with
  | zero => simp [stateAt]
  | succ j =>
    simp [stateAt, nextStateAt]
    rw [dif_pos (by omega)]

lemma actionAt_eq (τ : Trajectory S A H) (i : Fin H) : actionAt τ i.1 = (τ.2 i).1 := by
  simp [actionAt]

lemma nextStateAt_eq (τ : Trajectory S A H) (i : Fin H) : nextStateAt τ i.1 = (τ.2 i).2 := by
  simp [nextStateAt]

/-- `trajProb` against a weight depending only on the first layer. -/
lemma traj_sum (n : ℕ) (M : EpisodicMDP S A (n + 1)) (π : Policy S A (n + 1))
    (hπ : ∀ h s, ∑ a, π h s a = 1) (w : S → A → S → ℝ) :
    ∑ τ : Trajectory S A (n + 1), trajProb M π τ * w τ.1 (actionAt τ 0) (nextStateAt τ 0) =
      ∑ s, ∑ a, ∑ s', M.d1 s * π 0 s a * M.P 0 s a s' * w s a s' := by
  have hK : ∀ k s, ∑ x : A × S, π k s x.1 * M.P k s x.1 x.2 = 1 := by
    intro k s
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, M.P_sum_one, mul_one, hπ]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have key := first_sum (fun k s x => π k s x.1 * M.P k s x.1 x.2) hK n s
    (fun x => M.d1 s * w s x.1 x.2)
  have e1 : ∀ ρ : Fin (n + 1) → A × S, trajProb M π (s, ρ) *
      w (s, ρ).1 (actionAt (s, ρ) 0) (nextStateAt (s, ρ) 0) =
      M.d1 s * w s (ρ 0).1 (ρ 0).2 * ∏ i : Fin (n + 1), π i.1 (st s ρ i) (ρ i).1 *
        M.P i.1 (st s ρ i) (ρ i).1 (ρ i).2 := by
    intro ρ
    have ha := actionAt_eq (s, ρ) (0 : Fin (n + 1))
    have hn := nextStateAt_eq (s, ρ) (0 : Fin (n + 1))
    simp only [Fin.val_zero] at ha hn
    rw [ha, hn]
    unfold trajProb
    simp only [stateAt_eq, actionAt_eq, nextStateAt_eq]
    ring
  simp only [e1]
  rw [key, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun s' _ => ?_))
  ring

/-- total mass identity for histories, for any weight with per-step mass 1. -/
lemma hist_sum (M : EpisodicMDP S A H) (L : Learner S A H) (w : Trajectory S A H → ℝ)
    (hw : ∀ hist, ∑ τ, trajProb M (L hist) τ * w τ = 1) :
    ∀ n : ℕ, ∑ h : Fin n → Trajectory S A H, historyProb M L h * ∏ t, w (h t) = 1 := by
  intro n
  induction n with
  | zero => simp [historyProb]
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ => Trajectory S A H)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl (fun h' _ => ?_)) ih
    have hof : ∀ τ, List.ofFn ((Fin.snocEquiv (fun _ => Trajectory S A H)) (τ, h')) =
        List.ofFn h' ++ [τ] := by
      intro τ
      rw [List.ofFn_succ']
      simp [Fin.snocEquiv]
    have hhp : ∀ τ, historyProb M L ((Fin.snocEquiv (fun _ => Trajectory S A H)) (τ, h')) =
        historyProb M L h' * trajProb M (L (List.ofFn h')) τ := by
      intro τ
      unfold historyProb
      rw [Fin.prod_univ_castSucc, hof]
      congr 1
      · refine Finset.prod_congr rfl (fun t _ => ?_)
        have ht : t.1 ≤ (List.ofFn h').length := by simp [t.2.le]
        simp only [Fin.val_castSucc]
        rw [List.take_append_of_le_length ht]
        simp [Fin.snocEquiv]
      · have ht : (Fin.last n).1 ≤ (List.ofFn h').length := by simp
        rw [List.take_append_of_le_length ht]
        simp [Fin.snocEquiv, List.take_of_length_le]
    have hprod : ∀ τ, ∏ t, w ((Fin.snocEquiv (fun _ => Trajectory S A H)) (τ, h') t) =
        (∏ t, w (h' t)) * w τ := by
      intro τ; rw [Fin.prod_univ_castSucc]; simp [Fin.snocEquiv]
    simp only [hhp, hprod]
    have := hw (List.ofFn h')
    calc ∑ τ, historyProb M L h' * trajProb M (L (List.ofFn h')) τ * ((∏ t, w (h' t)) * w τ)
        = historyProb M L h' * (∏ t, w (h' t)) *
            ∑ τ, trajProb M (L (List.ofFn h')) τ * w τ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun τ _ => by ring)
      _ = _ := by rw [this, mul_one]

end Gen


open FoundationsRL.RLBasics


noncomputable def Pm (b : Bool) (h : ℕ) (s : Fin 3) (a : Bool) (s' : Fin 3) : ℝ :=
  if h = 0 then
    (if s = 0 ∧ a = !b then (if s' = 1 then 1/10 else if s' = 2 then 9/10 else 0)
     else if s' = 2 then 1 else 0)
  else if s' = s then 1 else 0

noncomputable def Rm (b : Bool) (h : ℕ) (s : Fin 3) (a : Bool) : ℝ :=
  if h = 0 then (if s = 0 ∧ a = b then 9/10 else 0) else if s = 1 then 1 else 0

noncomputable def dm (s : Fin 3) : ℝ := if s = 0 then 1 else 0

noncomputable def Mm (b : Bool) : EpisodicMDP (Fin 3) Bool 11 where
  P := Pm b
  R := Rm b
  d1 := dm
  P_nonneg := by intro h s a s'; unfold Pm; split_ifs <;> norm_num
  P_sum_one := by
    intro h s a
    simp only [Pm, Fin.sum_univ_three]
    by_cases h0 : h = 0
    · subst h0
      fin_cases s <;> cases a <;> cases b <;> simp <;> norm_num
    · fin_cases s <;> simp [h0]
  d1_nonneg := by intro s; unfold dm; split_ifs <;> norm_num
  d1_sum_one := by simp [dm, Fin.sum_univ_three]

@[simp] lemma Mm_P (b : Bool) : (Mm b).P = Pm b := rfl
@[simp] lemma Mm_R (b : Bool) : (Mm b).R = Rm b := rfl
@[simp] lemma Mm_d1 (b : Bool) : (Mm b).d1 = dm := rfl

lemma vaux (b : Bool) (π : Policy (Fin 3) Bool 11) (hπ : ∀ h, h < 11 → ∀ s, ∑ a, π h s a = 1) :
    ∀ k, k ≤ 10 → valueAux (Mm b) π k 1 = k ∧ valueAux (Mm b) π k 2 = 0 ∧
      valueAux (Mm b) π k 0 = 0 := by
  intro k
  induction k with
  | zero => intro _; simp [valueAux]
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2, h0⟩ := ih (by omega)
    have hl : 11 - 1 - k ≠ 0 := by omega
    have hs := hπ (11 - 1 - k) (by omega)
    refine ⟨?_, ?_, ?_⟩
    · show ∑ a, π (11 - 1 - k) 1 a * (Rm b (11 - 1 - k) 1 a +
          ∑ s', Pm b (11 - 1 - k) 1 a s' * valueAux (Mm b) π k s') = ((k + 1 : ℕ) : ℝ)
      calc _ = ∑ a, π (11 - 1 - k) 1 a * (1 + (k : ℝ)) := Finset.sum_congr rfl (fun a _ => by
              congr 1; simp [Rm, Pm, hl, Fin.sum_univ_three, h1, h2, h0])
        _ = _ := by rw [← Finset.sum_mul, hs]; push_cast; ring
    · show ∑ a, π (11 - 1 - k) 2 a * (Rm b (11 - 1 - k) 2 a +
          ∑ s', Pm b (11 - 1 - k) 2 a s' * valueAux (Mm b) π k s') = 0
      exact Finset.sum_eq_zero (fun a _ => by simp [Rm, Pm, hl, Fin.sum_univ_three, h1, h2, h0])
    · show ∑ a, π (11 - 1 - k) 0 a * (Rm b (11 - 1 - k) 0 a +
          ∑ s', Pm b (11 - 1 - k) 0 a s' * valueAux (Mm b) π k s') = 0
      exact Finset.sum_eq_zero (fun a _ => by simp [Rm, Pm, hl, Fin.sum_univ_three, h1, h2, h0])

lemma V0 (b : Bool) (π : Policy (Fin 3) Bool 11) (hπ : ∀ h, h < 11 → ∀ s, ∑ a, π h s a = 1) :
    V (Mm b) π 0 0 = π 0 0 b * (9/10) + π 0 0 (!b) := by
  obtain ⟨h1, h2, h0⟩ := vaux b π hπ 10 le_rfl
  show ∑ a, π (11 - 1 - 10) 0 a * (Rm b (11 - 1 - 10) 0 a +
          ∑ s', Pm b (11 - 1 - 10) 0 a s' * valueAux (Mm b) π 10 s') = _
  have e : ∀ a, Rm b (11 - 1 - 10) 0 a +
          ∑ s', Pm b (11 - 1 - 10) 0 a s' * valueAux (Mm b) π 10 s' =
          if a = b then 9/10 else 1 := by
    intro a
    cases a <;> cases b <;> simp [Rm, Pm, Fin.sum_univ_three, h1, h2, h0] <;> norm_num
  simp only [e]
  cases b <;> simp <;> ring

lemma V0x (b : Bool) (π : Policy (Fin 3) Bool 11) (hπ : ∀ h, h < 11 → ∀ s, ∑ a, π h s a = 1)
    (s : Fin 3) (hs : s ≠ 0) : V (Mm b) π 0 s = 0 := by
  obtain ⟨h1, h2, h0⟩ := vaux b π hπ 10 le_rfl
  show ∑ a, π (11 - 1 - 10) s a * (Rm b (11 - 1 - 10) s a +
          ∑ s', Pm b (11 - 1 - 10) s a s' * valueAux (Mm b) π 10 s') = 0
  exact Finset.sum_eq_zero (fun a _ => by simp [Rm, Pm, hs, Fin.sum_univ_three, h1, h2, h0])

lemma Q0 (b : Bool) (π : Policy (Fin 3) Bool 11) (hπ : ∀ h, h < 11 → ∀ s, ∑ a, π h s a = 1)
    (s : Fin 3) (a : Bool) :
    Q (Mm b) π 0 s a = if s = 0 then (if a = b then 9/10 else 1) else 0 := by
  obtain ⟨h1, h2, h0⟩ := vaux b π hπ 10 le_rfl
  show (if 0 < 11 then Rm b 0 s a + ∑ s', Pm b 0 s a s' * valueAux (Mm b) π (11 - (0 + 1)) s'
    else 0) = _
  simp only [show 11 - (0 + 1) = 10 from rfl, if_pos (show 0 < 11 by norm_num)]
  fin_cases s <;> cases a <;> cases b <;> simp [Rm, Pm, Fin.sum_univ_three, h1, h2, h0] <;> norm_num

lemma detPolicy_sum (f : ℕ → Fin 3 → Bool) (h : ℕ) (s : Fin 3) :
    ∑ a, (detPolicy f : Policy (Fin 3) Bool 11) h s a = 1 := by
  simp [detPolicy]

lemma Vstar0 (b : Bool) (s : Fin 3) :
    Vstar (Mm b) 0 s = if s = 0 then 1 else 0 := by
  haveI : Nonempty {π : Policy (Fin 3) Bool 11 // IsPolicy 11 π} :=
    ⟨⟨detPolicy (fun _ _ => b), fun h _ s => ⟨fun a => by
      simp only [detPolicy]; split_ifs <;> norm_num, detPolicy_sum _ h s⟩⟩⟩
  have hQ : ∀ a, Qstar (Mm b) 0 s a = if s = 0 then (if a = b then 9/10 else 1) else 0 := by
    intro a
    unfold Qstar
    rw [show (fun π : {π : Policy (Fin 3) Bool 11 // IsPolicy 11 π} => Q (Mm b) π.1 0 s a) =
      fun _ => (if s = 0 then (if a = b then (9/10 : ℝ) else 1) else 0) from
      funext fun π => Q0 b π.1 (fun h hh s => (π.2 h hh s).2) s a]
    exact ciSup_const
  unfold Vstar
  simp only [hQ]
  apply le_antisymm
  · apply ciSup_le; intro a; split_ifs <;> norm_num
  · have hb : BddAbove (Set.range fun a : Bool =>
        (if s = 0 then (if a = b then (9/10 : ℝ) else 1) else 0)) := (Set.finite_range _).bddAbove
    refine le_trans ?_ (le_ciSup hb (!b))
    split_ifs <;> simp_all

abbrev Tr := Trajectory (Fin 3) Bool 11

noncomputable def Lg (δ : ℝ) (T : ℕ) : ℝ := Real.log (132 * (T : ℝ) / δ)

lemma countSAS_good (hist : List Tr) (hG : ∀ τ ∈ hist, nextStateAt τ 0 = (2 : Fin 3))
    (a : Bool) (s' : Fin 3) :
    countSAS hist 0 0 a s' = if s' = 2 then countSA hist 0 0 a else 0 := by
  unfold countSAS countSA
  split_ifs with hs
  · subst hs
    congr 1
    apply List.filter_congr
    intro τ hτ
    simp [hG τ hτ]
  · rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro τ hτ
    have h2 := hG τ hτ
    simp only [decide_eq_true_eq, not_and]
    intro _ _ h3
    exact hs (h3 ▸ h2)

lemma estExp_good (hist : List Tr) (hG : ∀ τ ∈ hist, nextStateAt τ 0 = (2 : Fin 3))
    (a : Bool) (hn : countSA hist 0 0 a ≠ 0) (f : Fin 3 → ℝ) :
    estExp hist 0 0 a f = f 2 := by
  unfold estExp
  simp only [hn, if_false, countSAS_good hist hG, Fin.sum_univ_three]
  have hn' : (countSA hist 0 0 a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp
  field_simp

lemma bonus_nonneg (δ : ℝ) (a b c d n : ℕ) : 0 ≤ bonus δ a b c d n := by
  unfold bonus; positivity

lemma bonus_eq (δ : ℝ) (T n : ℕ) :
    bonus δ (Fintype.card (Fin 3)) (Fintype.card Bool) 11 T n = 2 * Real.sqrt (Lg δ T / n) := by
  simp only [bonus, Lg, Fintype.card_fin, Fintype.card_bool]
  norm_num

lemma bonus_le (δ : ℝ) (T n : ℕ) (hn : 0 < n) (h5 : 5 * Lg δ T ≤ n) :
    bonus δ (Fintype.card (Fin 3)) (Fintype.card Bool) 11 T n ≤ 9/10 := by
  rw [bonus_eq]
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have : Real.sqrt (Lg δ T / n) ≤ 9/20 := by
    calc Real.sqrt (Lg δ T / n) ≤ Real.sqrt ((9/20) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [div_le_iff₀ hnr]
          nlinarith
      _ = 9/20 := Real.sqrt_sq (by norm_num)
  linarith

lemma ucbQ00 (b : Bool) (δ : ℝ) (T : ℕ) (hist : List Tr) (a : Bool) :
    ucbQ (Mm b) (Rm b) δ T hist 0 0 a =
      if countSA hist 0 0 a = 0 then 1 else
        min 1 (Rm b 0 0 a + estExp hist 0 0 a
            (fun s' => ⨆ a', ucbQ (Mm b) (Rm b) δ T hist (0 + 1) s' a') +
          bonus δ (Fintype.card (Fin 3)) (Fintype.card Bool) 11 T (countSA hist 0 0 a)) := by
  rw [ucbQ.eq_1, dif_pos (by norm_num : (0 : ℕ) < 11)]

lemma argmax_two (f : Bool → ℝ) (b : Bool) (h : f (!b) ≤ f b) :
    List.argmax f [b, !b] = some b := by
  simp [List.argmax, List.foldl, List.argAux]
  exact h

lemma greedy_b (b : Bool) (hl : (Finset.univ : Finset Bool).toList = [b, !b]) (δ : ℝ) (T : ℕ)
    (hist : List Tr) (hG : ∀ τ ∈ hist, nextStateAt τ 0 = (2 : Fin 3))
    (hpos : 0 < countSA hist 0 0 (!b)) (h5 : 5 * Lg δ T ≤ countSA hist 0 0 (!b)) :
    ucbGreedy (Mm b) (Rm b) δ T hist 0 0 = b := by
  have hle : ucbQ (Mm b) (Rm b) δ T hist 0 0 (!b) ≤ ucbQ (Mm b) (Rm b) δ T hist 0 0 b := by
    rw [ucbQ00, ucbQ00, if_neg hpos.ne']
    by_cases hb : countSA hist 0 0 b = 0
    · rw [if_pos hb]; exact min_le_left _ _
    · rw [if_neg hb]
      apply min_le_min_left
      rw [estExp_good hist hG _ hpos.ne', estExp_good hist hG _ hb]
      have h1 := bonus_le δ T _ hpos h5
      have h2 := bonus_nonneg δ (Fintype.card (Fin 3)) (Fintype.card Bool) 11 T (countSA hist 0 0 b)
      have hr1 : Rm b 0 0 (!b) = 0 := by cases b <;> simp [Rm]
      have hr2 : Rm b 0 0 b = 9/10 := by simp [Rm]
      rw [hr1, hr2]; linarith
  unfold ucbGreedy
  rw [hl, argmax_two _ b hle]
  rfl

lemma countSA_append (l : List Tr) (τ : Tr) (a : Bool) :
    countSA (l ++ [τ]) 0 0 a =
      countSA l 0 0 a + if stateAt τ 0 = 0 ∧ actionAt τ 0 = a then 1 else 0 := by
  unfold countSA
  rw [List.filter_append, List.length_append]
  congr 1
  split_ifs with h
  · simp [h]
  · simp [h]


section Supp

lemma supp (b : Bool) (δ : ℝ) (T : ℕ) {n : ℕ} (h : Fin n → Tr)
    (hp : historyProb (Mm b) (ucbviLearner (Mm b) (Rm b) δ T) h ≠ 0) (t : Fin n) :
    (h t).1 = 0 ∧
      actionAt (h t) 0 = ucbGreedy (Mm b) (Rm b) δ T ((List.ofFn h).take t.1) 0 0 := by
  unfold historyProb at hp
  have ht := Finset.prod_ne_zero_iff.mp hp t (Finset.mem_univ _)
  unfold trajProb at ht
  have hd := left_ne_zero_of_mul ht
  have hpr := right_ne_zero_of_mul ht
  have h0 := Finset.prod_ne_zero_iff.mp hpr (0 : Fin 11) (Finset.mem_univ _)
  have hπ := left_ne_zero_of_mul h0
  have hs : (h t).1 = 0 := by
    by_contra hc; apply hd; simp [dm, hc]
  refine ⟨hs, ?_⟩
  simp only [ucbviLearner, detPolicy, Fin.val_zero] at hπ
  by_contra hc
  apply hπ
  have : stateAt (h t) 0 = 0 := hs
  simp [this, hc]

lemma take_succ_ofFn {n : ℕ} (h : Fin n → Tr) (k : ℕ) (hk : k < n) :
    (List.ofFn h).take (k + 1) = (List.ofFn h).take k ++ [h ⟨k, hk⟩] := by
  rw [List.take_add_one]; simp [hk]

lemma cnt_step (b : Bool) (δ : ℝ) (T : ℕ) {n : ℕ} (h : Fin n → Tr)
    (hp : historyProb (Mm b) (ucbviLearner (Mm b) (Rm b) δ T) h ≠ 0) (k : ℕ) (hk : k < n) :
    countSA ((List.ofFn h).take (k + 1)) 0 0 (!b) = countSA ((List.ofFn h).take k) 0 0 (!b) +
      if actionAt (h ⟨k, hk⟩) 0 = !b then 1 else 0 := by
  rw [take_succ_ofFn h k hk, countSA_append]
  have hs : stateAt (h ⟨k, hk⟩) 0 = 0 := (supp b δ T h hp ⟨k, hk⟩).1
  congr 1
  by_cases ha : actionAt (h ⟨k, hk⟩) 0 = !b
  · rw [if_pos ⟨hs, ha⟩, if_pos ha]
  · rw [if_neg (fun hh => ha hh.2), if_neg ha]

lemma good_take {n : ℕ} (h : Fin n → Tr) (hF : ∀ t, nextStateAt (h t) 0 = (2 : Fin 3)) (k : ℕ) :
    ∀ τ ∈ (List.ofFn h).take k, nextStateAt τ 0 = (2 : Fin 3) := by
  intro τ hτ
  have := List.mem_of_mem_take hτ
  rw [List.mem_ofFn] at this
  obtain ⟨i, rfl⟩ := this
  exact hF i

lemma cnt_le (b : Bool) (hl : (Finset.univ : Finset Bool).toList = [b, !b]) (δ : ℝ) (T : ℕ)
    {n : ℕ} (h : Fin n → Tr)
    (hp : historyProb (Mm b) (ucbviLearner (Mm b) (Rm b) δ T) h ≠ 0)
    (hF : ∀ t, nextStateAt (h t) 0 = (2 : Fin 3)) (N : ℕ) (hN1 : 1 ≤ N) (hN : 5 * Lg δ T ≤ N) :
    ∀ k, k ≤ n → countSA ((List.ofFn h).take k) 0 0 (!b) ≤ N := by
  intro k
  induction k with
  | zero => intro _; simp [countSA]
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    rw [cnt_step b δ T h hp k (by omega)]
    by_cases hlt : countSA ((List.ofFn h).take k) 0 0 (!b) < N
    · split_ifs <;> omega
    · have heq : countSA ((List.ofFn h).take k) 0 0 (!b) = N := by omega
      have hg := greedy_b b hl δ T _ (good_take h hF k) (by omega) (by rw [heq]; exact hN)
      have ha := (supp b δ T h hp ⟨k, by omega⟩).2
      simp only at ha
      rw [ha, hg, if_neg (by cases b <;> simp)]
      omega

lemma cnt_sum (b : Bool) (δ : ℝ) (T : ℕ) {n : ℕ} (h : Fin n → Tr)
    (hp : historyProb (Mm b) (ucbviLearner (Mm b) (Rm b) δ T) h ≠ 0) :
    ∀ k, k ≤ n →
      (∑ i ∈ Finset.range k, (if hi : i < n then
          (if actionAt (h ⟨i, hi⟩) 0 = !b then (1 : ℝ) else 0) else 0)) =
        countSA ((List.ofFn h).take k) 0 0 (!b) ∧
      (∏ i ∈ Finset.range k, (if hi : i < n then
          (if actionAt (h ⟨i, hi⟩) 0 = !b then (10/9 : ℝ) else 1) else 1)) =
        (10/9 : ℝ) ^ countSA ((List.ofFn h).take k) 0 0 (!b) := by
  intro k
  induction k with
  | zero => intro _; simp [countSA]
  | succ k ih =>
    intro hk
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [Finset.sum_range_succ, Finset.prod_range_succ, ih1, ih2,
      cnt_step b δ T h hp k (by omega), dif_pos (by omega : k < n), dif_pos (by omega : k < n)]
    split_ifs <;> push_cast <;> constructor <;> ring

lemma regret_eq (b : Bool) (δ : ℝ) (T : ℕ) (h : Fin T → Tr)
    (hp : historyProb (Mm b) (ucbviLearner (Mm b) (Rm b) δ T) h ≠ 0) :
    regret (Mm b) (Rm b) δ T h =
      ∑ t : Fin T, (1/10 - (1/10) * (if actionAt (h t) 0 = !b then (1 : ℝ) else 0)) := by
  unfold regret
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have ha := (supp b δ T h hp t).2
  have hV := V0 b (ucbviLearner (Mm b) (Rm b) δ T ((List.ofFn h).take t.1))
    (fun hh _ s => detPolicy_sum _ hh s)
  simp only [Fin.sum_univ_three, Mm_d1, dm, Vstar0]
  simp only [Fin.isValue, if_true, one_mul, Fin.reduceEq, if_false, zero_mul, add_zero, hV]
  simp only [ucbviLearner, detPolicy, ← ha]
  generalize actionAt (h t) 0 = x
  cases b <;> cases x <;> norm_num

noncomputable def wt (b : Bool) (_s : Fin 3) (a : Bool) (s' : Fin 3) : ℝ :=
  if s' = 2 then (if a = !b then 10/9 else 1) else 0

lemma hw_wt (b : Bool) (δ : ℝ) (T : ℕ) (hist : List Tr) :
    ∑ τ, trajProb (Mm b) (ucbviLearner (Mm b) (Rm b) δ T hist) τ *
      wt b τ.1 (actionAt τ 0) (nextStateAt τ 0) = 1 := by
  rw [traj_sum 10 (Mm b) (ucbviLearner (Mm b) (Rm b) δ T hist)
    (fun h s => detPolicy_sum (ucbGreedy (Mm b) (Rm b) δ T hist) h s) (wt b)]
  simp only [Fin.sum_univ_three, Mm_d1, Mm_P, dm, ucbviLearner, detPolicy, wt, Pm]
  generalize ucbGreedy (Mm b) (Rm b) δ T hist 0 0 = g
  cases b <;> cases g <;> simp <;> norm_num

lemma hw_one (b : Bool) (δ : ℝ) (T : ℕ) (hist : List Tr) :
    ∑ τ, trajProb (Mm b) (ucbviLearner (Mm b) (Rm b) δ T hist) τ *
      (fun (_ : Fin 3) (_ : Bool) (_ : Fin 3) => (1 : ℝ)) τ.1 (actionAt τ 0) (nextStateAt τ 0) = 1 := by
  rw [traj_sum 10 (Mm b) (ucbviLearner (Mm b) (Rm b) δ T hist)
    (fun h s => detPolicy_sum (ucbGreedy (Mm b) (Rm b) δ T hist) h s)
    (fun (_ : Fin 3) (_ : Bool) (_ : Fin 3) => (1 : ℝ))]
  simp only [Fin.sum_univ_three, Mm_d1, Mm_P, dm, ucbviLearner, detPolicy, Pm]
  generalize ucbGreedy (Mm b) (Rm b) δ T hist 0 0 = g
  cases b <;> cases g <;> simp <;> norm_num

lemma hp_nonneg (b : Bool) (δ : ℝ) (T : ℕ) {n : ℕ} (h : Fin n → Tr) :
    0 ≤ historyProb (Mm b) (ucbviLearner (Mm b) (Rm b) δ T) h := by
  unfold historyProb trajProb
  apply Finset.prod_nonneg; intro t _
  apply mul_nonneg ((Mm b).d1_nonneg _)
  apply Finset.prod_nonneg; intro i _
  apply mul_nonneg _ ((Mm b).P_nonneg _ _ _ _)
  simp only [ucbviLearner, detPolicy]; split_ifs <;> norm_num

/-- the key per-history bound. -/
lemma per_hist (b : Bool) (hl : (Finset.univ : Finset Bool).toList = [b, !b]) (δ : ℝ) (T : ℕ)
    (N : ℕ) (hN1 : 1 ≤ N) (hN : 5 * Lg δ T ≤ N) (B : ℝ) (hB : B < ((T : ℝ) - N) / 10)
    (h : Fin T → Tr) :
    (if regret (Mm b) (Rm b) δ T h ≤ B then historyProb (Mm b) (ucbviLearner (Mm b) (Rm b) δ T) h
      else 0) ≤
    historyProb (Mm b) (ucbviLearner (Mm b) (Rm b) δ T) h -
      (9/10 : ℝ) ^ N * (historyProb (Mm b) (ucbviLearner (Mm b) (Rm b) δ T) h *
        ∏ t, wt b (h t).1 (actionAt (h t) 0) (nextStateAt (h t) 0)) := by
  have h0 := hp_nonneg b δ T h
  set p := historyProb (Mm b) (ucbviLearner (Mm b) (Rm b) δ T) h with hpdef
  by_cases hz : p = 0
  · rw [hz]; simp
  by_cases hW : ∏ t, wt b (h t).1 (actionAt (h t) 0) (nextStateAt (h t) 0) = 0
  · rw [hW]; split_ifs <;> linarith
  have hF : ∀ t, nextStateAt (h t) 0 = (2 : Fin 3) := by
    intro t
    have := Finset.prod_ne_zero_iff.mp hW t (Finset.mem_univ _)
    by_contra hc; apply this; simp [wt, hc]
  have hc := cnt_le b hl δ T h hz hF N hN1 hN T le_rfl
  obtain ⟨hsum, hprod⟩ := cnt_sum b δ T h hz T le_rfl
  have hreg : regret (Mm b) (Rm b) δ T h ≥ ((T : ℝ) - N) / 10 := by
    rw [regret_eq b δ T h hz, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have e : ∑ t : Fin T, (if actionAt (h t) 0 = !b then (1 : ℝ) else 0) =
        countSA ((List.ofFn h).take T) 0 0 (!b) := by
      rw [← hsum, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [dif_pos t.2]
    rw [e]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (countSA ((List.ofFn h).take T) 0 0 (!b) : ℝ) ≤ N := by exact_mod_cast hc
    linarith
  have hWe : ∏ t, wt b (h t).1 (actionAt (h t) 0) (nextStateAt (h t) 0) =
      (10/9 : ℝ) ^ countSA ((List.ofFn h).take T) 0 0 (!b) := by
    rw [← hprod, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl (fun t _ => ?_)
    rw [dif_pos t.2]
    simp [wt, hF t]
  rw [if_neg (by linarith), hWe]
  have hpow : (9/10 : ℝ) ^ N * (10/9 : ℝ) ^ countSA ((List.ofFn h).take T) 0 0 (!b) ≤ 1 := by
    calc (9/10 : ℝ) ^ N * (10/9 : ℝ) ^ countSA ((List.ofFn h).take T) 0 0 (!b)
        ≤ (9/10 : ℝ) ^ N * (10/9 : ℝ) ^ N := by
          gcongr
          · norm_num
      _ = 1 := by rw [← mul_pow]; norm_num
  nlinarith

lemma prob_bound (b : Bool) (hl : (Finset.univ : Finset Bool).toList = [b, !b]) (δ : ℝ) (T : ℕ)
    (N : ℕ) (hN1 : 1 ≤ N) (hN : 5 * Lg δ T ≤ N) (B : ℝ) (hB : B < ((T : ℝ) - N) / 10) :
    probEvent (Mm b) (ucbviLearner (Mm b) (Rm b) δ T) T
      (fun histT => regret (Mm b) (Rm b) δ T histT ≤ B) ≤ 1 - (9/10 : ℝ) ^ N := by
  unfold probEvent
  have h1 := hist_sum (Mm b) (ucbviLearner (Mm b) (Rm b) δ T)
    (fun τ => (fun (_ : Fin 3) (_ : Bool) (_ : Fin 3) => (1 : ℝ)) τ.1 (actionAt τ 0) (nextStateAt τ 0))
    (hw_one b δ T) T
  have h2 := hist_sum (Mm b) (ucbviLearner (Mm b) (Rm b) δ T)
    (fun τ => wt b τ.1 (actionAt τ 0) (nextStateAt τ 0)) (hw_wt b δ T) T
  simp only [Finset.prod_const_one, mul_one] at h1
  calc _ ≤ ∑ h : Fin T → Tr, (historyProb (Mm b) (ucbviLearner (Mm b) (Rm b) δ T) h -
        (9/10 : ℝ) ^ N * (historyProb (Mm b) (ucbviLearner (Mm b) (Rm b) δ T) h *
          ∏ t, wt b (h t).1 (actionAt (h t) 0) (nextStateAt (h t) 0))) :=
        Finset.sum_le_sum (fun h _ => per_hist b hl δ T N hN1 hN B hB h)
    _ = 1 - (9/10 : ℝ) ^ N := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2, mul_one]

end Supp

lemma toList_bool : ∃ b : Bool, (Finset.univ : Finset Bool).toList = [b, !b] := by
  have hp : (Finset.univ : Finset Bool).toList.Perm [false, true] := by
    rw [List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (by decide)]
    intro a; cases a <;> simp
  have hl := hp.length_eq
  match h : (Finset.univ : Finset Bool).toList, hl with
  | [x, y], _ =>
    rw [h] at hp
    have hn : [x, y].Nodup := hp.nodup_iff.mpr (by decide)
    refine ⟨x, ?_⟩
    cases x <;> cases y <;> simp_all

lemma reals (C : ℝ) (hC : 0 < C) : ∃ T : ℕ, ∃ δ : ℝ, 0 < δ ∧
    δ < (9/10 : ℝ) ^ (⌈5 * Lg δ T⌉₊ + 1) ∧
    C * 11 * 3 * Real.sqrt (2 * T) * Real.sqrt (Real.log (3 * 2 * 11 * T / δ)) <
      ((T : ℝ) - ((⌈5 * Lg δ T⌉₊ + 1 : ℕ) : ℝ)) / 10 := by
  obtain ⟨m, hm12, hmC⟩ : ∃ m : ℕ, (12 : ℝ) ≤ m ∧ 3960 * C ≤ m - 12 := by
    refine ⟨⌈3960 * C⌉₊ + 12, ?_, ?_⟩
    · push_cast; have := Nat.cast_nonneg (α := ℝ) ⌈3960 * C⌉₊; linarith
    · push_cast; have := Nat.le_ceil (3960 * C); linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hmT : (0 : ℝ) < ((m ^ 16 : ℕ) : ℝ) := by
    push_cast; exact pow_pos hm0 16
  refine ⟨m ^ 16, 1 / (132 * ((m ^ 16 : ℕ) : ℝ)) ^ 2, by positivity, ?_⟩
  set T : ℕ := m ^ 16 with hT
  have hTr : (T : ℝ) = (m : ℝ) ^ 16 := by rw [hT]; push_cast; ring
  have hT1 : (1 : ℝ) ≤ T := by
    rw [hTr]; exact one_le_pow₀ (by linarith)
  set x : ℝ := 132 * (T : ℝ) with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  set ℓ : ℝ := Real.log x with hℓ
  have hLg : Lg (1 / x ^ 2) T = 3 * ℓ := by
    unfold Lg
    rw [show 132 * (T : ℝ) / (1 / x ^ 2) = x ^ 3 by rw [← hx]; field_simp, Real.log_pow]
    push_cast; ring
  rw [hLg]
  -- bounds on ℓ
  have hℓlo : 2 / 3 < ℓ := by
    have h1 : Real.log 132 ≤ ℓ := Real.log_le_log (by norm_num) (by rw [hx]; nlinarith)
    have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 132 by norm_num)
    norm_num at h2; linarith
  have hℓhi : ℓ ≤ 16 * m + 131 := by
    have e : ℓ = Real.log 132 + 16 * Real.log m := by
      rw [hℓ, hx, hTr, Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 132 by norm_num)
    have h2 := Real.log_le_sub_one_of_pos hm0
    rw [e]; linarith
  have hN : (((⌈5 * (3 * ℓ)⌉₊ + 1 : ℕ)) : ℝ) < 15 * ℓ + 2 := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 5 * (3 * ℓ) by linarith)
    push_cast; linarith
  have hN0 : (0 : ℝ) ≤ ((⌈5 * (3 * ℓ)⌉₊ + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  constructor
  · -- δ < (9/10)^N
    rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow,
      Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_pow]
    have h910 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 9/10 by norm_num)
    norm_num at h910
    have : ((⌈5 * (3 * ℓ)⌉₊ + 1 : ℕ) : ℝ) * (-1/9) ≤
        ((⌈5 * (3 * ℓ)⌉₊ + 1 : ℕ) : ℝ) * Real.log (9/10) :=
      mul_le_mul_of_nonneg_left (by linarith) hN0
    push_cast at this hN hN0 ⊢
    linarith [hℓ]
  · -- the regret threshold
    have hs1 : Real.sqrt (2 * (T : ℝ)) ≤ 2 * (m : ℝ) ^ 8 := by
      rw [show 2 * (m : ℝ) ^ 8 = Real.sqrt ((2 * (m : ℝ) ^ 8) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt
      rw [hTr]; nlinarith [pow_pos hm0 16]
    have e66 : 3 * 2 * 11 * (T : ℝ) / (1 / x ^ 2) = x ^ 3 / 2 := by
      rw [hx]; field_simp; ring
    have e3 : 3 * ℓ = Real.log (x ^ 3) := by rw [Real.log_pow, hℓ]; push_cast; ring
    have hlog : Real.log (3 * 2 * 11 * (T : ℝ) / (1 / x ^ 2)) ≤ 3 * ℓ := by
      rw [e66, e3]
      exact Real.log_le_log (by positivity) (by linarith [pow_pos hx0 3])
    have hs2 : Real.sqrt (Real.log (3 * 2 * 11 * (T : ℝ) / (1 / x ^ 2))) ≤ 6 * m := by
      rw [show 6 * (m : ℝ) = Real.sqrt ((6 * (m : ℝ)) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt
      nlinarith [hlog, hℓhi, hm12]
    have hB : C * 11 * 3 * Real.sqrt (2 * T) * Real.sqrt (Real.log (3 * 2 * 11 * T / (1 / x ^ 2)))
        ≤ C * 11 * 3 * (2 * (m : ℝ) ^ 8) * (6 * m) := by
      gcongr
    have hm8 : (12 : ℝ) ^ 8 ≤ (m : ℝ) ^ 8 := pow_le_pow_left₀ (by norm_num) hm12 8
    have hm9 : (m : ℝ) ^ 9 = m * (m : ℝ) ^ 8 := by ring
    have hm10 : (m : ℝ) ^ 10 ≤ (m : ℝ) ^ 16 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    have k1 : 3960 * C * (m : ℝ) ^ 9 ≤ (m - 12) * (m : ℝ) ^ 9 :=
      mul_le_mul_of_nonneg_right hmC (by positivity)
    have k2' : (m : ℝ) * 12 ^ 8 ≤ m * (m : ℝ) ^ 8 := mul_le_mul_of_nonneg_left hm8 hm0.le
    have k2 : 240 * (m : ℝ) + 1967 ≤ 12 * (m : ℝ) ^ 9 := by rw [hm9]; nlinarith
    have k3 : (m - 12) * (m : ℝ) ^ 9 = (m : ℝ) ^ 10 - 12 * (m : ℝ) ^ 9 := by ring
    push_cast at hN ⊢
    linarith

end Cex3b

open FoundationsRL.RLBasics in
theorem solution : ¬ (∃ C : ℝ, 0 < C ∧
      ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) (r : ℕ → S → A → ℝ),
        (∀ h, h < H → ∀ s a, r h s a ∈ Set.Icc (0 : ℝ) 1) →
        (∀ h, h < H → ∀ s a, M.R h s a = r h s a) →
        (∀ s : S, Vstar M 0 s ∈ Set.Icc (0 : ℝ) 1) →
        ∀ (T : ℕ) (δ : ℝ), 0 < δ →
        probEvent M (ucbviLearner M r δ T) T
            (fun histT => regret M r δ T histT ≤
              C * (H : ℝ) * (Fintype.card S : ℝ) * Real.sqrt ((Fintype.card A : ℝ) * T) *
                Real.sqrt (Real.log ((Fintype.card S : ℝ) * (Fintype.card A : ℝ) * H * T / δ)))
          ≥ 1 - δ) := by
  rintro ⟨C, hC, hmain⟩
  obtain ⟨b, hl⟩ := Cex3b.toList_bool
  obtain ⟨T, δ, hδ, h1, h2⟩ := Cex3b.reals C hC
  have key := hmain (Cex3b.Mm b) (Cex3b.Rm b)
    (by intro h _ s a; simp only [Set.mem_Icc]; unfold Cex3b.Rm; split_ifs <;> norm_num)
    (fun _ _ _ _ => rfl)
    (by intro s; rw [Cex3b.Vstar0]; simp only [Set.mem_Icc]; split_ifs <;> norm_num)
    T δ hδ
  revert key
  apply not_le.mpr
  refine lt_of_le_of_lt (Cex3b.prob_bound b hl δ T (⌈5 * Cex3b.Lg δ T⌉₊ + 1) (by omega) ?_ _ ?_) ?_
  · push_cast; have := Nat.le_ceil (5 * Cex3b.Lg δ T); linarith
  · simp only [Fintype.card_fin, Fintype.card_bool]
    push_cast at h2 ⊢
    linarith
  · linarith
