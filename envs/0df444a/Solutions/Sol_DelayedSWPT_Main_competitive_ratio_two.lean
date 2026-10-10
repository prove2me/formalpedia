-- Prove2me | solution 1 for DelayedSWPT.Main.competitive_ratio_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:42:50.591317+00:00
-- url     : https://prove2.me/submissions/a53722ba-e3a6-4038-8411-a0eaeb0f46fb

import Mathlib
import Definitions.Def_DelayedSWPT_Model_dswpt

set_option autoImplicit false

namespace P09bd5831

open DelayedSWPT.Model

theorem foldl_gen {α : Type} (A : Finset α) (g : Option α → α → Option α)
    (hg1 : ∀ acc k, k ∉ A → g acc k = acc)
    (hg2 : ∀ acc k, k ∈ A → ∃ b, g acc k = some b ∧ (b = k ∨ acc = some b)) :
    ∀ (l : List α) (acc : Option α),
      ((∀ b, acc = some b → b ∈ A) → ∀ b, l.foldl g acc = some b → b ∈ A) ∧
      ((acc ≠ none ∨ ∃ x ∈ l, x ∈ A) → l.foldl g acc ≠ none) := by
  intro l
  induction l with
  | nil =>
    intro acc
    refine ⟨fun h b hb => h b hb, fun h => ?_⟩
    rcases h with h | ⟨x, hx, _⟩
    · exact h
    · simp at hx
  | cons x l ih =>
    intro acc
    simp only [List.foldl_cons]
    refine ⟨fun h b hb => (ih (g acc x)).1 ?_ b hb, fun h => (ih (g acc x)).2 ?_⟩
    · intro c hc
      by_cases hx : x ∈ A
      · obtain ⟨b', hb', hor⟩ := hg2 acc x hx
        rw [hb'] at hc
        obtain rfl : b' = c := Option.some_inj.1 hc
        rcases hor with rfl | hacc
        · exact hx
        · exact h _ hacc
      · rw [hg1 acc x hx] at hc
        exact h c hc
    · by_cases hx : x ∈ A
      · obtain ⟨b', hb', _⟩ := hg2 acc x hx
        left; rw [hb']; simp
      · rw [hg1 acc x hx]
        rcases h with h | ⟨y, hy, hyA⟩
        · left; exact h
        · rcases List.mem_cons.1 hy with rfl | hy'
          · exact absurd hyA hx
          · right; exact ⟨y, hy', hyA⟩

theorem select_spec {n : ℕ} (prec : Fin n → Fin n → Prop) [DecidableRel prec]
    (A : Finset (Fin n)) :
    (∀ b, select prec A = some b → b ∈ A) ∧ (A.Nonempty → select prec A ≠ none) := by
  unfold select
  refine ⟨fun b hb => (foldl_gen A _ ?_ ?_ _ _).1 (fun c hc => by simp at hc) b hb,
    fun hA => (foldl_gen A _ ?_ ?_ _ _).2 ?_⟩
  · intro acc k hk
    simp only [hk, if_false]
  · intro acc k hk
    simp only [hk, if_true]
    cases acc with
    | none => exact ⟨k, rfl, Or.inl rfl⟩
    | some a =>
      dsimp only
      split_ifs
      · exact ⟨k, rfl, Or.inl rfl⟩
      · exact ⟨a, rfl, Or.inr rfl⟩
  · intro acc k hk
    simp only [hk, if_false]
  · intro acc k hk
    simp only [hk, if_true]
    cases acc with
    | none => exact ⟨k, rfl, Or.inl rfl⟩
    | some a =>
      dsimp only
      split_ifs
      · exact ⟨k, rfl, Or.inl rfl⟩
      · exact ⟨a, rfl, Or.inr rfl⟩
  · obtain ⟨x, hx⟩ := hA
    exact Or.inr ⟨x, List.mem_finRange x, hx⟩

section Sim

variable {n : ℕ} (r p : Fin n → ℕ) (prec : Fin n → Fin n → Prop) [DecidableRel prec]

def U (s : State n) : Finset (Fin n) := Finset.univ.filter (fun k => s.start k = none)

theorem U_update (s : State n) (k : Fin n) (t f : ℕ) :
    U (⟨Function.update s.start k (some t), f⟩ : State n) = (U s).erase k := by
  ext x
  by_cases hx : x = k
  · subst hx; simp [U]
  · simp [U, hx]

theorem stateAt_succ (t : ℕ) :
    stateAt r p prec (t + 1) = step r p prec t (stateAt r p prec t) := rfl

theorem step_eq (t : ℕ) (s : State n) :
    step r p prec t s = s ∨ ∃ k, s.free ≤ t ∧ s.start k = none ∧ r k ≤ t ∧ p k ≤ t ∧
      step r p prec t s = ⟨Function.update s.start k (some t), t + p k⟩ := by
  unfold step
  rcases hc : choice r prec s t with _ | k
  · left; rfl
  · dsimp only
    split_ifs with hpk
    · right
      unfold choice at hc
      split_ifs at hc with hf
      have hk := (select_spec prec _).1 k hc
      simp [available] at hk
      exact ⟨k, hf, hk.2, hk.1, hpk, rfl⟩
    · left; rfl

theorem inv (t : ℕ) :
    (∀ j s0, (stateAt r p prec t).start j = some s0 → p j ≤ s0) ∧
    (stateAt r p prec t).free + ∑ k ∈ U (stateAt r p prec t), p k ≤ t + ∑ k, p k := by
  induction t with
  | zero => simp [stateAt, initState, U]
  | succ t ih =>
    rw [stateAt_succ]
    rcases step_eq r p prec t (stateAt r p prec t) with h | ⟨k, hf, hk, hr, hpk, h⟩
    · rw [h]; exact ⟨ih.1, by omega⟩
    · rw [h]
      refine ⟨?_, ?_⟩
      · intro j s0 hj
        by_cases hjk : j = k
        · subst hjk
          simp at hj
          omega
        · dsimp only at hj
          rw [Function.update_of_ne hjk] at hj
          exact ih.1 j s0 hj
      · have hmem : k ∈ U (stateAt r p prec t) := by simp [U, hk]
        rw [U_update]
        have h2 := Finset.add_sum_erase _ p hmem
        have h3 := ih.2
        have h4 : ∑ k ∈ U (stateAt r p prec t), p k ≤ ∑ k, p k :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        dsimp only
        omega

theorem mono (t : ℕ) (j : Fin n) (h : (stateAt r p prec (t + 1)).start j = none) :
    (stateAt r p prec t).start j = none := by
  rw [stateAt_succ] at h
  rcases step_eq r p prec t (stateAt r p prec t) with h' | ⟨k, -, hk, -, -, h'⟩
  · rw [h'] at h; exact h
  · rw [h'] at h
    by_cases hjk : j = k
    · subst hjk; simp at h
    · simpa [Function.update_of_ne hjk] using h

theorem mono_le (j : Fin n) (t : ℕ) : ∀ d,
    (stateAt r p prec (t + d)).start j = none → (stateAt r p prec t).start j = none := by
  intro d
  induction d with
  | zero => intro h; simpa using h
  | succ d ih =>
    intro h
    exact ih (mono r p prec (t + d) j (by rw [← Nat.add_assoc] at h; exact h))

def phi (s : State n) (t : ℕ) : ℕ := max s.free t + ∑ k ∈ U s, p k

theorem phi_step (hp : ∀ j, 1 ≤ p j) (t : ℕ) (j : Fin n)
    (hj : (stateAt r p prec t).start j = none) (hrj : r j ≤ t) (hpall : ∀ k, p k ≤ t) :
    phi p (stateAt r p prec (t + 1)) (t + 1) ≤ phi p (stateAt r p prec t) t := by
  rw [stateAt_succ]
  generalize stateAt r p prec t = s at hj ⊢
  by_cases hf : s.free ≤ t
  · have hne : (available r s t).Nonempty := ⟨j, by simp [available, hrj, hj]⟩
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 ((select_spec prec _).2 hne)
    have hkA := (select_spec prec _).1 k hk
    simp [available] at hkA
    have hstep : step r p prec t s = ⟨Function.update s.start k (some t), t + p k⟩ := by
      unfold step choice
      rw [if_pos hf, hk]
      simp [hpall k]
    rw [hstep]
    have hmem : k ∈ U s := by simp [U, hkA.2]
    have h2 := Finset.add_sum_erase _ p hmem
    have h4 := hp k
    unfold phi
    rw [U_update]
    dsimp only
    rw [max_eq_left (by omega), max_eq_right hf]
    omega
  · have hstep : step r p prec t s = s := by
      unfold step choice
      rw [if_neg hf]
    rw [hstep]
    unfold phi
    rw [max_eq_left (by omega), max_eq_left (by omega)]

theorem all_started (hp : ∀ j, 1 ≤ p j) (j : Fin n) :
    (stateAt r p prec (horizon r p)).start j ≠ none := by
  intro hH
  have hple : ∀ k, p k ≤ ∑ k, p k := fun k =>
    Finset.single_le_sum (fun i _ => Nat.zero_le (p i)) (Finset.mem_univ k)
  have hrle : ∀ k, r k ≤ ∑ k, r k := fun k =>
    Finset.single_le_sum (fun i _ => Nat.zero_le (r i)) (Finset.mem_univ k)
  have hHM : horizon r p = (∑ k, r k + ∑ k, p k) + (∑ k, p k + 1) := by
    simp only [horizon, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hHM] at hH
  have key : ∀ d, d ≤ ∑ k, p k + 1 →
      phi p (stateAt r p prec ((∑ k, r k + ∑ k, p k) + d)) ((∑ k, r k + ∑ k, p k) + d) ≤
      phi p (stateAt r p prec (∑ k, r k + ∑ k, p k)) (∑ k, r k + ∑ k, p k) := by
    intro d
    induction d with
    | zero => intro _; exact le_refl _
    | succ d ih =>
      intro hd
      have hjn : (stateAt r p prec ((∑ k, r k + ∑ k, p k) + d)).start j = none := by
        have := mono_le r p prec j ((∑ k, r k + ∑ k, p k) + d) (∑ k, p k + 1 - d)
        apply this
        have he : (∑ k, r k + ∑ k, p k) + d + (∑ k, p k + 1 - d) =
            (∑ k, r k + ∑ k, p k) + (∑ k, p k + 1) := by omega
        rw [he]; exact hH
      refine le_trans ?_ (ih (by omega))
      rw [← Nat.add_assoc]
      exact phi_step r p prec hp _ j hjn (by have := hrle j; omega)
        (fun k => by have := hple k; omega)
  have h1 := key (∑ k, p k + 1) le_rfl
  have hjU : j ∈ U (stateAt r p prec ((∑ k, r k + ∑ k, p k) + (∑ k, p k + 1))) := by
    simp [U, hH]
  have h2 := Finset.single_le_sum (f := p) (fun i _ => Nat.zero_le (p i)) hjU
  have h3 := (inv r p prec (∑ k, r k + ∑ k, p k)).2
  have h4 : ∑ k ∈ U (stateAt r p prec (∑ k, r k + ∑ k, p k)), p k ≤ ∑ k, p k :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h5 := hp j
  unfold phi at h1
  have h6 := le_max_right (stateAt r p prec ((∑ k, r k + ∑ k, p k) + (∑ k, p k + 1))).free
    ((∑ k, r k + ∑ k, p k) + (∑ k, p k + 1))
  have h7 : max (stateAt r p prec (∑ k, r k + ∑ k, p k)).free (∑ k, r k + ∑ k, p k)
      ≤ (∑ k, r k + ∑ k, p k) + ∑ k, p k - ∑ k ∈ U (stateAt r p prec (∑ k, r k + ∑ k, p k)), p k := by
    apply max_le <;> omega
  omega

end Sim

end P09bd5831


namespace P36bbe2cf

open DelayedSWPT.Model

theorem start_ge_p {n : ℕ} (I : Instance n) (j : Fin n) : I.p j ≤ dswpt I j := by
  unfold dswpt dswptState
  have hs := @P09bd5831.all_started n I.r I.p (Prec I) (Classical.decRel _) I.p_pos j
  obtain ⟨s0, hs0⟩ := Option.ne_none_iff_exists'.1 hs
  rw [hs0]
  exact (@P09bd5831.inv n I.r I.p (Prec I) (Classical.decRel _) _).1 j s0 hs0

/-- The one-job instance `r = 0, p = 1, w = 1`. -/
def I1 : Instance 1 where
  r := fun _ => 0
  p := fun _ => 1
  w := fun _ => 1
  p_pos := fun _ => le_refl 1
  w_pos := fun _ => one_pos

/-- Lower bound: every valid ratio is at least 2. -/
theorem lower_bound (ρ : ℝ) (hρ : ∀ (n : ℕ) (I : Instance n) (S : Fin n → ℕ), IsFeasible I.r I.p S →
      cost I.w I.p (dswpt I) ≤ ρ * cost I.w I.p S) : 2 ≤ ρ := by
  have hfeas : IsFeasible I1.r I1.p (fun _ => 0) := by
    refine ⟨fun j => le_refl _, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
  have h := hρ 1 I1 (fun _ => 0) hfeas
  have hge : 1 ≤ dswpt I1 0 := start_ge_p I1 0
  have hcS : cost I1.w I1.p (fun _ => 0) = 1 := by
    simp [cost, I1]
  have hcD : cost I1.w I1.p (dswpt I1) = ((dswpt I1 0 : ℕ) : ℝ) + 1 := by
    simp [cost, I1]
  rw [hcS, hcD] at h
  have : (1 : ℝ) ≤ ((dswpt I1 0 : ℕ) : ℝ) := by exact_mod_cast hge
  linarith

end P36bbe2cf

namespace PSim

open DelayedSWPT.Model

section Sim

variable {n : ℕ} (r p : Fin n → ℕ) (prec : Fin n → Fin n → Prop) [DecidableRel prec]

theorem step_cases (t : ℕ) (s : State n) :
    step r p prec t s = s ∨ ∃ k, choice r prec s t = some k ∧ p k ≤ t ∧
      step r p prec t s = ⟨Function.update s.start k (some t), t + p k⟩ := by
  unfold step
  rcases hc : choice r prec s t with _ | k
  · left; rfl
  · dsimp only
    split_ifs with hpk
    · right; exact ⟨k, rfl, hpk, rfl⟩
    · left; rfl

theorem choice_some {s : State n} {t : ℕ} {k : Fin n} (h : choice r prec s t = some k) :
    s.free ≤ t ∧ r k ≤ t ∧ s.start k = none := by
  unfold choice at h
  split_ifs at h with hf
  have hk := (P09bd5831.select_spec prec _).1 k h
  simp only [available, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  exact ⟨hf, hk.1, hk.2⟩

theorem choice_free {s : State n} {t : ℕ} (hf : ¬ s.free ≤ t) : choice r prec s t = none := by
  unfold choice
  rw [if_neg hf]

theorem step_start {s : State n} {t : ℕ} {k : Fin n} (h : choice r prec s t = some k)
    (hpk : p k ≤ t) : step r p prec t s = ⟨Function.update s.start k (some t), t + p k⟩ := by
  unfold step
  rw [h]
  dsimp only
  rw [if_pos hpk]

theorem keep (t : ℕ) (j : Fin n) (s0 : ℕ) (h : (stateAt r p prec t).start j = some s0) :
    (stateAt r p prec (t + 1)).start j = some s0 := by
  rw [P09bd5831.stateAt_succ]
  rcases step_cases r p prec t (stateAt r p prec t) with h' | ⟨k, hc, -, h'⟩
  · rw [h']; exact h
  · rw [h']
    have hk := (choice_some r prec hc).2.2
    have hjk : j ≠ k := by
      rintro rfl
      rw [h] at hk
      exact absurd hk (by simp)
    dsimp only
    rw [Function.update_of_ne hjk]
    exact h

theorem keep_le (t : ℕ) (j : Fin n) (s0 : ℕ) (h : (stateAt r p prec t).start j = some s0) :
    ∀ d, (stateAt r p prec (t + d)).start j = some s0 := by
  intro d
  induction d with
  | zero => simpa using h
  | succ d ih =>
    rw [← Nat.add_assoc]
    exact keep r p prec (t + d) j s0 ih

theorem born (t : ℕ) (j : Fin n) (s0 : ℕ) (h0 : (stateAt r p prec t).start j = none)
    (h1 : (stateAt r p prec (t + 1)).start j = some s0) :
    s0 = t ∧ choice r prec (stateAt r p prec t) t = some j ∧ p j ≤ t ∧
      (stateAt r p prec (t + 1)).free = t + p j := by
  rw [P09bd5831.stateAt_succ] at h1 ⊢
  rcases step_cases r p prec t (stateAt r p prec t) with h' | ⟨k, hc, hpk, h'⟩
  · rw [h', h0] at h1
    exact absurd h1 (by simp)
  · rw [h'] at h1 ⊢
    by_cases hjk : j = k
    · subst hjk
      dsimp only at h1 ⊢
      rw [Function.update_self] at h1
      have : s0 = t := by
        have := Option.some_inj.1 h1
        omega
      exact ⟨this, hc, hpk, rfl⟩
    · dsimp only at h1
      rw [Function.update_of_ne hjk, h0] at h1
      exact absurd h1 (by simp)

theorem started (t : ℕ) (j : Fin n) (s0 : ℕ) (h : (stateAt r p prec t).start j = some s0) :
    s0 < t ∧ (stateAt r p prec s0).start j = none ∧
      choice r prec (stateAt r p prec s0) s0 = some j ∧ p j ≤ s0 ∧
      (stateAt r p prec (s0 + 1)).free = s0 + p j ∧
      (stateAt r p prec (s0 + 1)).start j = some s0 := by
  induction t with
  | zero => simp [stateAt, initState] at h
  | succ t ih =>
    rcases hnone : (stateAt r p prec t).start j with _ | s1
    · obtain ⟨hs, hc, hpk, hf⟩ := born r p prec t j s0 hnone h
      subst hs
      exact ⟨Nat.lt_succ_self _, hnone, hc, hpk, hf, h⟩
    · have hk := keep r p prec t j s1 hnone
      rw [hk] at h
      have hs : s1 = s0 := Option.some_inj.1 h
      subst hs
      obtain ⟨a, b, c, d, e, f⟩ := ih hnone
      exact ⟨by omega, b, c, d, e, f⟩

theorem free_mono (t : ℕ) : (stateAt r p prec t).free ≤ (stateAt r p prec (t + 1)).free := by
  rw [P09bd5831.stateAt_succ]
  rcases step_cases r p prec t (stateAt r p prec t) with h' | ⟨k, hc, -, h'⟩
  · rw [h']
  · rw [h']
    have := (choice_some r prec hc).1
    dsimp only
    omega

theorem free_mono_le (t : ℕ) : ∀ d, (stateAt r p prec t).free ≤ (stateAt r p prec (t + d)).free := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc]
    exact le_trans ih (free_mono r p prec (t + d))

theorem free_inv (t : ℕ) : (stateAt r p prec t).free ≤ t ∨
    ∃ j s0, (stateAt r p prec t).start j = some s0 ∧ (stateAt r p prec t).free = s0 + p j := by
  induction t with
  | zero => left; simp [stateAt, initState]
  | succ t ih =>
    have hst := P09bd5831.stateAt_succ r p prec t
    rcases step_cases r p prec t (stateAt r p prec t) with h' | ⟨k, hc, -, h'⟩
    · rcases ih with h | ⟨j, s0, hj, hf⟩
      · left; rw [hst, h']; omega
      · right
        refine ⟨j, s0, keep r p prec t j s0 hj, ?_⟩
        rw [hst, h']; exact hf
    · right
      refine ⟨k, t, ?_, ?_⟩
      · rw [hst, h']
        dsimp only
        rw [Function.update_self]
      · rw [hst, h']

end Sim

/-- Selection minimality, for any total preorder `R` compatible with `prec`. -/
theorem foldl_min {α : Type} (A : Finset α) (R : α → α → Prop) (prec : α → α → Prop)
    (hrefl : ∀ a, R a a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hprec : ∀ a b, prec a b → R a b) (hnot : ∀ a b, ¬ prec a b → R b a)
    (g : Option α → α → Option α)
    (hg1 : ∀ acc k, k ∉ A → g acc k = acc)
    (hg2 : ∀ k, k ∈ A → g none k = some k)
    (hg3 : ∀ b k, k ∈ A → prec k b → g (some b) k = some k)
    (hg4 : ∀ b k, k ∈ A → ¬ prec k b → g (some b) k = some b) :
    ∀ (l : List α) (S : α → Prop) (acc : Option α),
      ((acc = none → ∀ k ∈ A, ¬ S k) ∧ ∀ b, acc = some b → b ∈ A ∧ ∀ k ∈ A, S k → R b k) →
      ((l.foldl g acc = none → ∀ k ∈ A, ¬ (S k ∨ k ∈ l)) ∧
        ∀ b, l.foldl g acc = some b → b ∈ A ∧ ∀ k ∈ A, (S k ∨ k ∈ l) → R b k) := by
  intro l
  induction l with
  | nil =>
    intro S acc h
    simpa using h
  | cons x l ih =>
    intro S acc h
    have step : ((g acc x = none → ∀ k ∈ A, ¬ (S k ∨ k = x)) ∧
        ∀ b, g acc x = some b → b ∈ A ∧ ∀ k ∈ A, (S k ∨ k = x) → R b k) := by
      by_cases hx : x ∈ A
      · cases acc with
        | none =>
          rw [hg2 x hx]
          refine ⟨fun h' => by simp at h', fun b hb => ?_⟩
          obtain rfl := Option.some_inj.1 hb
          refine ⟨hx, fun k hk hS => ?_⟩
          rcases hS with hS | rfl
          · exact absurd hS (h.1 rfl k hk)
          · exact hrefl _
        | some a =>
          obtain ⟨haA, haR⟩ := h.2 a rfl
          by_cases hp : prec x a
          · rw [hg3 a x hx hp]
            refine ⟨fun h' => by simp at h', fun b hb => ?_⟩
            obtain rfl := Option.some_inj.1 hb
            refine ⟨hx, fun k hk hS => ?_⟩
            rcases hS with hS | rfl
            · exact htrans _ _ _ (hprec _ _ hp) (haR k hk hS)
            · exact hrefl _
          · rw [hg4 a x hx hp]
            refine ⟨fun h' => by simp at h', fun b hb => ?_⟩
            obtain rfl := Option.some_inj.1 hb
            refine ⟨haA, fun k hk hS => ?_⟩
            rcases hS with hS | rfl
            · exact haR k hk hS
            · exact hnot _ _ hp
      · rw [hg1 acc x hx]
        refine ⟨fun h' k hk hS => ?_, fun b hb => ?_⟩
        · rcases hS with hS | rfl
          · exact h.1 h' k hk hS
          · exact hx hk
        · obtain ⟨hbA, hbR⟩ := h.2 b hb
          refine ⟨hbA, fun k hk hS => ?_⟩
          rcases hS with hS | rfl
          · exact hbR k hk hS
          · exact absurd hk hx
    have := ih (fun k => S k ∨ k = x) (g acc x) step
    simp only [List.foldl_cons]
    refine ⟨fun h' k hk hS => this.1 h' k hk ?_, fun b hb => ⟨(this.2 b hb).1, fun k hk hS =>
      (this.2 b hb).2 k hk ?_⟩⟩
    · rcases hS with hS | hS
      · exact Or.inl (Or.inl hS)
      · rcases List.mem_cons.1 hS with h1 | h1
        · exact Or.inl (Or.inr h1)
        · exact Or.inr h1
    · rcases hS with hS | hS
      · exact Or.inl (Or.inl hS)
      · rcases List.mem_cons.1 hS with h1 | h1
        · exact Or.inl (Or.inr h1)
        · exact Or.inr h1

theorem select_min {n : ℕ} (prec : Fin n → Fin n → Prop) [DecidableRel prec]
    (R : Fin n → Fin n → Prop)
    (hrefl : ∀ a, R a a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hprec : ∀ a b, prec a b → R a b) (hnot : ∀ a b, ¬ prec a b → R b a)
    (A : Finset (Fin n)) (b : Fin n) (hb : select prec A = some b) : ∀ k ∈ A, R b k := by
  unfold select at hb
  intro k hk
  refine ((foldl_min A R prec hrefl htrans hprec hnot _ ?_ ?_ ?_ ?_ (List.finRange n)
    (fun _ => False) none ⟨fun _ _ _ h => h, fun b hb => by simp at hb⟩).2 b hb).2 k hk
    (Or.inr (List.mem_finRange k))
  · intro acc k hk
    simp only [hk, if_false]
  · intro k hk
    simp only [hk, if_true]
  · intro b k hk hp
    simp [hk, hp]
  · intro b k hk hp
    simp [hk, hp]

end PSim

namespace P36bbe2cf

open DelayedSWPT.Model

/-- Weak SWPT comparison: `j` has ratio `p/w` at most that of `k`. -/
def R {n : ℕ} (I : Instance n) (j k : Fin n) : Prop := (I.p j : ℝ) * I.w k ≤ (I.p k : ℝ) * I.w j

theorem R_refl {n : ℕ} (I : Instance n) (a : Fin n) : R I a a := le_refl _

theorem R_trans {n : ℕ} (I : Instance n) (a b c : Fin n) (h1 : R I a b) (h2 : R I b c) :
    R I a c := by
  unfold R at *
  have hwb := I.w_pos b
  have hwa := I.w_pos a
  have hwc := I.w_pos c
  have hpb : (0 : ℝ) < I.p b := by have := I.p_pos b; exact_mod_cast this
  have e1 := mul_le_mul_of_nonneg_right h1 hwc.le
  have e2 := mul_le_mul_of_nonneg_right h2 hwa.le
  have : (I.p a : ℝ) * I.w c * I.w b ≤ (I.p c : ℝ) * I.w a * I.w b := by nlinarith
  exact le_of_mul_le_mul_right this hwb

theorem R_of_prec {n : ℕ} (I : Instance n) (a b : Fin n) (h : Prec I a b) : R I a b := by
  unfold R
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

theorem R_of_not_prec {n : ℕ} (I : Instance n) (a b : Fin n) (h : ¬ Prec I a b) : R I b a := by
  unfold R
  unfold Prec at h
  push_neg at h
  exact h.1

theorem R_div {n : ℕ} (I : Instance n) (j k : Fin n) (h : R I j k) :
    I.w k / (I.p k : ℝ) ≤ I.w j / (I.p j : ℝ) := by
  have hpj : (0 : ℝ) < I.p j := by have := I.p_pos j; exact_mod_cast this
  have hpk : (0 : ℝ) < I.p k := by have := I.p_pos k; exact_mod_cast this
  rw [div_le_div_iff₀ hpk hpj]
  unfold R at h
  linarith

/-! ### Simulation facts specialised to Delayed SWPT -/

theorem choice_min {n : ℕ} (I : Instance n) {t : ℕ} {j : Fin n} (hc : dswptChoice I t = some j)
    (k : Fin n) (hk : k ∈ @available n I.r (dswptState I t) t) : R I j k := by
  unfold dswptChoice choice at hc
  split_ifs at hc with hf
  exact @PSim.select_min n (Prec I) (Classical.decRel _) (R I) (R_refl I) (R_trans I) (R_of_prec I) (R_of_not_prec I) _ j hc k hk

theorem choice_spec {n : ℕ} (I : Instance n) {t : ℕ} {j : Fin n} (hc : dswptChoice I t = some j) :
    (dswptState I t).free ≤ t ∧ I.r j ≤ t ∧ (dswptState I t).start j = none :=
  @PSim.choice_some n I.r (Prec I) (Classical.decRel _) _ _ _ hc

theorem pi_spec {n : ℕ} (I : Instance n) (j : Fin n) :
    (dswptState I (dswpt I j)).start j = none ∧ dswptChoice I (dswpt I j) = some j ∧
      I.p j ≤ dswpt I j ∧ (dswptState I (dswpt I j + 1)).free = dswpt I j + I.p j ∧
      (dswptState I (dswpt I j + 1)).start j = some (dswpt I j) ∧
      dswpt I j < horizon I.r I.p := by
  have hs := @P09bd5831.all_started n I.r I.p (Prec I) (Classical.decRel _) I.p_pos j
  obtain ⟨s0, hs0⟩ := Option.ne_none_iff_exists'.1 hs
  have hpi : dswpt I j = s0 := by
    unfold dswpt dswptState
    rw [hs0]
    rfl
  rw [hpi]
  obtain ⟨a, b, c, d, e, f⟩ := @PSim.started n I.r I.p (Prec I) (Classical.decRel _) _ j s0 hs0
  exact ⟨b, c, d, e, f, a⟩

theorem start_eq {n : ℕ} (I : Instance n) {t : ℕ} {j : Fin n} {s0 : ℕ}
    (h : (dswptState I t).start j = some s0) : s0 = dswpt I j := by
  have h1 := @PSim.keep_le n I.r I.p (Prec I) (Classical.decRel _) t j s0 h (dswpt I j + 1)
  have h2 := @PSim.keep_le n I.r I.p (Prec I) (Classical.decRel _) (dswpt I j + 1) j (dswpt I j)
    (pi_spec I j).2.2.2.2.1 t
  rw [Nat.add_comm (dswpt I j + 1) t] at h2
  have := h1.symm.trans h2
  exact Option.some_inj.1 this

theorem none_of_le {n : ℕ} (I : Instance n) {t : ℕ} {j : Fin n} (h : t ≤ dswpt I j) :
    (dswptState I t).start j = none := by
  rcases hs : (dswptState I t).start j with _ | s0
  · rfl
  · have he := start_eq I hs
    have := (@PSim.started n I.r I.p (Prec I) (Classical.decRel _) t j s0 hs).1
    omega

theorem le_of_none {n : ℕ} (I : Instance n) {t : ℕ} {j : Fin n}
    (h : (dswptState I t).start j = none) : t ≤ dswpt I j := by
  by_contra hlt
  push_neg at hlt
  have h2 := @PSim.keep_le n I.r I.p (Prec I) (Classical.decRel _) (dswpt I j + 1) j (dswpt I j)
    (pi_spec I j).2.2.2.2.1 (t - (dswpt I j + 1))
  have he : dswpt I j + 1 + (t - (dswpt I j + 1)) = t := by omega
  rw [he] at h2
  change (dswptState I t).start j = some (dswpt I j) at h2
  rw [h] at h2
  exact absurd h2 (by simp)

theorem free_mono_le {n : ℕ} (I : Instance n) {t t' : ℕ} (h : t ≤ t') :
    (dswptState I t).free ≤ (dswptState I t').free := by
  have := @PSim.free_mono_le n I.r I.p (Prec I) (Classical.decRel _) t (t' - t)
  rw [Nat.add_sub_cancel' h] at this
  exact this

theorem start_at {n : ℕ} (I : Instance n) {t : ℕ} {j : Fin n} (hc : dswptChoice I t = some j)
    (hp : I.p j ≤ t) : dswpt I j = t := by
  have hstep := @PSim.step_start n I.r I.p (Prec I) (Classical.decRel _) _ _ _ hc hp
  have h1 : (dswptState I (t + 1)).start j = some t := by
    show (@step n I.r I.p (Prec I) (Classical.decRel _) t (dswptState I t)).start j = some t
    rw [hstep]
    dsimp only
    rw [Function.update_self]
  exact (start_eq I h1).symm

theorem busy {n : ℕ} (I : Instance n) {t : ℕ} {j : Fin n} (h1 : dswpt I j < t)
    (h2 : t < dswpt I j + I.p j) : t < (dswptState I t).free := by
  have := free_mono_le I (show dswpt I j + 1 ≤ t by omega)
  rw [(pi_spec I j).2.2.2.1] at this
  omega

theorem free_inv {n : ℕ} (I : Instance n) (t : ℕ) : (dswptState I t).free ≤ t ∨
    ∃ j, dswpt I j < t ∧ (dswptState I t).free = dswpt I j + I.p j := by
  rcases @PSim.free_inv n I.r I.p (Prec I) (Classical.decRel _) t with h | ⟨j, s0, hj, hf⟩
  · exact Or.inl h
  · right
    have he := start_eq I hj
    have hlt := (@PSim.started n I.r I.p (Prec I) (Classical.decRel _) t j s0 hj).1
    subst he
    exact ⟨j, hlt, hf⟩

theorem no_overlap {n : ℕ} (I : Instance n) (i j : Fin n) (hij : i ≠ j) :
    dswpt I i + I.p i ≤ dswpt I j ∨ dswpt I j + I.p j ≤ dswpt I i := by
  have key : ∀ a b : Fin n, dswpt I a < dswpt I b → dswpt I a + I.p a ≤ dswpt I b := by
    intro a b hab
    have h1 := free_mono_le I (show dswpt I a + 1 ≤ dswpt I b by omega)
    rw [(pi_spec I a).2.2.2.1] at h1
    have h2 := (choice_spec I (pi_spec I b).2.1).1
    omega
  rcases lt_trichotomy (dswpt I i) (dswpt I j) with h | h | h
  · exact Or.inl (key i j h)
  · exfalso
    have hi := (pi_spec I i).2.1
    have hj := (pi_spec I j).2.1
    rw [h, hj] at hi
    exact hij (Option.some_inj.1 hi).symm
  · exact Or.inr (key j i h)

end P36bbe2cf


namespace A36bbe2cf

/-- Layer cake: nonnegative weights and nonnegative upper-set sums give a nonnegative
weighted sum. -/
theorem layer_cake {ι : Type*} (X : ι → ℝ) : ∀ (m : ℕ) (s : Finset ι) (ω : ι → ℝ),
    s.card = m → (∀ j ∈ s, 0 ≤ ω j) →
    (∀ j0 ∈ s, 0 ≤ ∑ j ∈ s.filter (fun j => ω j0 ≤ ω j), X j) →
    0 ≤ ∑ j ∈ s, ω j * X j := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro s ω hm hω hX
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs]
  obtain ⟨j0, hj0, hmin⟩ := s.exists_min_image ω hs
  have hsplit : ∑ j ∈ s, ω j * X j = ω j0 * ∑ j ∈ s, X j +
      ∑ j ∈ s.filter (fun j => ω j0 < ω j), (ω j - ω j0) * X j := by
    rw [Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    split_ifs with h
    · ring
    · have : ω j = ω j0 := le_antisymm (not_lt.1 h) (hmin j hj)
      rw [this]; ring
  have h1 : 0 ≤ ∑ j ∈ s, X j := by
    have := hX j0 hj0
    have he : s.filter (fun j => ω j0 ≤ ω j) = s := Finset.filter_true_of_mem (fun j hj => hmin j hj)
    rwa [he] at this
  have hlt : (s.filter (fun j => ω j0 < ω j)).card < m := by
    rw [← hm]
    apply Finset.card_lt_card
    refine ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
    have := hsub hj0
    simp at this
  have h2 : 0 ≤ ∑ j ∈ s.filter (fun j => ω j0 < ω j), (ω j - ω j0) * X j := by
    refine ih _ hlt (s.filter (fun j => ω j0 < ω j)) (fun j => ω j - ω j0) rfl ?_ ?_
    · intro j hj
      have := (Finset.mem_filter.1 hj).2
      show 0 ≤ ω j - ω j0
      linarith
    · intro j1 hj1
      have hj1' := Finset.mem_filter.1 hj1
      have he : (s.filter (fun j => ω j0 < ω j)).filter (fun j => ω j1 - ω j0 ≤ ω j - ω j0) =
          s.filter (fun j => ω j1 ≤ ω j) := by
        ext j
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hj, _⟩, h⟩
          exact ⟨hj, by linarith⟩
        · rintro ⟨hj, h⟩
          exact ⟨⟨hj, by linarith [hj1'.2]⟩, by linarith⟩
      rw [he]
      exact hX j1 hj1'.1
  have hc : 0 ≤ ω j0 := hω j0 hj0
  rw [hsplit]
  have := mul_nonneg hc h1
  linarith

/-- Ordered pairs identity: `2 ∑_{key i < key j} p_i p_j + ∑ p_j² = (∑ p)²`. -/
theorem pair_id {ι : Type*} [DecidableEq ι] (p key : ι → ℕ) (s : Finset ι)
    (hk : Set.InjOn key s) :
    2 * ∑ j ∈ s, p j * ∑ i ∈ s.filter (fun i => key i < key j), p i +
      ∑ j ∈ s, p j * p j = (∑ j ∈ s, p j) * (∑ j ∈ s, p j) := by
  have hsq : (∑ j ∈ s, p j) * (∑ j ∈ s, p j) = ∑ j ∈ s, ∑ i ∈ s, p j * p i := by
    rw [Finset.sum_mul_sum]
  have hsplit : ∀ j ∈ s, ∑ i ∈ s, p j * p i =
      (∑ i ∈ s, if key i < key j then p j * p i else 0) + p j * p j +
        (∑ i ∈ s, if key j < key i then p j * p i else 0) := by
    intro j hj
    have hdiag : p j * p j = ∑ i ∈ s, if i = j then p j * p i else 0 := by
      rw [Finset.sum_ite_eq' s j (fun i => p j * p i)]
      simp [hj]
    rw [hdiag, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    by_cases h1 : key i < key j
    · have h2 : i ≠ j := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      have h3 : ¬ key j < key i := by omega
      simp [h1, h2, h3]
    · by_cases h2 : i = j
      · subst h2
        simp
      · have h3 : key j < key i := by
          rcases lt_trichotomy (key i) (key j) with h | h | h
          · exact absurd h h1
          · exact absurd (hk hi hj h) h2
          · exact h
        simp [h1, h2, h3]
  have hA : ∑ j ∈ s, p j * ∑ i ∈ s.filter (fun i => key i < key j), p i =
      ∑ j ∈ s, ∑ i ∈ s, if key i < key j then p j * p i else 0 := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum, Finset.sum_filter]
  have hB : (∑ j ∈ s, ∑ i ∈ s, if key j < key i then p j * p i else 0) =
      ∑ j ∈ s, ∑ i ∈ s, if key i < key j then p j * p i else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    split_ifs <;> ring
  rw [hsq, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib, hB, hA]
  ring

/-- Disjoint intervals of total length below a point. -/
theorem chain {ι : Type*} [DecidableEq ι] (K : Finset ι) (p S : ι → ℕ)
    (hS : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → S i + p i ≤ S j ∨ S j + p j ≤ S i)
    (m : ι) (hmin : ∀ i ∈ K, S m ≤ S i) (j : ι) (hj : j ∈ K) :
    S m + ∑ i ∈ K.filter (fun i => S i < S j), p i ≤ S j := by
  set F := K.filter (fun i => S i < S j) with hF
  have hdisj : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      Disjoint (Finset.Ico (S x) (S x + p x)) (Finset.Ico (S y) (S y + p y)) := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.1 hx).1
    have hy' := (Finset.mem_filter.1 hy).1
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    rw [Finset.mem_Ico] at hz1 hz2
    rcases hS x hx' y hy' hxy with h | h <;> omega
  have hcard : (F.biUnion (fun i => Finset.Ico (S i) (S i + p i))).card = ∑ i ∈ F, p i := by
    rw [Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp
  have hsub : F.biUnion (fun i => Finset.Ico (S i) (S i + p i)) ⊆ Finset.Ico (S m) (S j) := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨i, hi, hz⟩ := hz
    have hi' := Finset.mem_filter.1 hi
    have hij : i ≠ j := fun h => by rw [h] at hi'; exact lt_irrefl _ hi'.2
    have h1 := hmin i hi'.1
    rw [Finset.mem_Ico] at hz ⊢
    rcases hS i hi'.1 j hj hij with h | h <;> omega
  have := Finset.card_le_card hsub
  rw [hcard, Nat.card_Ico] at this
  have h2 := hmin j hj
  omega

theorem run_arith {ι : Type*} [DecidableEq ι] (K : Finset ι) (p d S : ι → ℕ) (a : ℕ)
    (hp : ∀ j ∈ K, 1 ≤ p j) (hd : Set.InjOn d K)
    (hS : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → S i + p i ≤ S j ∨ S j + p j ≤ S i)
    (ha : ∀ j ∈ K, a ≤ 2 * S j)
    (hdj : ∀ j ∈ K, d j ≤ a + ∑ i ∈ K.filter (fun i => d i < d j), p i + K.sup p) :
    ∑ j ∈ K, p j * d j ≤ ∑ j ∈ K, p j * (2 * S j + p j) := by
  rcases K.eq_empty_or_nonempty with hK | hK
  · simp [hK]
  obtain ⟨m, hm, hmin⟩ := K.exists_min_image S hK
  have hSinj : Set.InjOn S K := by
    intro i hi j hj hij
    by_contra hne
    have := hp i hi
    have := hp j hj
    rcases hS i hi j hj hne with h | h <;> omega
  set P := ∑ j ∈ K, p j with hP
  set Q := ∑ j ∈ K, p j * p j with hQ
  set Pm := K.sup p with hPm
  set A1 := ∑ j ∈ K, p j * ∑ i ∈ K.filter (fun i => d i < d j), p i with hA1
  set A2 := ∑ j ∈ K, p j * ∑ i ∈ K.filter (fun i => S i < S j), p i with hA2
  have h1 : ∑ j ∈ K, p j * d j ≤ a * P + A1 + P * Pm := by
    calc ∑ j ∈ K, p j * d j
        ≤ ∑ j ∈ K, p j * (a + ∑ i ∈ K.filter (fun i => d i < d j), p i + Pm) :=
          Finset.sum_le_sum (fun j hj => Nat.mul_le_mul_left _ (hdj j hj))
      _ = ∑ j ∈ K, (a * p j + p j * ∑ i ∈ K.filter (fun i => d i < d j), p i + Pm * p j) :=
          Finset.sum_congr rfl (fun j _ => by ring)
      _ = a * P + A1 + P * Pm := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← hA1, ← hP]
          ring
  have h2 : a * P + 2 * A2 + Q ≤ ∑ j ∈ K, p j * (2 * S j + p j) := by
    have hle : ∀ j ∈ K, p j * (a + 2 * ∑ i ∈ K.filter (fun i => S i < S j), p i + p j) ≤
        p j * (2 * S j + p j) := by
      intro j hj
      apply Nat.mul_le_mul_left
      have := chain K p S hS m hmin j hj
      have := ha m hm
      omega
    calc a * P + 2 * A2 + Q
        = ∑ j ∈ K, (a * p j + 2 * (p j * ∑ i ∈ K.filter (fun i => S i < S j), p i) + p j * p j) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← hA2, ← hP, ← hQ]
      _ = ∑ j ∈ K, p j * (a + 2 * ∑ i ∈ K.filter (fun i => S i < S j), p i + p j) :=
          Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ _ := Finset.sum_le_sum hle
  have h3 : 2 * A1 + Q = P * P := pair_id p d K hd
  have h4 : 2 * A2 + Q = P * P := pair_id p S K hSinj
  have h5 : Pm * Pm ≤ Q := by
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup K hK p
    rw [hPm, hjeq, hQ]
    exact Finset.single_le_sum (f := fun j => p j * p j) (fun i _ => Nat.zero_le _) hj
  have h6 : 2 * P * Pm ≤ P * P + Pm * Pm := by
    have : (2 * P * Pm : ℤ) ≤ P * P + Pm * Pm := by nlinarith [sq_nonneg ((P : ℤ) - Pm)]
    exact_mod_cast this
  nlinarith

end A36bbe2cf

/-! ### Direct proof of the upper bound: runs of a ratio-upper-set `H` -/

namespace P36bbe2cf

open DelayedSWPT.Model

section Runs

variable {n : ℕ} (I : Instance n) (inH : Fin n → Prop)

/-- Slot `y` is used by `H`: an `H` job runs, or an `H` job is selected but too long (gap). -/
def Occ (y : ℕ) : Prop :=
  (∃ k, inH k ∧ dswpt I k ≤ y ∧ y < dswpt I k + I.p k) ∨
    (∃ c, inH c ∧ dswptChoice I y = some c ∧ y < I.p c)

/-- A pending `H` job forces `Occ`, unless a non-`H` job started before its release runs. -/
theorem pend (hH : ∀ c j, R I c j → inH j → inH c) {j : Fin n} (hj : inH j) {y : ℕ}
    (hr : I.r j ≤ y) (hy : y < dswpt I j) :
    Occ I inH y ∨ ∃ k, ¬ inH k ∧ dswpt I k < I.r j ∧ dswpt I k < y ∧ y < dswpt I k + I.p k := by
  classical
  by_cases hf : (dswptState I y).free ≤ y
  · have hjA : j ∈ @available n I.r (dswptState I y) y := by
      simp only [available, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hr, none_of_le I hy.le⟩
    have hne : dswptChoice I y ≠ none := by
      unfold dswptChoice choice
      rw [if_pos hf]
      exact (P09bd5831.select_spec (Prec I) _).2 ⟨j, hjA⟩
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hne
    have hcH : inH c := hH c j (choice_min I hc j hjA) hj
    left
    by_cases hp : I.p c ≤ y
    · left
      have h1 := start_at I hc hp
      have h2 := I.p_pos c
      exact ⟨c, hcH, by omega, by omega⟩
    · right
      exact ⟨c, hcH, hc, by omega⟩
  · rcases free_inv I y with h | ⟨k, hk, hfk⟩
    · exact absurd h hf
    · have hyk : y < dswpt I k + I.p k := by omega
      by_cases hkH : inH k
      · left
        left
        exact ⟨k, hkH, hk.le, hyk⟩
      · right
        refine ⟨k, hkH, ?_, hk, hyk⟩
        by_contra hrk
        have hrk' : I.r j ≤ dswpt I k := not_lt.1 hrk
        apply hkH
        apply hH k j _ hj
        apply choice_min I (pi_spec I k).2.1 j
        simp only [available, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hrk', none_of_le I (by omega)⟩

theorem gap_lt_start {c : Fin n} {x : ℕ} (hx : x < I.p c) : x < dswpt I c := by
  have := start_ge_p I c
  omega

/-- After a gap generated by an `H` job `c`, every slot up to the start of `c` is `Occ`. -/
theorem gap_occ (hH : ∀ c j, R I c j → inH j → inH c) {c : Fin n} (hcH : inH c) {x : ℕ}
    (hc : dswptChoice I x = some c) :
    ∀ y, x ≤ y → y < dswpt I c → Occ I inH y := by
  intro y hxy hy
  have hr := (choice_spec I hc).2.1
  rcases pend I inH hH hcH (le_trans hr hxy) hy with h | ⟨k, _, hk1, hk2, hk3⟩
  · exact h
  · exfalso
    have hb := busy I (j := k) (t := x) (by omega) (by omega)
    have := (choice_spec I hc).1
    omega

/-- `[a, π_j)` is entirely `Occ`. -/
def Q (j : Fin n) (a : ℕ) : Prop := ∀ y, a ≤ y → y < dswpt I j → Occ I inH y

theorem Q_ex (j : Fin n) : ∃ a, Q I inH j a :=
  ⟨dswpt I j, fun _ h1 h2 => absurd h2 (not_lt.2 h1)⟩

/-- The start of the `Occ` run that ends at `π_j`. -/
noncomputable def u (j : Fin n) : ℕ := @Nat.find _ (Classical.decPred _) (Q_ex I inH j)

theorem u_spec (j : Fin n) : Q I inH j (u I inH j) :=
  @Nat.find_spec _ (Classical.decPred _) (Q_ex I inH j)

theorem u_min (j : Fin n) {a : ℕ} (ha : Q I inH j a) : u I inH j ≤ a :=
  @Nat.find_min' _ (Classical.decPred _) (Q_ex I inH j) a ha

theorem u_le (j : Fin n) : u I inH j ≤ dswpt I j :=
  u_min I inH j (fun _ h1 h2 => absurd h2 (not_lt.2 h1))

theorem boundary (j : Fin n) (hu : 0 < u I inH j) : ¬ Occ I inH (u I inH j - 1) := by
  intro hocc
  have hQ : Q I inH j (u I inH j - 1) := by
    intro y h1 h2
    by_cases hy : y = u I inH j - 1
    · rw [hy]
      exact hocc
    · exact u_spec I inH j y (by omega) h2
  have := u_min I inH j hQ
  omega

theorem same_run (i j : Fin n) (hQ : Q I inH i (u I inH j)) (hle : u I inH j ≤ dswpt I i) :
    u I inH i = u I inH j := by
  have h1 := u_min I inH i hQ
  by_contra hne
  have hlt : u I inH i < u I inH j := by omega
  apply boundary I inH j (by omega)
  exact u_spec I inH i _ (by omega) (by omega)

theorem cover (hH : ∀ c j, R I c j → inH j → inH c) {j : Fin n} (y : ℕ)
    (h1 : u I inH j ≤ y) (h2 : y < dswpt I j) :
    (∃ i, inH i ∧ u I inH i = u I inH j ∧ dswpt I i < dswpt I j ∧ dswpt I i ≤ y ∧
        y < dswpt I i + I.p i) ∨
      (∃ c, inH c ∧ u I inH c = u I inH j ∧ y < I.p c) := by
  rcases u_spec I inH j y h1 h2 with ⟨k, hkH, hk1, hk2⟩ | ⟨c, hcH, hc, hcp⟩
  · left
    have hkj : k ≠ j := by
      rintro rfl
      omega
    have hkd : dswpt I k + I.p k ≤ dswpt I j := by
      rcases no_overlap I k j hkj with h | h
      · exact h
      · have := I.p_pos j
        omega
    have hpk := I.p_pos k
    have hku : u I inH j ≤ dswpt I k := by
      by_contra hlt
      have hlt' : dswpt I k < u I inH j := not_le.1 hlt
      apply boundary I inH j (by omega)
      left
      exact ⟨k, hkH, by omega, by omega⟩
    refine ⟨k, hkH, same_run I inH k j (fun y' h1' h2' => u_spec I inH j y' h1' (by omega)) hku,
      by omega, hk1, hk2⟩
  · right
    have hcd := gap_lt_start I hcp
    refine ⟨c, hcH, same_run I inH c j ?_ (by omega), hcp⟩
    intro y' h1' h2'
    by_cases hy' : y' < y
    · exact u_spec I inH j y' h1' (by omega)
    · exact gap_occ I inH hH hcH hc y' (by omega) h2'

/-- A run starts no later than twice the release date of any of its jobs. -/
theorem u_le_two_r (hH : ∀ c j, R I c j → inH j → inH c) {j : Fin n} (hj : inH j) :
    u I inH j ≤ 2 * I.r j := by
  by_contra hlt
  have hlt' : 2 * I.r j < u I inH j := not_le.1 hlt
  have hu0 : 0 < u I inH j := by omega
  have hr : I.r j ≤ u I inH j - 1 := by omega
  have hd := u_le I inH j
  rcases pend I inH hH hj hr (by omega) with h | ⟨k, _, hk1, hk2, hk3⟩
  · exact boundary I inH j hu0 h
  · have := start_ge_p I k
    omega

variable [DecidablePred inH]

/-- The per-run bound on start times. -/
theorem run_bound (hH : ∀ c j, R I c j → inH j → inH c) (j : Fin n) :
    dswpt I j ≤ u I inH j +
      ∑ i ∈ ((Finset.univ.filter inH).filter (fun i => u I inH i = u I inH j)).filter
        (fun i => dswpt I i < dswpt I j), I.p i +
      ((Finset.univ.filter inH).filter (fun i => u I inH i = u I inH j)).sup I.p := by
  set K := (Finset.univ.filter inH).filter (fun i => u I inH i = u I inH j) with hK
  have hsub : Finset.Ico (u I inH j) (dswpt I j) ⊆
      (K.filter (fun i => dswpt I i < dswpt I j)).biUnion
          (fun i => Finset.Ico (dswpt I i) (dswpt I i + I.p i)) ∪
        Finset.range (K.sup I.p) := by
    intro y hy
    rw [Finset.mem_Ico] at hy
    rcases cover I inH hH y hy.1 hy.2 with ⟨i, hiH, hiu, hid, h1, h2⟩ | ⟨c, hcH, hcu, hcp⟩
    · apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      refine ⟨i, ?_, ?_⟩
      · simp only [hK, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨hiH, hiu⟩, hid⟩
      · rw [Finset.mem_Ico]
        exact ⟨h1, h2⟩
    · apply Finset.mem_union_right
      rw [Finset.mem_range]
      have hcK : c ∈ K := by
        simp only [hK, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hcH, hcu⟩
      have : I.p c ≤ K.sup I.p := Finset.le_sup (f := I.p) hcK
      omega
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((K.filter (fun i => dswpt I i < dswpt I j)).biUnion
          (fun i => Finset.Ico (dswpt I i) (dswpt I i + I.p i))) (Finset.range (K.sup I.p))
  have h3 := Finset.card_biUnion_le (s := K.filter (fun i => dswpt I i < dswpt I j))
    (t := fun i => Finset.Ico (dswpt I i) (dswpt I i + I.p i))
  have h4 : ∑ i ∈ K.filter (fun i => dswpt I i < dswpt I j),
      (Finset.Ico (dswpt I i) (dswpt I i + I.p i)).card =
      ∑ i ∈ K.filter (fun i => dswpt I i < dswpt I j), I.p i :=
    Finset.sum_congr rfl (fun i _ => by simp)
  rw [Nat.card_Ico] at h1
  rw [Finset.card_range] at h2
  have h5 := u_le I inH j
  omega

/-- The unweighted bound for one upper set `H`. -/
theorem starH (hH : ∀ c j, R I c j → inH j → inH c) (S : Fin n → ℕ)
    (hS : IsFeasible I.r I.p S) :
    ∑ j ∈ Finset.univ.filter inH, I.p j * dswpt I j ≤
      ∑ j ∈ Finset.univ.filter inH, I.p j * (2 * S j + I.p j) := by
  have hmaps : ∀ x ∈ Finset.univ.filter inH,
      u I inH x ∈ (Finset.univ.filter inH).image (u I inH) :=
    fun x hx => Finset.mem_image_of_mem _ hx
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, ← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_le_sum
  intro a _
  apply A36bbe2cf.run_arith _ I.p (dswpt I) S a
  · exact fun j _ => I.p_pos j
  · intro i _ j _ hij
    by_contra hne
    have := I.p_pos i
    have := I.p_pos j
    rcases no_overlap I i j hne with h | h <;> omega
  · exact fun i _ j _ hij => hS.2 i j hij
  · intro j hj
    have hj' := Finset.mem_filter.1 hj
    have hjH := (Finset.mem_filter.1 hj'.1).2
    have h1 := u_le_two_r I inH hH hjH
    have h2 := hS.1 j
    omega
  · intro j hj
    have hj' := Finset.mem_filter.1 hj
    have hb := run_bound I inH hH j
    rw [hj'.2] at hb
    exact hb

end Runs

/-- **Upper bound**: Delayed SWPT costs at most twice any feasible schedule. -/
theorem upper {n : ℕ} (I : Instance n) (S : Fin n → ℕ) (hS : IsFeasible I.r I.p S) :
    cost I.w I.p (dswpt I) ≤ 2 * cost I.w I.p S := by
  classical
  set ω : Fin n → ℝ := fun j => I.w j / (I.p j : ℝ) with hω
  set X : Fin n → ℝ := fun j => ((I.p j * (2 * S j + I.p j) : ℕ) : ℝ) -
    ((I.p j * dswpt I j : ℕ) : ℝ) with hX
  have hL := A36bbe2cf.layer_cake X _ Finset.univ ω rfl
    (fun j _ => div_nonneg (I.w_pos j).le (Nat.cast_nonneg _)) (fun j0 _ => by
      have hH : ∀ c j, R I c j → (fun j => ω j0 ≤ ω j) j → (fun j => ω j0 ≤ ω j) c :=
        fun c j hR hj => le_trans hj (R_div I c j hR)
      have h := starH I (fun j => ω j0 ≤ ω j) hH S hS
      rw [hX]
      simp only []
      rw [Finset.sum_sub_distrib, sub_nonneg]
      exact_mod_cast h)
  have key : ∀ j, ω j * X j = 2 * (I.w j * ((S j + I.p j : ℕ) : ℝ)) -
      I.w j * ((dswpt I j + I.p j : ℕ) : ℝ) := by
    intro j
    have hp : (I.p j : ℝ) ≠ 0 := by
      have := I.p_pos j
      have : (0 : ℝ) < I.p j := by exact_mod_cast this
      exact this.ne'
    simp only [hω, hX]
    push_cast
    field_simp
    ring
  unfold cost
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_sub_distrib, ← Finset.mul_sum] at hL
  linarith

end P36bbe2cf

open DelayedSWPT.Model in
theorem solution :
    IsLeast {ρ : ℝ | ∀ (n : ℕ) (I : Instance n) (S : Fin n → ℕ), IsFeasible I.r I.p S →
      cost I.w I.p (dswpt I) ≤ ρ * cost I.w I.p S} 2 := by
  exact ⟨fun _ I S hS => P36bbe2cf.upper I S hS, fun ρ hρ => P36bbe2cf.lower_bound ρ hρ⟩
