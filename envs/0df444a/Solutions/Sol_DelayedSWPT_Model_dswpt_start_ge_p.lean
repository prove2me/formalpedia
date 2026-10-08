-- Prove2me | solution 1 for DelayedSWPT.Model.dswpt_start_ge_p
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T11:17:24.630252+00:00
-- url     : https://prove2.me/submissions/71d09b1b-c474-4a24-9dfa-33aa5c561a20

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

open DelayedSWPT.Model in
theorem solution {n : ℕ} (I : Instance n) (j : Fin n) : I.p j ≤ dswpt I j := by
  unfold dswpt dswptState
  have hs := @P09bd5831.all_started n I.r I.p (Prec I) (Classical.decRel _) I.p_pos j
  obtain ⟨s0, hs0⟩ := Option.ne_none_iff_exists'.1 hs
  rw [hs0]
  exact (@P09bd5831.inv n I.r I.p (Prec I) (Classical.decRel _) _).1 j s0 hs0
