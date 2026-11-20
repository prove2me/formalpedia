-- Prove2me | solution 1 for EditMulticoloring.Code.edit_ball_volume
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:39:41.897384+00:00
-- url     : https://prove2.me/submissions/201777bb-cb7b-40bf-bdbe-3e2b7f9b7cc5

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Words

section
set_option autoImplicit false
namespace EditMulticoloring.Dev.Ball
open EditMulticoloring.Code OAI.EditDistortion

variable {q : ℕ}

theorem length_availableEdits (hq : 1 ≤ q) (x : Word q) : (availableEdits x).length ≤ 2 * q * (x.length + 1) := by
  have h3 : (((List.range x.length).flatMap fun i =>
      ((List.finRange q).filter fun a => x[i]? ≠ some a).map fun a => (PositionedEdit.replace i a : PositionedEdit q))).length ≤ x.length * (q - 1) := by
    rw [List.length_flatMap]
    calc _ ≤ ((List.range x.length).map fun _ => q - 1).sum := by
          apply List.sum_le_sum
          intro i hi
          simp only [List.length_map]
          have hi' : i < x.length := by simpa using hi
          have : ((List.finRange q).filter fun a => decide (x[i]? ≠ some a)).length < (List.finRange q).length := by
            rw [List.length_filter_lt_length_iff_exists]
            refine ⟨x[i]'hi', ?_, ?_⟩
            · simp
            · simp [hi']
          simp only [List.length_finRange] at this
          omega
        _ = x.length * (q - 1) := by simp
  have h1 : (((List.range (x.length + 1)).flatMap fun i =>
      (List.finRange q).map fun a => (PositionedEdit.insert i a : PositionedEdit q))).length = (x.length + 1) * q := by
    rw [List.length_flatMap]
    simp
  simp only [availableEdits, List.length_append, List.length_map, List.length_range]
  rw [h1]
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h3
  nlinarith [h3]

theorem applyEdit_length {x z : Word q} {e : PositionedEdit q} (h : applyEdit x e = some z) :
    z.length ≤ x.length + 1 := by
  cases e with
  | insert i a =>
    simp only [applyEdit] at h
    split_ifs at h with hi
    cases h
    simp; omega
  | delete i =>
    simp only [applyEdit] at h
    split_ifs at h with hi
    cases h
    simp; omega
  | replace i a =>
    simp only [applyEdit] at h
    split_ifs at h with hi
    cases h
    simp; omega

theorem scripts_length (hq : 1 ≤ q) : ∀ (s L : ℕ) (x : Word q), x.length ≤ L →
    (scripts s x).length ≤ ∑ i ∈ Finset.range (s + 1), (2 * q * (L + s + 1)) ^ i := by
  intro s
  induction s with
  | zero => intro L x _; simp [scripts]
  | succ s ih =>
    intro L x hx
    set B := 2 * q * (L + (s + 1) + 1) with hB
    have hterm : ∀ e ∈ availableEdits x,
        (match applyEdit x e with
          | none => []
          | some z => (scripts s z).map fun (p : List (PositionedEdit q) × Word q) => (e :: p.1, p.2)).length
          ≤ ∑ i ∈ Finset.range (s + 1), B ^ i := by
      intro e _
      cases h : applyEdit x e with
      | none => simp
      | some z =>
        simp only [List.length_map]
        have hz := applyEdit_length h
        have := ih (L + 1) z (by omega)
        have e1 : L + 1 + s + 1 = L + (s + 1) + 1 := by omega
        rw [e1] at this
        exact this
    have hsum := List.sum_le_card_nsmul ((availableEdits x).map fun e =>
        (match applyEdit x e with
          | none => []
          | some z => (scripts s z).map fun (p : List (PositionedEdit q) × Word q) => (e :: p.1, p.2)).length)
        (∑ i ∈ Finset.range (s + 1), B ^ i) (by
          intro n hn
          obtain ⟨e, he, rfl⟩ := List.mem_map.1 hn
          exact hterm e he)
    have hN : (availableEdits x).length ≤ B := by
      refine (length_availableEdits hq x).trans ?_
      rw [hB]
      apply Nat.mul_le_mul_left
      omega
    have key : (scripts (s + 1) x).length = 1 + ((availableEdits x).map fun e =>
        (match applyEdit x e with
          | none => []
          | some z => (scripts s z).map fun (p : List (PositionedEdit q) × Word q) => (e :: p.1, p.2)).length).sum := by
      simp only [scripts, List.length_cons, List.length_flatMap]
      exact Nat.add_comm _ _
    rw [key]
    rw [List.length_map, smul_eq_mul] at hsum
    have h2 := Nat.mul_le_mul_right (∑ i ∈ Finset.range (s + 1), B ^ i) hN
    have h3 : 1 + ((availableEdits x).map fun e =>
        (match applyEdit x e with
          | none => []
          | some z => (scripts s z).map fun (p : List (PositionedEdit q) × Word q) => (e :: p.1, p.2)).length).sum
        ≤ 1 + B * ∑ i ∈ Finset.range (s + 1), B ^ i := by omega
    refine h3.trans (le_of_eq ?_)
    rw [Finset.sum_range_succ' (fun i => B ^ i) (s + 1)]
    simp [pow_succ, Finset.mul_sum, mul_comm, add_comm]

theorem ball_card_le (s : ℕ) (hq : 2 ≤ q) (m : ℕ) (x : Word q) (hx : x.length = m) :
    (ball s x).card ≤ radiusBound q s m := by
  unfold ball radiusBound
  refine (List.toFinset_card_le _).trans ?_
  rw [List.length_map]
  refine (scripts_length (by omega) s m x hx.le).trans ?_
  have hB : 1 ≤ 2 * q * (m + s + 1) := by nlinarith
  calc _ ≤ ∑ i ∈ Finset.range (s + 1), (2 * q * (m + s + 1)) ^ s := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.pow_le_pow_right hB (by simpa [Nat.lt_succ_iff] using hi)
    _ = _ := by simp

theorem mem_ball_succ (s : ℕ) (x y : Word q) :
    y ∈ ball (s + 1) x ↔ y = x ∨ ∃ e ∈ availableEdits x, ∃ z, applyEdit x e = some z ∧ y ∈ ball s z := by
  simp only [ball, scripts, List.map_cons, List.mem_toFinset, List.mem_cons, List.mem_map,
    List.mem_flatMap]
  constructor
  · rintro (h | ⟨⟨es, y'⟩, ⟨e, he, hm⟩, rfl⟩)
    · exact Or.inl h
    · right
      cases hz : applyEdit x e with
      | none => rw [hz] at hm; simp at hm
      | some z =>
        rw [hz] at hm
        simp only [List.mem_map] at hm
        obtain ⟨⟨es0, y0⟩, h0, h1⟩ := hm
        simp only [Prod.mk.injEq] at h1
        refine ⟨e, he, z, hz, (es0, y0), h0, ?_⟩
        simp [← h1.2]
  · rintro (h | ⟨e, he, z, hz, a, ha, rfl⟩)
    · exact Or.inl h
    · right
      refine ⟨(e :: a.1, a.2), ⟨e, he, ?_⟩, rfl⟩
      rw [hz]
      simp only [List.mem_map]
      exact ⟨a, ha, rfl⟩

theorem step_of_applyEdit {x z : Word q} {e : PositionedEdit q} (h : applyEdit x e = some z) :
    Step true x z := by
  cases e with
  | insert i a =>
    simp only [applyEdit] at h
    split_ifs at h with hi
    cases h
    have := Step.insert (substitutions := true) (x.take i) (x.drop i) a
    rwa [List.take_append_drop] at this
  | delete i =>
    simp only [applyEdit] at h
    split_ifs at h with hi
    cases h
    have hx : x = x.take i ++ x[i] :: x.drop (i + 1) := by
      conv_lhs => rw [← List.take_append_drop i x, List.drop_eq_getElem_cons hi]
    have := Step.delete (substitutions := true) (x.take i) (x.drop (i + 1)) x[i]
    rwa [← hx] at this
  | replace i a =>
    simp only [applyEdit] at h
    split_ifs at h with hi
    cases h
    have hx : x = x.take i ++ x[i]'hi.1 :: x.drop (i + 1) := by
      conv_lhs => rw [← List.take_append_drop i x, List.drop_eq_getElem_cons hi.1]
    have := Step.substitute (substitutions := true) rfl (x.take i) (x.drop (i + 1)) (x[i]'hi.1) a
    rwa [← hx] at this

theorem applyEdit_of_step {x y : Word q} (hs : Step true x y) (hne : y ≠ x) :
    ∃ e ∈ availableEdits x, applyEdit x e = some y := by
  cases hs with
  | insert p r a =>
    refine ⟨.insert p.length a, ?_, ?_⟩
    · simp [availableEdits]
    · simp [applyEdit]
  | delete p r a =>
    refine ⟨.delete p.length, ?_, ?_⟩
    · simp [availableEdits]
    · simp [applyEdit]
  | substitute _ p r a b =>
    have hab : a ≠ b := by
      rintro rfl; exact hne rfl
    refine ⟨.replace p.length b, ?_, ?_⟩
    · simp [availableEdits, hab]
    · simp [applyEdit, hab]

theorem script_of_mem_ball : ∀ (s : ℕ) (x y : Word q), y ∈ ball s x → ∃ k ≤ s, Script true k x y := by
  intro s
  induction s with
  | zero =>
    intro x y h
    simp [ball, scripts] at h
    subst h
    exact ⟨0, le_rfl, Script.nil _⟩
  | succ s ih =>
    intro x y h
    rcases (mem_ball_succ s x y).1 h with rfl | ⟨e, _, z, hz, hy⟩
    · exact ⟨0, by omega, Script.nil _⟩
    · obtain ⟨k, hk, hsc⟩ := ih z y hy
      exact ⟨k + 1, by omega, Script.cons (step_of_applyEdit hz) hsc⟩

theorem ball_mono : ∀ (s : ℕ) (x y : Word q), y ∈ ball s x → y ∈ ball (s + 1) x := by
  intro s
  induction s with
  | zero =>
    intro x y h
    simp [ball, scripts] at h
    subst h
    exact (mem_ball_succ 0 _ _).2 (Or.inl rfl)
  | succ s ih =>
    intro x y h
    rcases (mem_ball_succ s x y).1 h with rfl | ⟨e, he, z, hz, hy⟩
    · exact (mem_ball_succ _ _ _).2 (Or.inl rfl)
    · exact (mem_ball_succ _ _ _).2 (Or.inr ⟨e, he, z, hz, ih z y hy⟩)

theorem mem_ball_of_script : ∀ (k : ℕ) (x y : Word q), Script true k x y → y ∈ ball k x := by
  intro k x y h
  induction h with
  | nil x => simp [ball, scripts]
  | @cons n x w z first rest ih =>
    by_cases hw : w = x
    · subst hw
      exact ball_mono _ _ _ ih
    · obtain ⟨e, he, hz⟩ := applyEdit_of_step first hw
      exact (mem_ball_succ _ _ _).2 (Or.inr ⟨e, he, w, hz, ih⟩)

theorem ball_mono_le {s t : ℕ} (hst : s ≤ t) (x y : Word q) (h : y ∈ ball s x) : y ∈ ball t x := by
  induction hst with
  | refl => exact h
  | step _ ih => exact ball_mono _ _ _ ih

theorem script_trans {a b : ℕ} {x y z : Word q} (h1 : Script true a x y) (h2 : Script true b y z) :
    Script true (a + b) x z := by
  induction h1 with
  | nil x => simpa using h2
  | @cons n x w y first rest ih =>
    have := Script.cons first (ih h2)
    rwa [show n + 1 + b = n + b + 1 by omega]

theorem script_del : ∀ (a b : Word q), Script true a.length (a ++ b) b := by
  intro a
  induction a with
  | nil => intro b; exact Script.nil _
  | cons c l ih =>
    intro b
    exact Script.cons (Step.delete (substitutions := true) [] (l ++ b) c) (ih b)

theorem script_snoc {n : ℕ} {x y z : Word q} (h : Script true n x y) (st : Step true y z) :
    Script true (n + 1) x z := by
  have := script_trans h (Script.cons st (Script.nil z))
  simpa using this

theorem script_ins : ∀ (a b : Word q), Script true a.length b (a ++ b) := by
  intro a
  induction a with
  | nil => intro b; exact Script.nil _
  | cons c l ih =>
    intro b
    exact script_snoc (ih b) (Step.insert (substitutions := true) [] (l ++ b) c)

theorem script_exists (x y : Word q) : ∃ n, Script true n x y := by
  have h1 := script_del x []
  have h2 := script_ins y []
  simp only [List.append_nil] at h1 h2
  exact ⟨_, script_trans h1 h2⟩

theorem mem_ball_iff (s : ℕ) (x y : Word q) : y ∈ ball s x ↔ distance x y ≤ s := by
  constructor
  · intro h
    obtain ⟨k, hk, hsc⟩ := script_of_mem_ball s x y h
    exact (Nat.sInf_le (show k ∈ {n | Script true n x y} from hsc)).trans hk
  · intro h
    have hne : {n | Script true n x y}.Nonempty := script_exists x y
    have hm := Nat.sInf_mem hne
    exact ball_mono_le h x y (mem_ball_of_script _ x y hm)

theorem asymptotic (q s : ℕ) (hq : 2 ≤ q) (hs : 1 ≤ s) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      c * (m : ℝ) ^ s ≤ (radiusBound q s m : ℝ) ∧
      (radiusBound q s m : ℝ) ≤ C * (m : ℝ) ^ s := by
  refine ⟨1, ((s + 1) * (2 * q * (s + 2)) ^ s : ℕ), by norm_num, ?_, 1, le_rfl, ?_⟩
  · have : 0 < (s + 1) * (2 * q * (s + 2)) ^ s := by positivity
    exact_mod_cast this
  · intro m hm
    constructor
    · unfold radiusBound
      have h1 : m ^ s ≤ (s + 1) * (2 * q * (m + s + 1)) ^ s := by
        calc m ^ s ≤ (2 * q * (m + s + 1)) ^ s := Nat.pow_le_pow_left (by nlinarith) s
          _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)
      have : ((m : ℕ) ^ s : ℕ) ≤ (s + 1) * (2 * q * (m + s + 1)) ^ s := h1
      simpa using (by exact_mod_cast this : ((m : ℝ) ^ s) ≤ (((s + 1) * (2 * q * (m + s + 1)) ^ s : ℕ) : ℝ))
    · unfold radiusBound
      have h1 : (s + 1) * (2 * q * (m + s + 1)) ^ s ≤ ((s + 1) * (2 * q * (s + 2)) ^ s) * m ^ s := by
        have h0 : m + s + 1 ≤ (s + 2) * m := by nlinarith
        have h2 : (2 * q * (m + s + 1)) ^ s ≤ (2 * q * (s + 2) * m) ^ s :=
          Nat.pow_le_pow_left (by calc 2 * q * (m + s + 1) ≤ 2 * q * ((s + 2) * m) := Nat.mul_le_mul_left _ h0
                                  _ = _ := by ring) s
        calc _ ≤ (s + 1) * (2 * q * (s + 2) * m) ^ s := Nat.mul_le_mul_left _ h2
          _ = _ := by rw [mul_pow]; ring
      exact_mod_cast h1

end EditMulticoloring.Dev.Ball

namespace EditMulticoloring.Code
open EditMulticoloring.Dev.Ball in
theorem chk_edit_ball_volume (q s : ℕ) (hq : 2 ≤ q) (hs : 1 ≤ s) :
    (∀ (m : ℕ) (hm : 1 ≤ m) (x : Word q), x.length = m →
      (scripts s x).length ≤ ∑ i ∈ Finset.range (s + 1), (2 * q * (m + s + 1)) ^ i ∧
      (∀ y : Word q, y ∈ ball s x ↔ distance x y ≤ s) ∧
      (ball s x).card ≤ radiusBound q s m) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      c * (m : ℝ) ^ s ≤ (radiusBound q s m : ℝ) ∧
      (radiusBound q s m : ℝ) ≤ C * (m : ℝ) ^ s) := by
  refine ⟨fun m hm x hx => ⟨?_, fun y => mem_ball_iff s x y, ball_card_le s hq m x hx⟩, asymptotic q s hq hs⟩
  have := scripts_length (q := q) (by omega) s m x hx.le
  exact this

end EditMulticoloring.Code
end

theorem solution : type_of% @EditMulticoloring.Code.chk_edit_ball_volume := @EditMulticoloring.Code.chk_edit_ball_volume
