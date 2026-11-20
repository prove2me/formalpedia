-- Prove2me | solution 1 for EditMulticoloring.Code.interval_restriction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:39:42.050259+00:00
-- url     : https://prove2.me/submissions/ad15942d-0b1d-49ad-b981-899fc17681e5

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Words

section
set_option autoImplicit false
namespace EditMulticoloring.Dev.Interval
open EditMulticoloring.Code OAI.EditDistortion

variable {q : ℕ}

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

theorem step_symm {x y : Word q} (h : Step true x y) : Step true y x := by
  cases h with
  | insert p r a => exact Step.delete p r a
  | delete p r a => exact Step.insert p r a
  | substitute _ p r a b => exact Step.substitute rfl p r b a

theorem script_symm {n : ℕ} {x y : Word q} (h : Script true n x y) : Script true n y x := by
  induction h with
  | nil x => exact Script.nil x
  | @cons n x w z first rest ih => exact script_snoc ih (step_symm first)

theorem edit_le {k : ℕ} {x y : Word q} (h : Script true k x y) : edit x y ≤ k :=
  Nat.sInf_le (show k ∈ {n | Script true n x y} from h)

theorem edit_script (x y : Word q) : Script true (edit x y) x y :=
  Nat.sInf_mem (show {n | Script true n x y}.Nonempty from script_exists x y)

theorem edit_trans (x y z : Word q) : edit x z ≤ edit x y + edit y z :=
  edit_le (script_trans (edit_script x y) (edit_script y z))

theorem edit_symm (x y : Word q) : edit x y = edit y x :=
  le_antisymm (edit_le (script_symm (edit_script y x))) (edit_le (script_symm (edit_script x y)))

theorem step_append {a b w : Word q} (h : Step true (a ++ b) w) :
    ∃ a' b', w = a' ++ b' ∧ ((Step true a a' ∧ b' = b) ∨ (a' = a ∧ Step true b b')) := by
  generalize hx : a ++ b = x at h
  cases h with
  | insert p r c =>
    rcases List.append_eq_append_iff.1 hx with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
    · exact ⟨a, a' ++ c :: r, by simp, Or.inr ⟨rfl, Step.insert a' r c⟩⟩
    · exact ⟨p ++ c :: c', b, by simp, Or.inl ⟨Step.insert p c' c, rfl⟩⟩
  | delete p r c =>
    rcases List.append_eq_append_iff.1 hx with ⟨a', rfl, rfl⟩ | ⟨c', rfl, h2⟩
    · exact ⟨a, a' ++ r, by simp, Or.inr ⟨rfl, Step.delete a' r c⟩⟩
    · cases c' with
      | nil =>
        simp only [List.nil_append] at h2
        subst h2
        exact ⟨p, r, by simp, Or.inr ⟨by simp, Step.delete [] r c⟩⟩
      | cons d c'' =>
        simp only [List.cons_append, List.cons.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨p ++ c'', b, by simp, Or.inl ⟨Step.delete p c'' _, rfl⟩⟩
  | substitute hs p r c d =>
    rcases List.append_eq_append_iff.1 hx with ⟨a', rfl, rfl⟩ | ⟨c', rfl, h2⟩
    · exact ⟨a, a' ++ d :: r, by simp, Or.inr ⟨rfl, Step.substitute rfl a' r c d⟩⟩
    · cases c' with
      | nil =>
        simp only [List.nil_append] at h2
        subst h2
        exact ⟨p, d :: r, by simp, Or.inr ⟨by simp, Step.substitute rfl [] r c d⟩⟩
      | cons e c'' =>
        simp only [List.cons_append, List.cons.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨p ++ d :: c'', b, by simp, Or.inl ⟨Step.substitute rfl p c'' _ d, rfl⟩⟩

theorem script_append {n : ℕ} {x y : Word q} (h : Script true n x y) :
    ∀ a b : Word q, x = a ++ b → ∃ y1 y2 : Word q, ∃ i j : ℕ, y = y1 ++ y2 ∧ i + j ≤ n ∧
      Script true i a y1 ∧ Script true j b y2 := by
  induction h with
  | nil x =>
    intro a b hx
    subst hx
    exact ⟨a, b, 0, 0, rfl, le_rfl, Script.nil _, Script.nil _⟩
  | @cons n x w z first rest ih =>
    intro a b hx
    subst hx
    obtain ⟨a', b', hw, (⟨h1, rfl⟩ | ⟨rfl, h2⟩)⟩ := step_append first
    · subst hw
      obtain ⟨y1, y2, i, j, hy, hij, hi, hj⟩ := ih a' b' rfl
      exact ⟨y1, y2, i + 1, j, hy, by omega, Script.cons h1 hi, hj⟩
    · subst hw
      obtain ⟨y1, y2, i, j, hy, hij, hi, hj⟩ := ih a' b' rfl
      exact ⟨y1, y2, i, j + 1, hy, by omega, hi, Script.cons h2 hj⟩

theorem script_length {n : ℕ} {x y : Word q} (h : Script true n x y) :
    y.length ≤ x.length + n ∧ x.length ≤ y.length + n := by
  induction h with
  | nil x => simp
  | @cons n x w z first rest ih =>
    have : w.length ≤ x.length + 1 ∧ x.length ≤ w.length + 1 := by
      cases first <;> simp <;> omega
    omega

/-- the factor `y[p, r)` -/
def g (y : Word q) (p r : ℕ) : Word q := (y.drop p).take (r - p)

theorem g_left (y : Word q) (p r : ℕ) (hp : 1 ≤ p) (hpr : p ≤ r) (hr : r ≤ y.length) :
    g y (p - 1) r = y[p - 1]'(by omega) :: g y p r := by
  unfold g
  have h1 : y.drop (p - 1) = y[p - 1]'(by omega) :: y.drop p := by
    rw [List.drop_eq_getElem_cons (by omega)]
    congr 2
    omega
  rw [h1, show r - (p - 1) = (r - p) + 1 by omega]
  rfl

theorem g_right (y : Word q) (p r : ℕ) (hpr : p ≤ r) (hr : r < y.length) :
    g y p (r + 1) = g y p r ++ [y[r]] := by
  unfold g
  rw [show r + 1 - p = (r - p) + 1 by omega, List.take_add_one]
  simp [List.getElem?_drop, show p + (r - p) = r by omega, hr]

theorem edit_cons_le (c : Fin q) (a : Word q) : edit (c :: a) a ≤ 1 := by
  have := Script.cons (Step.delete (substitutions := true) [] a c) (Script.nil a)
  exact edit_le (by simpa using this)

theorem edit_snoc_le (c : Fin q) (a : Word q) : edit a (a ++ [c]) ≤ 1 := by
  have := Script.cons (Step.insert (substitutions := true) a [] c) (Script.nil _)
  exact edit_le (by simpa using this)

theorem grow_left (y : Word q) (r : ℕ) (hr : r ≤ y.length) :
    ∀ i p : ℕ, i ≤ p → p ≤ r → edit (g y p r) (g y (p - i) r) ≤ i := by
  intro i
  induction i with
  | zero => intro p _ _; simp [edit_le (Script.nil _)]
  | succ i ih =>
    intro p hi hpr
    have h1 := ih p (by omega) hpr
    have h2 := g_left y (p - i) r (by omega) (by omega) hr
    have h3 : edit (g y (p - i) r) (g y (p - i - 1) r) ≤ 1 := by
      rw [edit_symm, h2]
      exact edit_cons_le _ _
    have := edit_trans (g y p r) (g y (p - i) r) (g y (p - i - 1) r)
    rw [show p - (i + 1) = p - i - 1 by omega]
    omega

theorem grow_right (y : Word q) (p : ℕ) :
    ∀ i r : ℕ, r + i ≤ y.length → p ≤ r → edit (g y p r) (g y p (r + i)) ≤ i := by
  intro i
  induction i with
  | zero => intro r _ _; simp [edit_le (Script.nil _)]
  | succ i ih =>
    intro r hr hpr
    have h1 := ih r (by omega) hpr
    have h2 := g_right y p (r + i) (by omega) (by omega)
    have h3 : edit (g y p (r + i)) (g y p (r + i + 1)) ≤ 1 := by
      rw [h2]
      exact edit_snoc_le _ _
    have := edit_trans (g y p r) (g y p (r + i)) (g y p (r + i + 1))
    rw [← add_assoc]
    omega

theorem edit_to_big (y : Word q) (p r P R : ℕ) (hP : P ≤ p) (hpr : p ≤ r) (hrR : r ≤ R)
    (hR : R ≤ y.length) : edit (g y p r) (g y P R) ≤ (p - P) + (R - r) := by
  have h1 := grow_left y r (by omega) (p - P) p (by omega) hpr
  have h2 := grow_right y (p - (p - P)) (R - r) r (by omega) (by omega)
  have e1 : p - (p - P) = P := by omega
  have e2 : r + (R - r) = R := by omega
  rw [e1] at h1 h2
  rw [e2] at h2
  have := edit_trans (g y p r) (g y P r) (g y P R)
  omega

theorem edit_g (y : Word q) (p r j e : ℕ) (hpr : p ≤ r) (hje : j ≤ e) (hr : r ≤ y.length)
    (he : e ≤ y.length) :
    edit (g y p r) (g y j e) ≤ (p - j) + (j - p) + (r - e) + (e - r) := by
  have h1 := edit_to_big y p r (min p j) (max r e) (by omega) hpr (by omega) (by omega)
  have h2 := edit_to_big y j e (min p j) (max r e) (by omega) hje (by omega) (by omega)
  have h3 := edit_symm (g y (min p j) (max r e)) (g y j e)
  have := edit_trans (g y p r) (g y (min p j) (max r e)) (g y j e)
  omega

theorem interval_eq_g (y : Word q) (lo hi : ℕ) (hlo : 1 ≤ lo) (horder : lo ≤ hi) :
    interval y lo hi = g y (lo - 1) hi := by
  unfold interval g
  congr 1
  omega

theorem main (lo hi n : ℕ) (hlo : 1 ≤ lo) (horder : lo ≤ hi) (hhi : hi ≤ n)
    (x y : Word q) (hx : x.length = n) (hy : y.length = n) :
    edit (interval x lo hi) (interval y lo hi) ≤ edit x y := by
  have hsc := edit_script x y
  set xr := x.drop (lo - 1) with hxr
  have hxdec : x = x.take (lo - 1) ++ (xr.take (hi - lo + 1) ++ xr.drop (hi - lo + 1)) := by
    rw [List.take_append_drop, hxr, List.take_append_drop]
  obtain ⟨y1, y23, i1, j1, hy1, hij1, hs1, hs23⟩ := script_append hsc _ _ hxdec
  obtain ⟨y2, y3, i2, i3, hy2, hij2, hs2, hs3⟩ := script_append hs23 _ _ rfl
  subst hy2
  have hl1 := script_length hs1
  have hl3 := script_length hs3
  have hlx1 : (x.take (lo - 1)).length = lo - 1 := by simp; omega
  have hlx3 : (xr.drop (hi - lo + 1)).length = n - hi := by simp [hxr]; omega
  rw [hlx1] at hl1
  rw [hlx3] at hl3
  have hlen : y1.length + (y2.length + y3.length) = n := by
    rw [← hy, hy1]; simp
  have hyg : y2 = g y y1.length (y1.length + y2.length) := by
    rw [hy1]; unfold g; simp
  have hI : interval x lo hi = xr.take (hi - lo + 1) := rfl
  have key := edit_g y y1.length (y1.length + y2.length) (lo - 1) hi (by omega) (by omega)
    (by omega) (by omega)
  rw [← interval_eq_g y lo hi hlo horder, ← hyg] at key
  have t1 := edit_le hs2
  have := edit_trans (interval x lo hi) y2 (interval y lo hi)
  have e2 : edit (interval x lo hi) y2 ≤ i2 := by rw [hI]; exact edit_le hs2
  omega

end EditMulticoloring.Dev.Interval

namespace EditMulticoloring.Code
open EditMulticoloring.Dev.Interval in
theorem chk_interval_restriction (q t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t)
    (n lo hi : ℕ) (hlo : 1 ≤ lo) (horder : lo ≤ hi) (hhi : hi ≤ n)
    (x y : Word q) (hx : x.length = n) (hy : y.length = n) :
    distance (interval x lo hi) (interval y lo hi) ≤ distance x y :=
  main lo hi n hlo horder hhi x y hx hy

end EditMulticoloring.Code
end

theorem solution : type_of% @EditMulticoloring.Code.chk_interval_restriction := @EditMulticoloring.Code.chk_interval_restriction
