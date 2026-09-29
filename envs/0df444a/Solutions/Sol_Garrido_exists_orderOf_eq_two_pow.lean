-- Prove2me | solution 1 for Garrido.exists_orderOf_eq_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T13:16:25.649716+00:00
-- url     : https://prove2.me/submissions/48857228-2e60-437f-8ac1-9c8b8ad821dd

import Mathlib
import Definitions.Def_Chou_Classes
import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Growth
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Garrido_Grigorchuk

namespace Garrido.GR.St

open Garrido

local notation "P" => Equiv.Perm (List Bool)
local notation "Γ" => GrigorchukGroup

@[simp] theorem C1a_apply (w : List Bool) :
    (((GrigorchukGroup.a : Γ) : BinaryTreeAut) : P) w = grigAFun w := rfl
@[simp] theorem C1b_apply (w : List Bool) :
    (((GrigorchukGroup.b : Γ) : BinaryTreeAut) : P) w = grigBFun w := rfl
@[simp] theorem C1c_apply (w : List Bool) :
    (((GrigorchukGroup.c : Γ) : BinaryTreeAut) : P) w = grigCFun w := rfl
@[simp] theorem C1d_apply (w : List Bool) :
    (((GrigorchukGroup.d : Γ) : BinaryTreeAut) : P) w = grigDFun w := rfl
@[simp] theorem C1mul_apply (g h : Γ) (w : List Bool) :
    (((g * h : Γ) : BinaryTreeAut) : P) w =
      ((g : BinaryTreeAut) : P) (((h : BinaryTreeAut) : P) w) := rfl
@[simp] theorem C1one_apply (w : List Bool) : (((1 : Γ) : BinaryTreeAut) : P) w = w := rfl

theorem C1len (g : Γ) (v : List Bool) : (((g : BinaryTreeAut) : P) v).length = v.length :=
  (g : BinaryTreeAut).2.1 v

/-! ### Target 1 -/



/-! ### Target 2 -/



/-! ### Target 3 -/



end Garrido.GR.St

namespace Garrido.GR.Sec

open Garrido

local notation "P" => Equiv.Perm (List Bool)


end Garrido.GR.Sec

namespace Garrido.GR.Tor

open Equiv

abbrev P' := Perm (List Bool)

def pairFun (u v : List Bool → List Bool) : List Bool → List Bool
  | [] => []
  | false :: w => false :: u w
  | true :: w => true :: v w

def pr (u v : P') : P' where
  toFun := pairFun u v
  invFun := pairFun ⇑u⁻¹ ⇑v⁻¹
  left_inv w := by rcases w with _ | ⟨_ | _, w⟩ <;> simp [pairFun]
  right_inv w := by rcases w with _ | ⟨_ | _, w⟩ <;> simp [pairFun]

@[simp] lemma pr_nil (u v : P') : pr u v [] = [] := rfl
@[simp] lemma pr_false (u v : P') (w) : pr u v (false :: w) = false :: u w := rfl
@[simp] lemma pr_true (u v : P') (w) : pr u v (true :: w) = true :: v w := rfl

lemma pr_mul (u v u' v' : P') : pr u v * pr u' v' = pr (u * u') (v * v') := by
  ext w; rcases w with _ | ⟨_ | _, w⟩ <;> simp

lemma pr_one : pr 1 1 = 1 := by
  ext w; rcases w with _ | ⟨_ | _, w⟩ <;> simp

lemma pr_pow (u v : P') (n : ℕ) : pr u v ^ n = pr (u ^ n) (v ^ n) := by
  induction n with
  | zero => simp [pr_one]
  | succ n ih => rw [pow_succ, ih, pr_mul, pow_succ, pow_succ]

def σ : P' := ((grigA : BinaryTreeAut) : P')
def eB : P' := ((grigB : BinaryTreeAut) : P')
def eC : P' := ((grigC : BinaryTreeAut) : P')
def eD : P' := ((grigD : BinaryTreeAut) : P')

@[simp] lemma σ_apply (w) : σ w = grigAFun w := rfl
@[simp] lemma eB_apply (w) : eB w = grigBFun w := rfl
@[simp] lemma eC_apply (w) : eC w = grigCFun w := rfl
@[simp] lemma eD_apply (w) : eD w = grigDFun w := rfl

lemma σ_pr (u v : P') : σ * pr u v = pr v u * σ := by
  ext w; rcases w with _ | ⟨_ | _, w⟩ <;> simp [grigAFun]

lemma σσ : σ * σ = 1 := by ext w; simp [grigAFun_involutive w]

lemma eB_eq : eB = pr σ eC := by
  ext w; rcases w with _ | ⟨_ | _, w⟩ <;> simp [grigBFun]
lemma eC_eq : eC = pr σ eD := by
  ext w; rcases w with _ | ⟨_ | _, w⟩ <;> simp [grigCFun]
lemma eD_eq : eD = pr 1 eB := by
  ext w; rcases w with _ | ⟨_ | _, w⟩ <;> simp [grigDFun]

lemma bcd_rel (w : List Bool) :
    grigBFun (grigCFun w) = grigDFun w ∧ grigCFun (grigBFun w) = grigDFun w ∧
    grigBFun (grigDFun w) = grigCFun w ∧ grigDFun (grigBFun w) = grigCFun w ∧
    grigCFun (grigDFun w) = grigBFun w ∧ grigDFun (grigCFun w) = grigBFun w := by
  induction w with
  | nil => simp [grigBFun, grigCFun, grigDFun]
  | cons x w ih =>
    cases x <;> simp [grigBFun, grigCFun, grigDFun, grigAFun_involutive w, ih]

inductive L | a | b | c | d
  deriving DecidableEq

def ev : L → P'
  | .a => σ
  | .b => eB
  | .c => eC
  | .d => eD

def ew (w : List L) : P' := (w.map ev).prod

@[simp] lemma ew_nil : ew [] = 1 := rfl
@[simp] lemma ew_cons (x : L) (w : List L) : ew (x :: w) = ev x * ew w := by simp [ew]
@[simp] lemma ew_append (u v : List L) : ew (u ++ v) = ew u * ew v := by simp [ew]

lemma ev_sq (x : L) : ev x * ev x = 1 := by
  cases x <;> ext w <;>
    simp [ev, grigAFun_involutive w, (grigBCD_involutive w).1, (grigBCD_involutive w).2.1,
      (grigBCD_involutive w).2.2]

/-- reducible adjacent pair -/
def red (x y : L) : Prop := (x = .a ∧ y = .a) ∨ (x ≠ .a ∧ y ≠ .a)

def merge : L → L → List L
  | .b, .c => [.d] | .c, .b => [.d]
  | .b, .d => [.c] | .d, .b => [.c]
  | .c, .d => [.b] | .d, .c => [.b]
  | _, _ => []

lemma merge_spec (x y : L) (h : red x y) : ev x * ev y = ew (merge x y) := by
  rcases x with _ | _ | _ | _ <;> rcases y with _ | _ | _ | _ <;> simp [red] at h <;>
    first
    | simpa [merge] using ev_sq _
    | (ext w; simp [merge, ev, bcd_rel w])

lemma merge_length (x y : L) : (merge x y).length ≤ 1 := by
  rcases x with _ | _ | _ | _ <;> rcases y with _ | _ | _ | _ <;> simp [merge]

/-- sign -/
def sg (p : Bool) : P' := if p then σ else 1

def comp : L → Bool × List L × List L
  | .a => (true, [], [])
  | .b => (false, [.a], [.c])
  | .c => (false, [.a], [.d])
  | .d => (false, [], [.b])

lemma comp_spec (x : L) : ev x = pr (ew (comp x).2.1) (ew (comp x).2.2) * sg (comp x).1 := by
  cases x <;> simp [comp, ev, sg, pr_one] <;> first | exact eB_eq | exact eC_eq | exact eD_eq

def dec : List L → Bool × List L × List L
  | [] => (false, [], [])
  | x :: w =>
    let r := dec w
    let q := comp x
    (xor q.1 r.1, q.2.1 ++ (if q.1 then r.2.2 else r.2.1), q.2.2 ++ (if q.1 then r.2.1 else r.2.2))

lemma sg_pr (p : Bool) (u v : P') :
    sg p * pr u v = pr (if p then v else u) (if p then u else v) * sg p := by
  cases p <;> simp [sg, σ_pr]

lemma sg_mul (p q : Bool) : sg p * sg q = sg (xor p q) := by
  cases p <;> cases q <;> simp [sg, σσ]

lemma dec_spec (w : List L) :
    ew w = pr (ew (dec w).2.1) (ew (dec w).2.2) * sg (dec w).1 := by
  induction w with
  | nil => simp [dec, sg, pr_one]
  | cons x w ih =>
    rw [ew_cons, ih, comp_spec x]
    simp only [dec, ew_append]
    rw [mul_assoc, ← mul_assoc (sg _), sg_pr, mul_assoc, sg_mul, ← mul_assoc, pr_mul]
    cases (comp x).1 <;> simp

def na : List L → ℕ
  | [] => 0
  | x :: w => (if x = .a then 1 else 0) + na w
def ny : List L → ℕ
  | [] => 0
  | x :: w => (if x = .a then 0 else 1) + ny w
def nd : List L → ℕ
  | [] => 0
  | x :: w => (if x = .d then 1 else 0) + nd w

lemma len_eq (w : List L) : w.length = na w + ny w := by
  induction w with
  | nil => rfl
  | cons x w ih => simp only [List.length_cons, na, ny, ih]; split_ifs <;> omega

lemma nd_pos (w : List L) (h : L.d ∈ w) : 1 ≤ nd w := by
  induction w with
  | nil => simp at h
  | cons x w ih =>
    simp only [nd]
    rcases List.mem_cons.mp h with h | h
    · subst h; simp
    · have := ih h; omega

lemma comp_len (x : L) : (comp x).2.1.length ≤ (if x = .a then 0 else 1) ∧
    (comp x).2.2.length ≤ (if x = .a then 0 else 1) ∧
    (comp x).2.1.length + (comp x).2.2.length + (if x = .d then 1 else 0) ≤
      2 * (if x = .a then 0 else 1) := by
  cases x <;> simp [comp]

lemma dec_len (w : List L) : (dec w).2.1.length ≤ ny w ∧ (dec w).2.2.length ≤ ny w ∧
    (dec w).2.1.length + (dec w).2.2.length + nd w ≤ 2 * ny w := by
  induction w with
  | nil => simp [dec, ny, nd]
  | cons x w ih =>
    have hc := comp_len x
    simp only [dec, ny, nd, List.length_append]
    cases (comp x).1 <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

lemma dec_mem (w : List L) (z : L) : z ∈ (dec w).2.1 ++ (dec w).2.2 ↔
    ∃ x ∈ w, z ∈ (comp x).2.1 ++ (comp x).2.2 := by
  induction w with
  | nil => simp [dec]
  | cons x w ih =>
    simp only [List.mem_append] at ih
    simp only [dec, List.mem_append, List.mem_cons, exists_eq_or_imp]
    rw [← ih]
    cases (comp x).1 <;> simp only [Bool.false_eq_true, if_false, if_true] <;> tauto

def tt (w : List L) : ℕ := if L.d ∈ w then 0 else if L.c ∈ w then 1 else 2
def μ (w : List L) : ℕ := 4 * w.length + tt w

lemma tt_le (w : List L) : tt w ≤ 2 := by unfold tt; split_ifs <;> omega

def Alt : List L → Prop
  | [] => True
  | [_] => True
  | x :: y :: r => ¬ red x y ∧ Alt (y :: r)

lemma not_Alt (w : List L) (h : ¬ Alt w) : ∃ l x y r, w = l ++ x :: y :: r ∧ red x y := by
  induction w with
  | nil => simp [Alt] at h
  | cons x w ih =>
    rcases w with _ | ⟨y, r⟩
    · simp [Alt] at h
    · simp only [Alt] at h
      by_cases hr : red x y
      · exact ⟨[], x, y, r, rfl, hr⟩
      · obtain ⟨l, x', y', r', he, hred⟩ := ih (by tauto)
        exact ⟨x :: l, x', y', r', by simp [he], hred⟩

lemma Alt_tail {x : L} {r : List L} (h : Alt (x :: r)) : Alt r := by
  rcases r with _ | ⟨y, r⟩
  · trivial
  · exact h.2

lemma Alt_count (r : List L) : ∀ x, Alt (x :: r) →
    (x = .a → ny (x :: r) ≤ na (x :: r)) ∧ ny (x :: r) ≤ na (x :: r) + 1 := by
  induction r with
  | nil => intro x _; cases x <;> simp [na, ny]
  | cons y r ih =>
    intro x h
    obtain ⟨hxy, hr⟩ := h
    have := ih y hr
    simp only [na, ny] at this ⊢
    by_cases hx : x = .a
    · subst hx
      have hy : y ≠ .a := fun hy => hxy (Or.inl ⟨rfl, hy⟩)
      simp only [if_true, hy, if_false] at this ⊢
      omega
    · have hy : y = .a := by by_contra hy; exact hxy (Or.inr ⟨hx, hy⟩)
      subst hy
      simp [hx] at this ⊢
      omega

lemma Alt_YY (n : ℕ) : ∀ w : List L, w.length ≤ n → Alt w → na w < ny w →
    (∃ y, w = [y]) ∨ ∃ y y' m, y ≠ .a ∧ y' ≠ .a ∧ w = y :: (m ++ [y']) := by
  induction n with
  | zero => intro w hw _ h; rcases w with _ | _ <;> simp [na, ny] at h hw ⊢
  | succ n ih =>
    intro w hw halt hlt
    rcases w with _ | ⟨x, r⟩
    · simp [na, ny] at hlt
    by_cases hx : x = .a
    · have := (Alt_count r x halt).1 hx; omega
    rcases r with _ | ⟨y, r'⟩
    · exact Or.inl ⟨x, rfl⟩
    obtain ⟨hxy, hr⟩ := halt
    have hy : y = .a := by by_contra hy; exact hxy (Or.inr ⟨hx, hy⟩)
    subst hy
    have hr' := Alt_tail hr
    have hlt' : na r' < ny r' := by
      simp only [na, ny, hx, if_true, if_false] at hlt; omega
    have hlen : r'.length ≤ n := by simp at hw; omega
    right
    rcases ih r' (by omega) hr' hlt' with ⟨y', rfl⟩ | ⟨y1, y', m, _, hy', rfl⟩
    · exact ⟨x, y', [.a], hx, by
        rintro rfl; simp [na, ny] at hlt', rfl⟩
    · exact ⟨x, y', .a :: y1 :: m, hx, hy', rfl⟩

/-! ### The torsion predicate -/

def Pw (g : P') : Prop := ∃ n : ℕ, g ^ (2 ^ n) = 1

lemma pow_two_pow_mono {g : P'} {n : ℕ} (h : g ^ (2 ^ n) = 1) (k : ℕ) :
    g ^ (2 ^ (n + k)) = 1 := by
  rw [pow_add, pow_mul, h, one_pow]

lemma Pw_pr {u v : P'} (hu : Pw u) (hv : Pw v) : Pw (pr u v) := by
  obtain ⟨n, hn⟩ := hu
  obtain ⟨m, hm⟩ := hv
  refine ⟨n + m, ?_⟩
  rw [pr_pow, pow_two_pow_mono hn, add_comm, pow_two_pow_mono hm, pr_one]

lemma Pw_sq {u v : P'} (hu : Pw (u * v)) (hv : Pw (v * u)) : Pw (pr u v * σ) := by
  have h2 : (pr u v * σ) ^ 2 = pr (u * v) (v * u) := by
    rw [sq, mul_assoc, ← mul_assoc σ, σ_pr, mul_assoc, σσ, mul_one, pr_mul]
  obtain ⟨n, hn⟩ := Pw_pr hu hv
  refine ⟨n + 1, ?_⟩
  rw [pow_succ', pow_mul, h2, hn]

lemma Pw_conj {x g : P'} (hx : x * x = 1) (h : Pw (x * g * x)) : Pw g := by
  obtain ⟨n, hn⟩ := h
  have hxi : x⁻¹ = x := (eq_inv_of_mul_eq_one_left hx).symm
  refine ⟨n, ?_⟩
  have : (x * g * x⁻¹) ^ (2 ^ n) = x * g ^ (2 ^ n) * x⁻¹ := conj_pow
  rw [hxi, hn] at this
  have h2 : g ^ (2 ^ n) = x * (x * g ^ (2 ^ n) * x) * x := by
    simp only [← mul_assoc, hx, one_mul]; rw [mul_assoc, hx, mul_one]
  rw [h2, ← this, mul_one, hx]

lemma μ_append_comm (u v : List L) : μ (u ++ v) = μ (v ++ u) := by
  unfold μ tt
  rw [List.length_append, List.length_append, add_comm u.length]
  congr 1
  simp only [List.mem_append, or_comm]

lemma main (N : ℕ) : ∀ w : List L, μ w < N → Pw (ew w) := by
  induction N with
  | zero => intro w h; omega
  | succ N ih =>
  intro w hw
  have htw := tt_le w
  -- Case B: short words
  by_cases hshort : w.length ≤ 1
  · rcases w with _ | ⟨x, _ | ⟨y, r⟩⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [sq, ev_sq]⟩
    · simp at hshort
  push Not at hshort
  -- Case A: a reducible adjacent pair
  by_cases halt : ¬ Alt w
  · obtain ⟨l, x, y, r, rfl, hred⟩ := not_Alt w halt
    have hlt : μ (l ++ merge x y ++ r) < N := by
      have := merge_length x y
      have := tt_le (l ++ merge x y ++ r)
      unfold μ at hw ⊢; simp only [List.length_append, List.length_cons] at hw ⊢; omega
    have := ih _ hlt
    rw [ew_append, ew_append, ← merge_spec x y hred] at this
    simpa [mul_assoc] using this
  push Not at halt
  -- Case C: both ends are letters of {b, c, d}
  by_cases hcount : na w < ny w
  · rcases Alt_YY w.length w le_rfl halt hcount with ⟨y, rfl⟩ | ⟨y, y', m, hy, hy', rfl⟩
    · simp at hshort
    have hred : red y' y := Or.inr ⟨hy', hy⟩
    refine Pw_conj (x := ev y) (ev_sq y) ?_
    have hlt : μ (m ++ merge y' y) < N := by
      have := merge_length y' y
      have := tt_le (m ++ merge y' y)
      unfold μ at hw ⊢; simp only [List.length_append, List.length_cons] at hw ⊢; omega
    have := ih _ hlt
    rw [ew_append, ← merge_spec y' y hred] at this
    convert this using 1
    simp only [ew_cons, ew_append, ew_nil, mul_one, ← mul_assoc, ev_sq, one_mul]
  push Not at hcount
  -- Case D
  have hlen := len_eq w
  have hna : 1 ≤ na w := by omega
  obtain ⟨h1, h2, h3⟩ := dec_len w
  rw [dec_spec w]
  cases hp : (dec w).1
  · -- g ∈ St(1)
    simp only [sg, Bool.false_eq_true, if_false, mul_one]
    have := tt_le (dec w).2.1
    have := tt_le (dec w).2.2
    unfold μ at hw
    exact Pw_pr (ih _ (by unfold μ; omega)) (ih _ (by unfold μ; omega))
  · simp only [sg, if_true]
    set u := (dec w).2.1
    set v := (dec w).2.2
    have hmem := dec_mem w
    have hlt : μ (u ++ v) < N := by
      have hl : (u ++ v).length + nd w ≤ w.length := by simp; omega
      unfold μ at hw ⊢
      by_cases hd : L.d ∈ w
      · have := nd_pos w hd
        have := tt_le (u ++ v)
        omega
      by_cases hc : L.c ∈ w
      · have hd' : L.d ∈ u ++ v := (hmem .d).2 ⟨.c, hc, by simp [comp]⟩
        have : tt w = 1 := by simp [tt, hd, hc]
        have : tt (u ++ v) = 0 := by simp only [tt, hd', if_true]
        omega
      have hw2 : tt w = 2 := by simp [tt, hd, hc]
      have hd' : L.d ∉ u ++ v := by
        intro h
        obtain ⟨x, hx, hz⟩ := (hmem .d).1 h
        cases x <;> simp [comp] at hz
        exact hc hx
      by_cases hc' : L.c ∈ u ++ v
      · have : tt (u ++ v) = 1 := by simp only [tt, hd', hc', if_true, if_false]
        omega
      have hnil : u ++ v = [] := by
        rcases hne : u ++ v with _ | ⟨z, r⟩
        · rfl
        exfalso
        obtain ⟨x, hx, hz⟩ := (hmem z).1 (by rw [hne]; simp)
        cases x
        · simp [comp] at hz
        · exact hc' ((hmem .c).2 ⟨.b, hx, by simp [comp]⟩)
        · exact hc hx
        · exact hd hx
      rw [hnil]
      simp [tt]
      omega
    have := ih _ hlt
    have := ih _ (by rwa [μ_append_comm] at hlt)
    rw [ew_append] at *
    exact Pw_sq ‹_› ‹_›

lemma ew_reverse (w : List L) : (ew w)⁻¹ = ew w.reverse := by
  induction w with
  | nil => simp
  | cons x w ih =>
    have hx : (ev x)⁻¹ = ev x := (eq_inv_of_mul_eq_one_left (ev_sq x)).symm
    simp [mul_inv_rev, ih, hx]

lemma exists_word (g : BinaryTreeAut) (hg : g ∈ GrigorchukGroup) :
    ∃ w : List L, (g : P') = ew w := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨[.a], by simp [ev, σ]⟩
    · exact ⟨[.b], by simp [ev, eB]⟩
    · exact ⟨[.c], by simp [ev, eC]⟩
    · exact ⟨[.d], by simp [ev, eD]⟩
  | one => exact ⟨[], by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u ++ v, by simp [hu, hv]⟩
  | inv x _ hx =>
    obtain ⟨u, hu⟩ := hx
    exact ⟨u.reverse, by simp [hu, ← ew_reverse]⟩

/-- Proposition 4.7 (p. 14): every element of Γ has order a power of 2. -/
theorem exists_orderOf_eq_two_pow' (g : GrigorchukGroup) : ∃ k : ℕ, orderOf g = 2 ^ k := by
  obtain ⟨w, hw⟩ := exists_word (g : BinaryTreeAut) g.2
  obtain ⟨n, hn⟩ := main (μ w + 1) w (Nat.lt_succ_self _)
  have hg : g ^ (2 ^ n) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [hw, hn]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hg)
  exact ⟨k, hk⟩


end Garrido.GR.Tor

/-!
# Lemma 4.8 of Garrido's notes: `∑_{v ∈ level 3} l(g|_v) ≤ 3/4 l(g) + 8`

Proof strategy (block decomposition).

* Words in the letters `a, b, c, d` (`Ltr`) evaluate to `Γ` (`ev`).  The level-1 section of the
  element represented by a word is represented by an explicit word (`sec1`), computed letter by
  letter (`b = (a, c)`, `c = (a, d)`, `d = (1, b)`); iterating gives level-3 sections (`sec3`).
* Sections are a cocycle: `sec3 (u ++ u') v = sec3 u (act3 u' v) ++ sec3 u' v`, where
  `act3 u'` is a bijection of the 8 level-3 vertices.  Hence if `u` and `u'` have level-3
  sections of total lengths `≤ K` and `≤ K'`, so has `u ++ u'`, with `K + K'`.
* A shortest word for `g` reduces (free product `ℤ/2 * (ℤ/2)²`) to a normal form
  `[a] x₁ a x₂ a … xₘ a [x]`.  Cut `x₁ a … xₘ a` greedily into blocks `xᵢ a … xⱼ a` with
  `4 F(block) ≤ 3 |block|`, where `F` is the total length of the reduced level-3 sections: a
  finite check (`check_nil_eight`, by `decide`) shows every run of 8 pairs has such a prefix.
  Fewer than 8 pairs left over, and the end letters, cost a bounded amount.

The hypothesis `g ∈ St(3)` is not needed.
-/

namespace Garrido.GR.L48

open Garrido

/-! ### Letters and evaluation -/

inductive Ltr | a | b | c | d
  deriving DecidableEq, Repr

inductive NL | b | c | d
  deriving DecidableEq, Repr

def NL.toL : NL → Ltr
  | .b => .b
  | .c => .c
  | .d => .d

/-- The product of two distinct non-`a` letters. -/
def NL.mul : NL → NL → NL
  | .b, .c => .d
  | .c, .b => .d
  | .b, .d => .c
  | .d, .b => .c
  | .c, .d => .b
  | .d, .c => .b
  | x, _ => x

def ltrAut : Ltr → BinaryTreeAut
  | .a => grigA
  | .b => grigB
  | .c => grigC
  | .d => grigD

theorem ltrAut_mem (x : Ltr) : ltrAut x ∈ GrigorchukGroup := by
  apply Subgroup.subset_closure
  cases x <;> simp [ltrAut]

def ltrG (x : Ltr) : GrigorchukGroup := ⟨ltrAut x, ltrAut_mem x⟩

def ev (u : List Ltr) : GrigorchukGroup := (u.map ltrG).prod

/-! ### Relations -/

/-! ### Sections of words -/

/-! ### Reduction to normal form `[a] x₁ a … xₘ a [x]` -/

structure NF where
  lead : Bool
  xs : List NL
  t : Option NL

/-- `x₁ a x₂ a … xₘ a`. -/
def pw : List NL → List Ltr
  | [] => []
  | x :: xs => x.toL :: .a :: pw xs

def tw : Option NL → List Ltr
  | none => []
  | some y => [y.toL]

def nfw (n : NF) : List Ltr := (if n.lead then [.a] else []) ++ (pw n.xs ++ tw n.t)

def pushN (y : NL) : NF → NF
  | ⟨true, xs, t⟩ => ⟨false, y :: xs, t⟩
  | ⟨false, [], none⟩ => ⟨false, [], some y⟩
  | ⟨false, [], some z⟩ => if y = z then ⟨false, [], none⟩ else ⟨false, [], some (y.mul z)⟩
  | ⟨false, z :: zs, t⟩ => if y = z then ⟨true, zs, t⟩ else ⟨false, (y.mul z) :: zs, t⟩

def push : Ltr → NF → NF
  | .a, ⟨l, xs, t⟩ => ⟨!l, xs, t⟩
  | .b, n => pushN .b n
  | .c, n => pushN .c n
  | .d, n => pushN .d n

def nf : List Ltr → NF
  | [] => ⟨false, [], none⟩
  | x :: u => push x (nf u)

/-- Free-product reduction of a word. -/
def red (u : List Ltr) : List Ltr := nfw (nf u)

/-! ### The finite check -/

/-! ### Bounds on the total length of level-3 sections -/

/-! ### Words and word length in `Γ` -/

/-! ### Lemma 4.8 -/


end Garrido.GR.L48

namespace Garrido.GR.Gro

open Chou

section Ball
variable {G : Type*} [Group G] (S : Set G)

end Ball

section Index
variable {G : Type*} [Group G] (S : Set G) (H : Subgroup G)


end Index

section Grig

section Hyp
variable (h_psi : ∀ n : ℕ,
    (∀ g : GrigorchukGroup, g ∈ levelStabilizer n → ∀ v : Fin n → Bool,
        treeSection (g : BinaryTreeAut) (List.ofFn v) ∈ GrigorchukGroup) ∧
      (∀ g h : GrigorchukGroup, g ∈ levelStabilizer n → h ∈ levelStabilizer n →
        ∀ v : Fin n → Bool, treeSection ((g * h : GrigorchukGroup) : BinaryTreeAut) (List.ofFn v) =
          treeSection (g : BinaryTreeAut) (List.ofFn v) * treeSection (h : BinaryTreeAut) (List.ofFn v)) ∧
      ∀ g h : GrigorchukGroup, g ∈ levelStabilizer n → h ∈ levelStabilizer n →
        (∀ v : Fin n → Bool, treeSection (g : BinaryTreeAut) (List.ofFn v) =
          treeSection (h : BinaryTreeAut) (List.ofFn v)) → g = h)

variable (h48 : ∀ (g : GrigorchukGroup) (hg : g ∈ levelStabilizer 3)
    (h : (Fin 3 → Bool) → GrigorchukGroup)
    (hh : ∀ v, (h v : BinaryTreeAut) = treeSection (g : BinaryTreeAut) (List.ofFn v)),
    (∑ v, (wordLength (h v) : ℝ)) ≤ 3 / 4 * (wordLength g : ℝ) + 8)

variable (h_index : (levelStabilizer 3).index = 2 ^ 7)

end Hyp


end Grig

end Garrido.GR.Gro

namespace Garrido.GR.Final

open Garrido


theorem exists_orderOf_eq_two_pow (g : GrigorchukGroup) : ∃ k : ℕ, orderOf g = 2 ^ k :=
  by first | exact Garrido.GR.Tor.exists_orderOf_eq_two_pow' | (intros; apply Garrido.GR.Tor.exists_orderOf_eq_two_pow' <;> assumption)


end Garrido.GR.Final

open Garrido

theorem solution (g : GrigorchukGroup) : ∃ k : ℕ, orderOf g = 2 ^ k :=
  Garrido.GR.Final.exists_orderOf_eq_two_pow g
