-- Prove2me | solution 1 for GTWSched.NPC.evenOdd_polyReducible_td
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T23:10:19.757972+00:00
-- url     : https://prove2.me/submissions/a7d58878-bf25-4d05-b2dc-999b08dcb591

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_GTWSched_NPC_theorem_1_reduction

set_option autoImplicit false

namespace TDEOTD

open CookPvsNP ProjSchedTW.Complexity GTWSched.NPC

/-! ## Binary arithmetic model (LSB first) -/

def bval : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bval l)

def Canon : List Bool → Prop
  | [] => True
  | b :: l => (l = [] → b = true) ∧ Canon l

instance canonDec : (l : List Bool) → Decidable (Canon l)
  | [] => isTrue trivial
  | b :: l => by
    have := canonDec l
    exact (inferInstance : Decidable ((l = [] → b = true) ∧ Canon l))

lemma bval_pos {l : List Bool} (h : Canon l) (hne : l ≠ []) : 0 < bval l := by
  induction l with
  | nil => exact absurd rfl hne
  | cons b t ih =>
    simp only [Canon] at h
    by_cases ht : t = []
    · subst ht; have := h.1 rfl; subst this; simp [bval]
    · have := ih h.2 ht
      simp only [bval]
      cases b <;> simp [Nat.bit] <;> omega

lemma bits_bval {l : List Bool} (h : Canon l) : Nat.bits (bval l) = l := by
  induction l with
  | nil => simp [bval]
  | cons b t ih =>
    simp only [Canon] at h
    simp only [bval]
    rw [Nat.bits_append_bit, ih h.2]
    intro h0
    by_cases ht : t = []
    · exact h.1 ht
    · exact absurd h0 (Nat.pos_iff_ne_zero.mp (bval_pos h.2 ht))

lemma canon_bits_bval (n : ℕ) : Canon (Nat.bits n) ∧ bval (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [Canon, bval]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn]
    refine ⟨⟨fun h => ?_, ih.1⟩, by simp [bval, ih.2]⟩
    have : n = 0 := by
      have h2 := ih.2; rw [h] at h2; simpa [bval] using h2.symm
    exact hn this

/-- one step of the stack adder: inputs absent read as `false`. -/
def addB : List Bool → List Bool → Bool → List Bool
  | [], [], false => []
  | [], [], true => [true]
  | x :: xs, [], c => (x ^^ c) :: addB xs [] (x && c)
  | [], y :: ys, c => (y ^^ c) :: addB [] ys (y && c)
  | x :: xs, y :: ys, c => (x ^^ y ^^ c) :: addB xs ys ((x && y) || (c && (x ^^ y)))

lemma bval_addB (x y : List Bool) (c : Bool) :
    bval (addB x y c) = bval x + bval y + c.toNat := by
  induction x, y, c using addB.induct with
  | case1 => simp [addB, bval]
  | case2 => simp [addB, bval, Nat.bit]
  | case3 x xs c ih =>
    simp only [addB, bval, ih]; cases x <;> cases c <;> simp [Nat.bit] <;> omega
  | case4 y ys c ih =>
    simp only [addB, bval, ih]; cases y <;> cases c <;> simp [Nat.bit] <;> omega
  | case5 x xs y ys c ih =>
    simp only [addB, bval, ih]; cases x <;> cases y <;> cases c <;> simp [Nat.bit] <;> omega

lemma addB_eq_nil {x y : List Bool} {c : Bool} (h : addB x y c = []) :
    x = [] ∧ y = [] ∧ c = false := by
  rcases x with _ | ⟨a, x⟩ <;> rcases y with _ | ⟨b, y⟩ <;> cases c <;> simp_all [addB]

lemma canon_addB (x y : List Bool) (c : Bool) (hx : Canon x) (hy : Canon y) :
    Canon (addB x y c) := by
  induction x, y, c using addB.induct with
  | case1 => simp [addB, Canon]
  | case2 => simp [addB, Canon]
  | case3 x xs c ih =>
    simp only [Canon] at hx
    simp only [addB, Canon]
    refine ⟨fun h => ?_, ih hx.2 hy⟩
    obtain ⟨h1, -, h3⟩ := addB_eq_nil h
    have := hx.1 h1; subst this; simpa using h3
  | case4 y ys c ih =>
    simp only [Canon] at hy
    simp only [addB, Canon]
    refine ⟨fun h => ?_, ih hx hy.2⟩
    obtain ⟨-, h2, h3⟩ := addB_eq_nil h
    have := hy.1 h2; subst this; simpa using h3
  | case5 x xs y ys c ih =>
    simp only [Canon] at hx hy
    simp only [addB, Canon]
    refine ⟨fun h => ?_, ih hx.2 hy.2⟩
    obtain ⟨h1, h2, h3⟩ := addB_eq_nil h
    have := hx.1 h1; have := hy.1 h2; subst_vars; simp at h3

lemma bits_add (a b : ℕ) : Nat.bits (a + b) = addB (Nat.bits a) (Nat.bits b) false := by
  have ha := canon_bits_bval a; have hb := canon_bits_bval b
  have hc := canon_addB _ _ false ha.1 hb.1
  rw [← bits_bval hc, bval_addB, ha.2, hb.2]; simp

lemma bits_div_two (n : ℕ) : Nat.bits (n / 2) = (Nat.bits n).tail := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn _ =>
    rw [Nat.bits_append_bit _ _ hn]
    simp [Nat.bit_div_two]

/-! ## Stacks of the machine -/

inductive Key
  | inp | cur | prev | x1 | S | P | T | K | U | par | seen | lt | bad | lz | Rl | R
  | tmp | car | sc | c1 | c2 | e0 | W | Nb | out
  deriving DecidableEq

instance : Fintype Key where
  elems := {.inp, .cur, .prev, .x1, .S, .P, .T, .K, .U, .par, .seen, .lt, .bad, .lz, .Rl, .R,
    .tmp, .car, .sc, .c1, .c2, .e0, .W, .Nb, .out}
  complete := by intro x; cases x <;> simp

abbrev Store := Key → List BSym

def toB (b : Bool) : BSym := if b then .one else .zero
def enc (x : List Bool) : List BSym := x.map toB

def bitOf : Option BSym → Bool
  | some .one => true
  | _ => false

def isDig : Option BSym → Bool
  | some .one => true
  | some .zero => true
  | _ => false

def carS (c : Bool) : List BSym := if c then [.one] else []

def addAct (src dst : Key) (h : Key → Option BSym) (k : Key) : StackAct BSym :=
  if k = dst then .pop
  else if k = src then (if isDig (h src) then .pop else .keep)
  else if k = .tmp then .push (toB (bitOf (h dst) ^^ bitOf (h src) ^^ (h .car).isSome))
  else if k = .car then
    (if (bitOf (h dst) && bitOf (h src)) || ((h .car).isSome && (bitOf (h dst) ^^ bitOf (h src)))
      then (if (h .car).isSome then .keep else .push .one)
      else (if (h .car).isSome then .pop else .keep))
  else if k = .lz then
    (if isDig (h src) then
      (if bitOf (h src) then (if (h .lz).isSome then .pop else .keep)
        else (if (h .lz).isSome then .keep else .push .one))
     else .keep)
  else .keep

def addTest (src dst : Key) (h : Key → Option BSym) : Bool :=
  isDig (h src) || (h dst).isSome || (h .car).isSome

def addLoop (src dst : Key) : StackProg Key BSym :=
  .loop (addTest src dst) (.act (addAct src dst))

/-- the leading-zero flag after reading digits `y` -/
def lzF : List Bool → List BSym → List BSym
  | [], z => z
  | b :: l, _ => lzF l (if b then [] else [.one])

def addPost (src dst : Key) (x y : List Bool) (c : Bool) (r : List BSym) (s : Store) : Store :=
  fun k => if k = dst then [] else if k = src then r
    else if k = .tmp then (enc (addB x y c)).reverse ++ s .tmp
    else if k = .car then [] else if k = .lz then lzF y (s .lz) else s k

lemma addB_step (x y : List Bool) (c : Bool) (h : ¬ (x = [] ∧ y = [] ∧ c = false)) :
    addB x y c = (x.headD false ^^ y.headD false ^^ c) ::
      addB x.tail y.tail ((x.headD false && y.headD false) ||
        (c && (x.headD false ^^ y.headD false))) := by
  match x, y, c with
  | [], [], false => simp at h
  | [], [], true => simp [addB]
  | x :: xs, [], c => cases x <;> cases c <;> simp [addB]
  | [], y :: ys, c => cases y <;> cases c <;> simp [addB]
  | x :: xs, y :: ys, c => simp [addB]

lemma head_enc_append (x : List Bool) (r : List BSym) (hr : isDig r.head? = false) :
    bitOf (enc x ++ r).head? = x.headD false ∧ isDig (enc x ++ r).head? = !x.isEmpty := by
  cases x with
  | nil =>
    simp only [enc, List.map_nil, List.nil_append, List.headD_nil, List.isEmpty_nil, Bool.not_true]
    refine ⟨?_, hr⟩
    rcases r with _ | ⟨a, r⟩
    · rfl
    · cases a <;> simp_all [bitOf, isDig]
  | cons b x => cases b <;> simp [enc, toB, bitOf, isDig]

lemma car_act (a b c : Bool) :
    StackAct.apply (if (a && b) || (c && (a ^^ b)) then (if c then .keep else .push .one)
      else (if c then .pop else .keep)) (carS c) = carS ((a && b) || (c && (a ^^ b))) := by
  cases a <;> cases b <;> cases c <;> rfl

lemma lz_act (y : List Bool) (r : List BSym) (hr : isDig r.head? = false) (z : List BSym)
    (hz : z = [] ∨ z = [.one]) :
    lzF y z = lzF y.tail (StackAct.apply (if isDig (enc y ++ r).head? then
      (if bitOf (enc y ++ r).head? then (if z.head?.isSome then .pop else .keep)
        else (if z.head?.isSome then .keep else .push .one))
     else .keep) z) ∧
    (StackAct.apply (if isDig (enc y ++ r).head? then
      (if bitOf (enc y ++ r).head? then (if z.head?.isSome then .pop else .keep)
        else (if z.head?.isSome then .keep else .push .one))
     else .keep) z = [] ∨ StackAct.apply (if isDig (enc y ++ r).head? then
      (if bitOf (enc y ++ r).head? then (if z.head?.isSome then .pop else .keep)
        else (if z.head?.isSome then .keep else .push .one))
     else .keep) z = [.one]) := by
  have := head_enc_append y r hr
  rw [this.1, this.2]
  rcases y with _ | ⟨b0, y⟩
  · simp [lzF, StackAct.apply, hz]
  · rcases hz with hz | hz <;> cases b0 <;> subst hz <;> simp [lzF, StackAct.apply]

lemma meas_step (x y : List Bool) (c : Bool) (h0 : ¬ (x = [] ∧ y = [] ∧ c = false)) :
    x.tail.length + y.tail.length +
      ((x.headD false && y.headD false) || (c && (x.headD false ^^ y.headD false))).toNat + 1 ≤
      x.length + y.length + c.toNat := by
  rcases x with _ | ⟨x0, x⟩ <;> rcases y with _ | ⟨y0, y⟩ <;> cases c <;>
    (try cases x0) <;> (try cases y0) <;> simp_all <;> omega

lemma test_step (x y : List Bool) (c : Bool) (h0 : ¬ (x = [] ∧ y = [] ∧ c = false)) :
    ((!y.isEmpty) || (!x.isEmpty) || c) = true := by
  rcases x with _ | ⟨x0, x⟩ <;> rcases y with _ | ⟨y0, y⟩ <;> cases c <;> simp_all

lemma exec_addLoop (src dst : Key) (hsd : src ≠ dst)
    (hs1 : src ≠ .tmp) (hs2 : src ≠ .car) (hs3 : src ≠ .lz)
    (hd1 : dst ≠ .tmp) (hd2 : dst ≠ .car) (hd3 : dst ≠ .lz) (r : List BSym)
    (hr : isDig r.head? = false) :
    ∀ (N : ℕ) (x y : List Bool) (c : Bool) (s : Store),
      x.length + y.length + c.toNat ≤ N →
      s dst = enc x → s src = enc y ++ r → s .car = carS c →
      (s .lz = [] ∨ s .lz = [.one]) →
      ∃ n ≤ 3 * (x.length + y.length + c.toNat) + 1,
        (addLoop src dst).Exec s (addPost src dst x y c r s) n := by
  intro N
  induction N with
  | zero =>
    intro x y c s hN hx hy hc hz
    have hx0 : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy0 : y = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hc0 : c = false := by cases c <;> simp_all
    subst hx0 hy0 hc0
    refine ⟨1, by simp, ?_⟩
    have hpost : addPost src dst [] [] false r s = s := by
      funext k
      simp only [addPost, addB, enc, List.map_nil, List.reverse_nil, List.nil_append, lzF]
      split_ifs with h1 h2 h3 h4 <;> subst_vars <;> simp_all [carS, enc]
    rw [hpost]
    apply StackProg.Exec.loopFalse
    simp [addTest, hx, hy, hc, enc, carS, hr]
  | succ N ih =>
    intro x y c s hN hx hy hc hz
    by_cases h0 : x = [] ∧ y = [] ∧ c = false
    · obtain ⟨rfl, rfl, rfl⟩ := h0
      refine ⟨1, by simp, ?_⟩
      have hpost : addPost src dst [] [] false r s = s := by
        funext k
        simp only [addPost, addB, enc, List.map_nil, List.reverse_nil, List.nil_append, lzF]
        split_ifs with h1 h2 h3 h4 <;> subst_vars <;> simp_all [carS, enc]
      rw [hpost]
      apply StackProg.Exec.loopFalse
      simp [addTest, hx, hy, hc, enc, carS, hr]
    · have hA := head_enc_append x [] (by simp [isDig])
      have hB := head_enc_append y r hr
      simp only [List.append_nil] at hA
      have hhx : bitOf (s dst).head? = x.headD false := by rw [hx]; exact hA.1
      have hdx : ((s dst).head?).isSome = !x.isEmpty := by rw [hx]; cases x <;> simp [enc]
      have hhy : bitOf (s src).head? = y.headD false := by rw [hy]; exact hB.1
      have hdy : isDig (s src).head? = !y.isEmpty := by rw [hy]; exact hB.2
      have hcs : ((s .car).head?).isSome = c := by rw [hc]; cases c <;> simp [carS]
      have hmeas := meas_step x y c h0
      have htest := test_step x y c h0
      generalize ha : x.headD false = a at hhx hmeas
      generalize hb : y.headD false = b at hhy hmeas
      have hstep := addB_step x y c h0
      rw [ha, hb] at hstep
      obtain ⟨s1, hs1def⟩ : ∃ s1, s1 = StackProg.applyAct (addAct src dst) s := ⟨_, rfl⟩
      have e_dst : s1 dst = enc x.tail := by
        rw [hs1def]; simp only [StackProg.applyAct, addAct, if_true]
        rw [hx]; simp [StackAct.apply, enc, List.map_tail]
      have e_src : s1 src = enc y.tail ++ r := by
        rw [hs1def]; simp only [StackProg.applyAct, addAct, if_neg hsd, if_true, hdy]
        rw [hy]; rcases y with _ | ⟨b0, y⟩ <;> simp [StackAct.apply, enc]
      have e_tmp : s1 .tmp = toB (a ^^ b ^^ c) :: s .tmp := by
        rw [hs1def]; simp only [StackProg.applyAct, addAct, if_neg hd1.symm, if_neg hs1.symm,
          if_true, hhx, hhy, hcs]; rfl
      have e_car : s1 .car = carS ((a && b) || (c && (a ^^ b))) := by
        rw [hs1def]; simp only [StackProg.applyAct, addAct, if_neg hd2.symm, if_neg hs2.symm,
          show (Key.car = Key.tmp) = False from by simp, if_false, if_true, hhx, hhy, hcs]
        rw [hc]; exact car_act a b c
      have e_lz : lzF y (s .lz) = lzF y.tail (s1 .lz) ∧ (s1 .lz = [] ∨ s1 .lz = [.one]) := by
        rw [hs1def]; simp only [StackProg.applyAct, addAct, if_neg hd3.symm, if_neg hs3.symm,
          show (Key.lz = Key.tmp) = False from by simp, show (Key.lz = Key.car) = False from by simp,
          if_false, if_true]
        rw [hy]; exact lz_act y r hr (s .lz) hz
      have e_oth : ∀ k, k ≠ dst → k ≠ src → k ≠ .tmp → k ≠ .car → k ≠ .lz → s1 k = s k := by
        intro k h1 h2 h3 h4 h5
        rw [hs1def]; simp [StackProg.applyAct, addAct, h1, h2, h3, h4, h5, StackAct.apply]
      obtain ⟨m, hm, hex⟩ := ih x.tail y.tail ((a && b) || (c && (a ^^ b))) s1 (by omega)
        e_dst e_src e_car e_lz.2
      refine ⟨1 + 1 + 1 + m, by omega, ?_⟩
      have hpost : addPost src dst x.tail y.tail ((a && b) || (c && (a ^^ b))) r s1 =
          addPost src dst x y c r s := by
        funext k
        simp only [addPost]
        by_cases k1 : k = dst
        · simp [k1]
        by_cases k2 : k = src
        · simp [k2, hsd]
        by_cases k3 : k = .tmp
        · subst k3
          simp only [k1, k2, if_false, if_true, e_tmp, hstep]
          simp [enc]
        by_cases k4 : k = .car
        · subst k4; simp [k1, k2]
        by_cases k5 : k = .lz
        · subst k5; simp [k1, k2, e_lz.1]
        simp [k1, k2, k3, k4, k5, e_oth k k1 k2 k3 k4 k5]
      rw [← hpost]
      subst hs1def
      refine StackProg.Exec.loopTrue ?_ (StackProg.Exec.act _ _) hex
      simp only [addTest, hdy, hdx, hcs]; exact htest

/-! ## Generic transfer / copy -/

lemma exec_transfer (src : Key) (targets : Key → Bool) :
    ∀ (l : List BSym) (s : Store), s src = l →
      ∃ n ≤ 3 * l.length + 1, (transferProg src targets).Exec s (transferStore src targets s) n := by
  intro l
  induction l with
  | nil =>
    intro s hs
    refine ⟨1, by simp, ?_⟩
    have : transferStore src targets s = s := by
      funext k; simp only [transferStore]
      split_ifs with h1 h2 <;> simp_all
    rw [this]
    exact StackProg.Exec.loopFalse (by simp [hs])
  | cons a l ih =>
    intro s hs
    obtain ⟨s1, hs1⟩ : ∃ s1, s1 = StackProg.applyAct (transferAct src targets) s := ⟨_, rfl⟩
    have e1 : s1 src = l := by
      rw [hs1]; simp [StackProg.applyAct, transferAct, StackAct.apply, hs]
    obtain ⟨m, hm, hex⟩ := ih s1 e1
    refine ⟨1 + 1 + 1 + m, by simp; omega, ?_⟩
    have hpost : transferStore src targets s1 = transferStore src targets s := by
      funext k; simp only [transferStore]
      by_cases k1 : k = src
      · simp [k1]
      by_cases k2 : targets k = true
      · simp [k1, k2, e1, hs, hs1, StackProg.applyAct, transferAct, StackAct.apply]
      · simp [k1, k2, hs1, StackProg.applyAct, transferAct, StackAct.apply]
    rw [← hpost]; subst hs1
    exact StackProg.Exec.loopTrue (by simp [hs]) (StackProg.Exec.act _ _) hex

lemma exec_copy (src dst scr : Key) (h1 : src ≠ dst) (h2 : src ≠ scr) (h3 : dst ≠ scr)
    (s : Store) (hs : s scr = []) :
    ∃ n ≤ 6 * (s src).length + 3,
      (copyProg src dst scr).Exec s (Function.update s dst (s src ++ s dst)) n := by
  obtain ⟨n1, hn1, e1⟩ := exec_transfer src (fun k => decide (k = scr)) (s src) s rfl
  set s1 := transferStore src (fun k => decide (k = scr)) s with hs1
  have hs1scr : s1 scr = (s src).reverse := by simp [hs1, transferStore, h2.symm, hs]
  obtain ⟨n2, hn2, e2⟩ := exec_transfer scr (fun k => decide (k = src ∨ k = dst)) _ s1 hs1scr
  refine ⟨n1 + 1 + n2, by simp at hn2; omega, ?_⟩
  have : transferStore scr (fun k => decide (k = src ∨ k = dst)) s1 =
      Function.update s dst (s src ++ s dst) := by
    funext k
    by_cases k1 : k = scr
    · subst k1; simp [transferStore, h3.symm, hs]
    by_cases k2 : k = src
    · subst k2; simp [transferStore, hs1, k1, h1, Ne.symm k1, hs]
    by_cases k3 : k = dst
    · subst k3; simp [transferStore, hs1, k1, k2, h2.symm, h3, hs]
    · simp [transferStore, hs1, k1, k2, k3]
  rw [← this]
  exact StackProg.Exec.seq e1 e2

/-! ## Tokens of the input -/

def isDigB : BSym → Bool
  | .one => true
  | .zero => true
  | _ => false

def toBool (a : BSym) : Bool := decide (a = .one)

lemma split_digits (w : List BSym) :
    w = enc ((w.takeWhile isDigB).map toBool) ++ w.dropWhile isDigB ∧
      isDig (w.dropWhile isDigB).head? = false := by
  induction w with
  | nil => simp [enc, isDig]
  | cons a w ih =>
    cases a <;> simp [List.takeWhile, List.dropWhile, isDigB, enc, toB, toBool, isDig] at ih ⊢ <;>
      first | exact ih | exact ih.1 | exact ih.2 | simp_all

lemma enc_append_inj {y y' : List Bool} {r r' : List BSym} (hr : isDig r.head? = false)
    (hr' : isDig r'.head? = false) (h : enc y ++ r = enc y' ++ r') : y = y' ∧ r = r' := by
  induction y generalizing y' with
  | nil =>
    rcases y' with _ | ⟨b, y'⟩
    · simpa using h
    · exfalso; simp [enc] at h; subst h; cases b <;> simp [toB, isDig] at hr
  | cons b y ih =>
    rcases y' with _ | ⟨b', y'⟩
    · exfalso; simp [enc] at h; subst h; cases b <;> simp [toB, isDig] at hr'
    · simp only [enc, List.map_cons, List.cons_append, List.cons.injEq] at h
      have hb : b = b' := by cases b <;> cases b' <;> simp_all [toB]
      obtain ⟨h1, h2⟩ := ih (y' := y') h.2
      exact ⟨by rw [hb, h1], h2⟩

lemma encNat_eq (k : ℕ) : encNat k = enc (Nat.bits k) ++ [BSym.sep] := by
  simp [encNat, enc, toB]

lemma lzF_nil_iff (y : List Bool) : lzF y [] = [] ↔ Canon y := by
  suffices h : ∀ z, (z = [] ∨ z = [.one]) →
      (lzF y z = [] ↔ (y = [] → z = []) ∧ Canon y) by
    simpa using h [] (Or.inl rfl)
  induction y with
  | nil => intro z hz; simp [lzF, Canon]
  | cons b l ih =>
    intro z hz
    rw [lzF, ih _ (by cases b <;> simp)]
    cases b <;> simp [Canon]

lemma lzF_cases (y : List Bool) (z : List BSym) (hz : z = [] ∨ z = [.one]) :
    lzF y z = [] ∨ lzF y z = [.one] := by
  induction y generalizing z with
  | nil => simpa [lzF] using hz
  | cons b l ih => exact ih _ (by cases b <;> simp)

lemma encNats_cons' (k : ℕ) (sl : List ℕ) :
    encNats (k :: sl) = enc (Nat.bits k) ++ (BSym.sep :: encNats sl) := by
  simp [encNats, encNat_eq]

lemma encNats_eq_nil {sl : List ℕ} (h : encNats sl = []) : sl = [] := by
  cases sl with
  | nil => rfl
  | cons k sl => rw [encNats_cons'] at h; simp at h

/-! ## The binary counter -/

lemma len_bits_le (x : ℕ) : (Nat.bits x).length ≤ x := by
  induction x using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn]
    have : n ≠ 0 ∨ b = true := by
      by_cases h : n = 0
      · exact Or.inr (hn h)
      · exact Or.inl h
    cases b <;> simp [Nat.bit] at this ⊢ <;> omega

lemma bits_one : Nat.bits 1 = [true] := by
  have := Nat.bits_append_bit 0 true (by simp)
  simpa using this


/-! ## Generic building blocks -/

lemma length_addB_le (x y : List Bool) (c : Bool) :
    (addB x y c).length ≤ x.length + y.length + 1 := by
  induction x, y, c using addB.induct <;> simp_all [addB] <;> omega

lemma addB_nil_left (y : List Bool) : addB [] y false = y := by
  induction y with
  | nil => simp [addB]
  | cons b y ih => cases b <;> simp [addB, ih]

def pushAt (dst : Key) (a : BSym) : StackProg Key BSym :=
  .act (fun _ k => if k = dst then .push a else .keep)

def skipP : StackProg Key BSym := .act (fun _ _ => .keep)

lemma exec_pushAt (dst : Key) (a : BSym) (s : Store) :
    (pushAt dst a).Exec s (Function.update s dst (a :: s dst)) 1 := by
  have e := StackProg.Exec.act (fun (_ : Key → Option BSym) (k : Key) =>
    if k = dst then StackAct.push a else .keep) s
  have : StackProg.applyAct (fun (_ : Key → Option BSym) (k : Key) =>
      if k = dst then StackAct.push a else .keep) s = Function.update s dst (a :: s dst) := by
    funext k
    by_cases hk : k = dst
    · subst hk; simp [StackProg.applyAct, StackAct.apply]
    · simp [StackProg.applyAct, StackAct.apply, hk]
  rw [this] at e; exact e

lemma exec_skip (s : Store) : skipP.Exec s s 1 := by
  have e := StackProg.Exec.act (fun (_ : Key → Option BSym) (_ : Key) => StackAct.keep (A := BSym)) s
  have : StackProg.applyAct (fun (_ : Key → Option BSym) (_ : Key) => StackAct.keep (A := BSym)) s = s := by
    funext k; simp [StackProg.applyAct, StackAct.apply]
  rw [this] at e; exact e

/-- Add the binary number on `src` into `dst` (both LSB first), consuming `src`. -/
def addTo (src dst : Key) : StackProg Key BSym :=
  .seq (addLoop src dst) (transferProg .tmp (fun k => decide (k = dst)))

lemma exec_addTo (src dst : Key) (h0 : src ≠ dst) (h2 : src ≠ .tmp) (h3 : src ≠ .car)
    (h4 : src ≠ .lz) (d2 : dst ≠ .tmp) (d3 : dst ≠ .car) (d4 : dst ≠ .lz)
    (x y : List Bool) (r : List BSym) (hr : isDig r.head? = false) (s : Store)
    (hdst : s dst = enc x) (hsrc : s src = enc y ++ r) (hcar : s .car = []) (htmp : s .tmp = [])
    (hlz : s .lz = [] ∨ s .lz = [.one]) :
    ∃ n ≤ 6 * (x.length + y.length) + 10, (addTo src dst).Exec s
      (Function.update (Function.update (Function.update s dst (enc (addB x y false))) src r)
        .lz (lzF y (s .lz))) n := by
  obtain ⟨n1, hn1, e1⟩ := exec_addLoop src dst h0 h2 h3 h4 d2 d3 d4
    r hr _ x y false s le_rfl hdst hsrc (by rw [hcar]; rfl) hlz
  set s1 := addPost src dst x y false r s with hs1
  obtain ⟨n2, hn2, e2⟩ := exec_transfer .tmp (fun k => decide (k = dst)) (s1 .tmp) s1 rfl
  have h2' : Key.tmp ≠ src := Ne.symm h2
  have d2' : Key.tmp ≠ dst := Ne.symm d2
  have hfin : transferStore .tmp (fun k => decide (k = dst)) s1 =
      Function.update (Function.update (Function.update s dst (enc (addB x y false))) src r)
        .lz (lzF y (s .lz)) := by
    funext k
    by_cases k1 : k = .lz
    · subst k1; simp [transferStore, hs1, addPost, Ne.symm h4, Ne.symm d4]
    by_cases k2 : k = src
    · rw [k2]; simp [transferStore, hs1, addPost, h0, h2, h4, Function.update_apply]
    by_cases k3 : k = dst
    · rw [k3]; simp [transferStore, hs1, addPost, htmp, Ne.symm h0, d2', d2, d4, h0, h2', Function.update_apply]
    by_cases k4 : k = .tmp
    · subst k4; simp [transferStore, hs1, addPost, htmp, Ne.symm h2, d2']
    by_cases k5 : k = .car
    · subst k5; simp [transferStore, hs1, addPost, hcar, Ne.symm h3, k2, k3]
    · simp [transferStore, hs1, addPost, k1, k2, k3, k4, k5]
  rw [hfin] at e2
  refine ⟨n1 + 1 + n2, ?_, StackProg.Exec.seq e1 e2⟩
  have hl := length_addB_le x y false
  have : (s1 .tmp).length = (addB x y false).length := by
    simp [hs1, addPost, htmp, enc, h2', d2']
  simp only [Bool.toNat_false] at hn1
  omega

/-- Add a copy of `src` into `dst` (through the scratch stacks `c1`, `sc`). -/
def addCopy (src dst : Key) : StackProg Key BSym := .seq (copyProg src .c1 .sc) (addTo .c1 dst)

lemma exec_addCopy (src dst : Key) (h0 : src ≠ dst) (hs1 : src ≠ .c1) (hs2 : src ≠ .sc)
    (h2 : src ≠ .tmp) (h3 : src ≠ .car) (h4 : src ≠ .lz)
    (d0 : dst ≠ .c1) (d1 : dst ≠ .sc) (d2 : dst ≠ .tmp) (d3 : dst ≠ .car) (d4 : dst ≠ .lz)
    (a b : ℕ) (s : Store) (hdst : s dst = enc (Nat.bits a)) (hsrc : s src = enc (Nat.bits b))
    (hc1 : s .c1 = []) (hsc : s .sc = []) (hcar : s .car = []) (htmp : s .tmp = [])
    (hlz : s .lz = []) :
    ∃ n ≤ 12 * ((Nat.bits a).length + (Nat.bits b).length) + 20, (addCopy src dst).Exec s
      (Function.update s dst (enc (Nat.bits (a + b)))) n := by
  obtain ⟨n1, hn1, e1⟩ := exec_copy src .c1 .sc hs1 hs2 (by decide) s hsc
  set s1 := Function.update s .c1 (s src ++ s .c1) with hs1d
  have v1 : ∀ k, k ≠ .c1 → s1 k = s k := fun k hk => by simp [hs1d, hk]
  obtain ⟨n2, hn2, e2⟩ := exec_addTo .c1 dst (Ne.symm d0) (by decide) (by decide) (by decide)
    d2 d3 d4 (Nat.bits a) (Nat.bits b) [] (by rfl) s1 (by rw [v1 _ d0, hdst])
    (by simp [hs1d, hsrc, hc1]) (by rw [v1 _ (by decide), hcar]) (by rw [v1 _ (by decide), htmp])
    (Or.inl (by rw [v1 _ (by decide), hlz]))
  have hfin : Function.update (Function.update (Function.update s1 dst
      (enc (addB (Nat.bits a) (Nat.bits b) false))) .c1 []) .lz (lzF (Nat.bits b) (s1 .lz)) =
      Function.update s dst (enc (Nat.bits (a + b))) := by
    have hl : lzF (Nat.bits b) [] = [] := (lzF_nil_iff _).2 (canon_bits_bval b).1
    rw [← bits_add]
    funext k
    by_cases k1 : k = .lz
    · subst k1; simp [v1, hlz, hl, Ne.symm d4]
    by_cases k2 : k = .c1
    · subst k2; simp [hc1, Ne.symm d0]
    by_cases k3 : k = dst
    · subst k3; simp [k1, k2]
    · simp [k1, k2, k3, v1 k k2]
  rw [hfin] at e2
  refine ⟨n1 + 1 + n2, ?_, StackProg.Exec.seq e1 e2⟩
  simp [hsrc, enc] at hn1
  omega

/-- Append the code of `src`, and a separator, to the reversed output stack `dst`. -/
def emitTo (src dst : Key) : StackProg Key BSym :=
  .seq (copyProg src .W .sc) (.seq (transferProg .W (fun k => decide (k = dst))) (pushAt dst .sep))

lemma exec_emitTo (src dst : Key) (h0 : src ≠ dst) (hs1 : src ≠ .W) (hs2 : src ≠ .sc)
    (d1 : dst ≠ .W) (d2 : dst ≠ .sc) (s : Store) (hW : s .W = []) (hsc : s .sc = []) :
    ∃ n ≤ 9 * (s src).length + 8,
      (emitTo src dst).Exec s (Function.update s dst (.sep :: ((s src).reverse ++ s dst))) n := by
  obtain ⟨n1, hn1, e1⟩ := exec_copy src .W .sc hs1 hs2 (by decide) s hsc
  set s1 := Function.update s .W (s src ++ s .W) with hs1d
  obtain ⟨n2, hn2, e2⟩ := exec_transfer .W (fun k => decide (k = dst)) (s1 .W) s1 rfl
  set s2 := transferStore .W (fun k => decide (k = dst)) s1 with hs2d
  have e3 := exec_pushAt dst .sep s2
  have hfin : Function.update s2 dst (.sep :: s2 dst) =
      Function.update s dst (.sep :: ((s src).reverse ++ s dst)) := by
    funext k
    by_cases k1 : k = dst
    · subst k1; simp [hs2d, hs1d, transferStore, hW, d1]
    by_cases k2 : k = .W
    · subst k2; simp [hs2d, hs1d, transferStore, hW, k1]
    · simp [hs2d, hs1d, transferStore, k1, k2]
  rw [hfin] at e3
  refine ⟨n1 + 1 + (n2 + 1 + 1), ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 e3)⟩
  have : (s1 .W).length = (s src).length := by simp [hs1d, hW]
  omega

/-! ## Comparison of two binary numbers -/

/-- `bcmp xs ys f`: scanning from the least significant bit, the flag records whether `ys` is
larger on the most significant differing bit seen so far. -/
def bcmp : List Bool → List Bool → Bool → Bool
  | [], [], f => f
  | a :: xs, [], f => bcmp xs [] (if a = false then f else false)
  | [], b :: ys, f => bcmp [] ys (if b = false then f else true)
  | a :: xs, b :: ys, f => bcmp xs ys (if a = b then f else b)

lemma bcmp_spec : ∀ (xs ys : List Bool) (f : Bool),
    bcmp xs ys f = true ↔ bval xs < bval ys ∨ (bval xs = bval ys ∧ f = true) := by
  intro xs
  induction xs with
  | nil =>
    intro ys
    induction ys with
    | nil => intro f; simp [bcmp, bval]
    | cons b ys ih =>
      intro f; rw [bcmp, ih]; cases b <;> cases f <;> simp [Nat.bit, bval] <;> omega
  | cons a xs ih =>
    intro ys f
    cases ys with
    | nil => rw [bcmp, ih]; cases a <;> cases f <;> simp [Nat.bit, bval] <;> omega
    | cons b ys => rw [bcmp, ih]; cases a <;> cases b <;> cases f <;> simp [Nat.bit, bval] <;> omega

def fl (b : Bool) : List BSym := if b then [.one] else []

def bcmpAct (a b : Key) (h : Key → Option BSym) (k : Key) : StackAct BSym :=
  if k = a then .pop else if k = b then .pop else if k = .lt then
    (if bitOf (h a) = bitOf (h b) then .keep
     else if bitOf (h b) then (if (h .lt).isSome then .keep else .push .one)
     else (if (h .lt).isSome then .pop else .keep))
  else .keep

def bcmpLoop (a b : Key) : StackProg Key BSym :=
  .loop (fun h => (h a).isSome || (h b).isSome) (.act (bcmpAct a b))

lemma exec_bcmpLoop (a b : Key) (hab : a ≠ b) (ha : a ≠ .lt) (hb : b ≠ .lt) :
    ∀ (N : ℕ) (xs ys : List Bool) (f : Bool) (s : Store), xs.length + ys.length ≤ N →
      s a = enc xs → s b = enc ys → s .lt = fl f →
      ∃ n ≤ 3 * (xs.length + ys.length) + 1, (bcmpLoop a b).Exec s
        (Function.update (Function.update (Function.update s a []) b []) .lt (fl (bcmp xs ys f))) n := by
  intro N
  induction N with
  | zero =>
    intro xs ys f s hN hxs hys hf
    have hx0 : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy0 : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hx0 hy0
    refine ⟨1, by simp, ?_⟩
    have hpost : Function.update (Function.update (Function.update s a []) b []) .lt
        (fl (bcmp [] [] f)) = s := by
      funext k
      by_cases k1 : k = .lt
      · subst k1; simp [bcmp, hf]
      by_cases k2 : k = b
      · subst k2; simp [k1, hys, enc]
      by_cases k3 : k = a
      · subst k3; simp [k1, k2, hxs, enc]
      · simp [k1, k2, k3]
    rw [hpost]
    exact StackProg.Exec.loopFalse (by simp [hxs, hys, enc])
  | succ N ih =>
    intro xs ys f s hN hxs hys hf
    by_cases h0 : xs = [] ∧ ys = []
    · obtain ⟨rfl, rfl⟩ := h0
      refine ⟨1, by simp, ?_⟩
      have hpost : Function.update (Function.update (Function.update s a []) b []) .lt
          (fl (bcmp [] [] f)) = s := by
        funext k
        by_cases k1 : k = .lt
        · subst k1; simp [bcmp, hf]
        by_cases k2 : k = b
        · subst k2; simp [k1, hys, enc]
        by_cases k3 : k = a
        · subst k3; simp [k1, k2, hxs, enc]
        · simp [k1, k2, k3]
      rw [hpost]
      exact StackProg.Exec.loopFalse (by simp [hxs, hys, enc])
    · set s1 := StackProg.applyAct (bcmpAct a b) s with hs1
      have hA := head_enc_append xs [] (by simp [isDig])
      have hB := head_enc_append ys [] (by simp [isDig])
      simp only [List.append_nil] at hA hB
      have hfs : ((s .lt).head?).isSome = f := by rw [hf]; cases f <;> simp [fl]
      set α := xs.headD false
      set β := ys.headD false
      set f' := if α = β then f else β with hf'
      have e_a : s1 a = enc xs.tail := by
        simp [hs1, StackProg.applyAct, bcmpAct, StackAct.apply, hxs, enc, List.map_tail]
      have e_b : s1 b = enc ys.tail := by
        simp [hs1, StackProg.applyAct, bcmpAct, StackAct.apply, hys, enc, List.map_tail, Ne.symm hab]
      have e_lt : s1 .lt = fl f' := by
        simp only [hs1, StackProg.applyAct, bcmpAct, Ne.symm ha, Ne.symm hb, if_false, if_true]
        rw [hxs, hys, hA.1, hB.1, hfs, hf, hf']
        cases hα : α <;> cases hβ : β <;> cases f <;> simp [fl, StackAct.apply]
      have e_oth : ∀ k, k ≠ a → k ≠ b → k ≠ .lt → s1 k = s k := by
        intro k h1 h2 h3
        simp [hs1, StackProg.applyAct, bcmpAct, h1, h2, h3, StackAct.apply]
      obtain ⟨m, hm, hex⟩ := ih xs.tail ys.tail f' s1
        (by rcases xs with _ | ⟨_, xs⟩ <;> rcases ys with _ | ⟨_, ys⟩ <;> simp_all <;> omega)
        e_a e_b e_lt
      have hcmp : bcmp xs.tail ys.tail f' = bcmp xs ys f := by
        rcases xs with _ | ⟨x0, xs⟩ <;> rcases ys with _ | ⟨y0, ys⟩
        · exact absurd ⟨rfl, rfl⟩ h0
        · cases y0 <;> simp [bcmp, hf', α, β]
        · cases x0 <;> simp [bcmp, hf', α, β]
        · simp [bcmp, hf', α, β]
      have hpost : Function.update (Function.update (Function.update s1 a []) b []) .lt
          (fl (bcmp xs.tail ys.tail f')) =
          Function.update (Function.update (Function.update s a []) b []) .lt (fl (bcmp xs ys f)) := by
        rw [hcmp]
        funext k
        by_cases k1 : k = .lt
        · subst k1; simp
        by_cases k2 : k = b
        · subst k2; simp [k1]
        by_cases k3 : k = a
        · subst k3; simp [k1, k2]
        · simp [k1, k2, k3, e_oth k k3 k2 k1]
      rw [hpost] at hex
      refine ⟨1 + 1 + 1 + m, ?_, StackProg.Exec.loopTrue ?_ (StackProg.Exec.act _ _) hex⟩
      · rcases xs with _ | ⟨_, xs⟩ <;> rcases ys with _ | ⟨_, ys⟩ <;> simp_all <;> omega
      · rcases xs with _ | ⟨_, xs⟩ <;> rcases ys with _ | ⟨_, ys⟩ <;> simp_all [enc]

/-! ## Good states of the machine -/

def eb (n : ℕ) : List BSym := enc (Nat.bits n)

lemma eb_zero : eb 0 = [] := by simp [eb, enc]

lemma len_eb (n : ℕ) : (eb n).length = Nat.size n := by
  simp [eb, enc, Nat.size_eq_bits_len]

/-- The numeric registers between two rounds. -/
structure G where
  i : List BSym
  prev : ℕ
  x1 : ℕ
  S : ℕ
  P : ℕ
  T : ℕ
  K : ℕ
  U : ℕ
  par : Bool
  seen : Bool
  Rl : List BSym
  R : List BSym

def Sg (g : G) (cur bad lt lz : List BSym) : Store := fun k =>
  match k with
  | .inp => g.i | .cur => cur | .prev => eb g.prev | .x1 => eb g.x1 | .S => eb g.S
  | .P => eb g.P | .T => eb g.T | .K => eb g.K | .U => List.replicate g.U .one
  | .par => fl g.par | .seen => fl g.seen | .lt => lt | .bad => bad | .lz => lz
  | .Rl => g.Rl | .R => g.R | _ => []

/-- One processed number `v` (the paper's `xᵢ`), as a pure function of the registers. -/
def stepG (g : G) (v : ℕ) : G :=
  let x1' := if g.seen then g.x1 else v
  let Rl1 := if g.seen then g.Rl else .sep :: ((eb v).reverse ++ (.zero :: g.Rl))
  let Rl' := .sep :: ((eb (v + 1)).reverse ++ (.zero :: Rl1))
  let P1 := g.P + (v + 1)
  if g.par then
    ⟨g.i, v, x1', g.S + (v + 1), 0, g.T + P1, g.K + g.T + g.T + P1 + x1' + x1', g.U + 1, false,
      true, Rl', g.R⟩
  else
    ⟨g.i, v, x1', g.S + (v + 1), P1, g.T, g.K, g.U + 1, true, true, Rl', g.R⟩

/-! ## The round program -/

def badT (h : Key → Option BSym) : Bool := (h .bad).isSome

def chkAct (h : Key → Option BSym) (k : Key) : StackAct BSym :=
  if k = .bad then (if isDig (h .inp) then .keep else .push .one) else .keep

def termAct (h : Key → Option BSym) (k : Key) : StackAct BSym :=
  if decide (h .inp = some .sep) && (h .lz).isNone then
    (if k = .inp then .pop else .keep)
  else (if k = .bad then .push .one else .keep)

def ltAct (h : Key → Option BSym) (k : Key) : StackAct BSym :=
  if (h .lt).isSome then (if k = .lt then .pop else .keep)
  else (if k = .bad then .push .one else .keep)

def parAct (h : Key → Option BSym) (k : Key) : StackAct BSym :=
  if k = .par then (if (h .par).isSome then .pop else .push .one) else .keep

def firstP : StackProg Key BSym :=
  .branch (fun h => (h .seen).isSome) skipP
    (.seq (clearProg .x1) (.seq (copyProg .cur .x1 .sc) (.seq (pushAt .Rl .zero)
      (.seq (emitTo .x1 .Rl) (pushAt .seen .one)))))

def incP (dst : Key) : StackProg Key BSym := .seq (pushAt .e0 .one) (addTo .e0 dst)

def pairP : StackProg Key BSym :=
  .seq (addCopy .T .K) (.seq (addCopy .T .K) (.seq (addCopy .P .K) (.seq (addTo .P .T)
    (.seq (addCopy .x1 .K) (addCopy .x1 .K)))))

def rest2 : StackProg Key BSym :=
  .seq (clearProg .prev) (.seq (copyProg .cur .prev .sc) (.seq firstP (.seq (incP .cur)
    (.seq (pushAt .Rl .zero) (.seq (emitTo .cur .Rl) (.seq (addCopy .cur .S) (.seq (addTo .cur .P)
      (.seq (pushAt .U .one) (.seq (.act parAct)
        (.branch (fun h => (h .par).isSome) skipP pairP))))))))))

def rest1 : StackProg Key BSym :=
  .seq (copyProg .cur .c1 .sc) (.seq (copyProg .prev .c2 .sc) (.seq (bcmpLoop .c2 .c1)
    (.seq (.act ltAct) (.branch badT skipP rest2))))

def body : StackProg Key BSym :=
  .seq (.act chkAct) (.seq (addTo .inp .cur) (.seq (.act termAct) (.branch badT skipP rest1)))

def loopTest (h : Key → Option BSym) : Bool := (h .inp).isSome && (h .bad).isNone

def mainLoop : StackProg Key BSym := .loop loopTest body

/-! ## Execution of the pair step and of `rest2` -/

lemma size_mono {a b : ℕ} (h : a ≤ b) : Nat.size a ≤ Nat.size b := Nat.size_le_size h

lemma bits_len_le {a b : ℕ} (h : a ≤ b) : (Nat.bits a).length ≤ Nat.size b := by
  rw [Nat.size_eq_bits_len]; exact Nat.size_le_size h

lemma exec_pairP (g : G) (cur : List BSym) (Z : ℕ)
    (hZ : Nat.size (g.K + g.T + g.T + g.P + g.x1 + g.x1) ≤ Z) :
    ∃ n ≤ 200 * Z + 200, pairP.Exec (Sg g cur [] [] [])
      (Sg { g with P := 0, T := g.T + g.P, K := g.K + g.T + g.T + g.P + g.x1 + g.x1 }
        cur [] [] []) n := by
  have l1 : ∀ a, a ≤ g.K + g.T + g.T + g.P + g.x1 + g.x1 → (Nat.bits a).length ≤ Z :=
    fun a ha => (bits_len_le ha).trans hZ
  obtain ⟨n1, hn1, e1⟩ := exec_addCopy .T .K (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    g.K g.T (Sg g cur [] [] []) rfl rfl rfl rfl rfl rfl rfl
  have p1 : Function.update (Sg g cur [] [] []) .K (enc (Nat.bits (g.K + g.T))) =
      Sg { g with K := g.K + g.T } cur [] [] [] := by funext k; cases k <;> rfl
  rw [p1] at e1
  obtain ⟨n2, hn2, e2⟩ := exec_addCopy .T .K (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (g.K + g.T) g.T (Sg { g with K := g.K + g.T } cur [] [] []) rfl rfl rfl rfl rfl rfl rfl
  have p2 : Function.update (Sg { g with K := g.K + g.T } cur [] [] []) .K
      (enc (Nat.bits (g.K + g.T + g.T))) = Sg { g with K := g.K + g.T + g.T } cur [] [] [] := by
    funext k; cases k <;> rfl
  rw [p2] at e2
  obtain ⟨n3, hn3, e3⟩ := exec_addCopy .P .K (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (g.K + g.T + g.T) g.P (Sg { g with K := g.K + g.T + g.T } cur [] [] []) rfl rfl rfl rfl rfl rfl rfl
  have p3 : Function.update (Sg { g with K := g.K + g.T + g.T } cur [] [] []) .K
      (enc (Nat.bits (g.K + g.T + g.T + g.P))) =
      Sg { g with K := g.K + g.T + g.T + g.P } cur [] [] [] := by
    funext k; cases k <;> rfl
  rw [p3] at e3
  obtain ⟨n4, hn4, e4⟩ := exec_addTo .P .T (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Nat.bits g.T) (Nat.bits g.P) [] (by rfl)
    (Sg { g with K := g.K + g.T + g.T + g.P } cur [] [] []) rfl (by simp [Sg, eb]) rfl rfl
    (Or.inl rfl)
  have p4 : Function.update (Function.update (Function.update
      (Sg { g with K := g.K + g.T + g.T + g.P } cur [] [] []) .T
      (enc (addB (Nat.bits g.T) (Nat.bits g.P) false))) .P []) .lz
      (lzF (Nat.bits g.P) (Sg { g with K := g.K + g.T + g.T + g.P } cur [] [] [] .lz)) =
      Sg { g with K := g.K + g.T + g.T + g.P, T := g.T + g.P, P := 0 } cur [] [] [] := by
    have hl : lzF (Nat.bits g.P) [] = [] := (lzF_nil_iff _).2 (canon_bits_bval _).1
    rw [← bits_add]
    funext k; cases k <;> simp [Sg, hl, eb, enc]
  rw [p4] at e4
  obtain ⟨n5, hn5, e5⟩ := exec_addCopy .x1 .K (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (g.K + g.T + g.T + g.P) g.x1
    (Sg { g with K := g.K + g.T + g.T + g.P, T := g.T + g.P, P := 0 } cur [] [] [])
    rfl rfl rfl rfl rfl rfl rfl
  have p5 : Function.update
      (Sg { g with K := g.K + g.T + g.T + g.P, T := g.T + g.P, P := 0 } cur [] [] []) .K
      (enc (Nat.bits (g.K + g.T + g.T + g.P + g.x1))) =
      Sg { g with K := g.K + g.T + g.T + g.P + g.x1, T := g.T + g.P, P := 0 } cur [] [] [] := by
    funext k; cases k <;> rfl
  rw [p5] at e5
  obtain ⟨n6, hn6, e6⟩ := exec_addCopy .x1 .K (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (g.K + g.T + g.T + g.P + g.x1) g.x1
    (Sg { g with K := g.K + g.T + g.T + g.P + g.x1, T := g.T + g.P, P := 0 } cur [] [] [])
    rfl rfl rfl rfl rfl rfl rfl
  have p6 : Function.update
      (Sg { g with K := g.K + g.T + g.T + g.P + g.x1, T := g.T + g.P, P := 0 } cur [] [] []) .K
      (enc (Nat.bits (g.K + g.T + g.T + g.P + g.x1 + g.x1))) =
      Sg { g with P := 0, T := g.T + g.P, K := g.K + g.T + g.T + g.P + g.x1 + g.x1 }
        cur [] [] [] := by
    funext k; cases k <;> rfl
  rw [p6] at e6
  refine ⟨n1 + 1 + (n2 + 1 + (n3 + 1 + (n4 + 1 + (n5 + 1 + n6)))), ?_,
    StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
      (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 e6))))⟩
  have := l1 g.K (by omega); have := l1 g.T (by omega); have := l1 g.P (by omega)
  have := l1 g.x1 (by omega); have := l1 (g.K + g.T) (by omega)
  have := l1 (g.K + g.T + g.T) (by omega); have := l1 (g.K + g.T + g.T + g.P) (by omega)
  have := l1 (g.K + g.T + g.T + g.P + g.x1) (by omega)
  omega

lemma exec_clear (src : Key) (s : Store) :
    ∃ n ≤ 3 * (s src).length + 1, (clearProg src).Exec s (Function.update s src []) n := by
  obtain ⟨n, hn, e⟩ := exec_transfer src (fun _ => false) (s src) s rfl
  have : transferStore src (fun _ => false) s = Function.update s src [] := by
    funext k; by_cases hk : k = src
    · subst hk; simp [transferStore]
    · simp [transferStore, hk]
  rw [this] at e; exact ⟨n, hn, e⟩

lemma exec_firstP (g : G) (v : ℕ) (Z : ℕ) (hx : Nat.size g.x1 ≤ Z) (hv : Nat.size v ≤ Z) :
    ∃ n ≤ 30 * Z + 30, firstP.Exec (Sg g (eb v) [] [] [])
      (Sg { g with x1 := (if g.seen then g.x1 else v), Rl := (if g.seen then g.Rl else .sep :: ((eb v).reverse ++ (.zero :: g.Rl))), seen := true } (eb v) [] [] []) n := by
  cases hs : g.seen
  · -- first number
    obtain ⟨n1, hn1, e1⟩ := exec_clear .x1 (Sg g (eb v) [] [] [])
    have p1 : Function.update (Sg g (eb v) [] [] []) .x1 [] = Sg { g with x1 := 0 } (eb v) [] [] [] := by
      funext k; cases k <;> simp [Sg, eb_zero]
    rw [p1] at e1
    obtain ⟨n2, hn2, e2⟩ := exec_copy .cur .x1 .sc (by decide) (by decide) (by decide)
      (Sg { g with x1 := 0 } (eb v) [] [] []) rfl
    have p2 : Function.update (Sg { g with x1 := 0 } (eb v) [] [] []) .x1
        ((Sg { g with x1 := 0 } (eb v) [] [] []) .cur ++ (Sg { g with x1 := 0 } (eb v) [] [] []) .x1) =
        Sg { g with x1 := v } (eb v) [] [] [] := by
      funext k; cases k <;> simp [Sg, eb_zero]
    rw [p2] at e2
    have e3 := exec_pushAt .Rl .zero (Sg { g with x1 := v } (eb v) [] [] [])
    have p3 : Function.update (Sg { g with x1 := v } (eb v) [] [] []) .Rl
        (.zero :: (Sg { g with x1 := v } (eb v) [] [] []) .Rl) =
        Sg { g with x1 := v, Rl := .zero :: g.Rl } (eb v) [] [] [] := by
      funext k; cases k <;> rfl
    rw [p3] at e3
    obtain ⟨n4, hn4, e4⟩ := exec_emitTo .x1 .Rl (by decide) (by decide) (by decide) (by decide)
      (by decide) (Sg { g with x1 := v, Rl := .zero :: g.Rl } (eb v) [] [] []) rfl rfl
    have p4 : Function.update (Sg { g with x1 := v, Rl := .zero :: g.Rl } (eb v) [] [] []) .Rl
        (.sep :: (((Sg { g with x1 := v, Rl := .zero :: g.Rl } (eb v) [] [] []) .x1).reverse ++
          (Sg { g with x1 := v, Rl := .zero :: g.Rl } (eb v) [] [] []) .Rl)) =
        Sg { g with x1 := v, Rl := .sep :: ((eb v).reverse ++ (.zero :: g.Rl)) } (eb v) [] [] [] := by
      funext k; cases k <;> rfl
    rw [p4] at e4
    have e5 := exec_pushAt .seen .one
      (Sg { g with x1 := v, Rl := .sep :: ((eb v).reverse ++ (.zero :: g.Rl)) } (eb v) [] [] [])
    have p5 : Function.update
        (Sg { g with x1 := v, Rl := .sep :: ((eb v).reverse ++ (.zero :: g.Rl)) } (eb v) [] [] []) .seen
        (.one :: (Sg { g with x1 := v, Rl := .sep :: ((eb v).reverse ++ (.zero :: g.Rl)) }
          (eb v) [] [] []) .seen) =
        Sg { g with x1 := (if false = true then g.x1 else v), Rl := (if false = true then g.Rl else .sep :: ((eb v).reverse ++ (.zero :: g.Rl))), seen := true } (eb v) [] [] [] := by
      funext k; cases k <;> simp [Sg, fl, hs]
    rw [p5] at e5
    refine ⟨1 + (n1 + 1 + (n2 + 1 + (1 + 1 + (n4 + 1 + 1)))), ?_,
      StackProg.Exec.branchFalse (by simp [Sg, fl, hs]) (StackProg.Exec.seq e1
        (StackProg.Exec.seq e2 (StackProg.Exec.seq e3 (StackProg.Exec.seq e4 e5))))⟩
    simp only [Sg, len_eb] at hn1 hn2 hn4
    omega
  · refine ⟨1 + 1, by omega, StackProg.Exec.branchTrue (by simp [Sg, fl, hs]) ?_⟩
    have : Sg { g with x1 := (if true = true then g.x1 else v), Rl := (if true = true then g.Rl else .sep :: ((eb v).reverse ++ (.zero :: g.Rl))), seen := true } (eb v) [] [] [] = Sg g (eb v) [] [] [] := by
      funext k; cases k <;> simp [Sg, fl, hs]
    rw [this]; exact exec_skip _

def gA (g : G) (v : ℕ) : G := { g with prev := v, x1 := (if g.seen then g.x1 else v), Rl := (if g.seen then g.Rl else .sep :: ((eb v).reverse ++ (.zero :: g.Rl))), seen := true }

def gB (g : G) (v : ℕ) : G := { gA g v with S := g.S + (v + 1), P := g.P + (v + 1), U := g.U + 1, par := !g.par, Rl := .sep :: ((eb (v + 1)).reverse ++ (.zero :: (gA g v).Rl)) }

lemma exec_rest2 (g : G) (v V : ℕ) (hp : g.prev ≤ V) (hx : g.x1 ≤ V) (hS : g.S ≤ V) (hP : g.P ≤ V)
    (hT : g.T ≤ V) (hK : g.K ≤ V) (hv : v ≤ V) :
    ∃ n ≤ 400 * Nat.size (8 * V + 8) + 500,
      rest2.Exec (Sg g (eb v) [] [] []) (Sg (stepG g v) [] [] [] []) n := by
  set Z := Nat.size (8 * V + 8) with hZ
  have l1 : ∀ a, a ≤ 8 * V + 8 → (Nat.bits a).length ≤ Z := fun a ha => bits_len_le ha
  have l2 : ∀ a, a ≤ 8 * V + 8 → Nat.size a ≤ Z := fun a ha => size_mono ha
  -- clear prev
  obtain ⟨n1, hn1, e1⟩ := exec_clear .prev (Sg g (eb v) [] [] [])
  have p1 : Function.update (Sg g (eb v) [] [] []) .prev [] = Sg { g with prev := 0 } (eb v) [] [] [] := by
    funext k; cases k <;> simp [Sg, eb_zero]
  rw [p1] at e1
  -- prev := v
  obtain ⟨n2, hn2, e2⟩ := exec_copy .cur .prev .sc (by decide) (by decide) (by decide)
    (Sg { g with prev := 0 } (eb v) [] [] []) rfl
  have p2 : Function.update (Sg { g with prev := 0 } (eb v) [] [] []) .prev ((Sg { g with prev := 0 } (eb v) [] [] []) .cur ++ (Sg { g with prev := 0 } (eb v) [] [] []) .prev) = Sg { g with prev := v } (eb v) [] [] [] := by
    funext k; cases k <;> simp [Sg, eb_zero]
  rw [p2] at e2
  -- first number
  obtain ⟨n3, hn3, e3⟩ := exec_firstP { g with prev := v } v Z (l2 g.x1 (by omega)) (l2 v (by omega))
  have p3 : ({ { g with prev := v } with x1 := (if ({ g with prev := v } : G).seen then ({ g with prev := v } : G).x1 else v), Rl := (if ({ g with prev := v } : G).seen then ({ g with prev := v } : G).Rl else .sep :: ((eb v).reverse ++ (.zero :: ({ g with prev := v } : G).Rl))), seen := true } : G) = gA g v := rfl
  rw [p3] at e3
  -- increment cur
  have e4a := exec_pushAt .e0 .one (Sg (gA g v) (eb v) [] [] [])
  obtain ⟨n4, hn4, e4b⟩ := exec_addTo .e0 .cur (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Nat.bits v) [true] [] (by rfl)
    (Function.update (Sg (gA g v) (eb v) [] [] []) .e0 (.one :: (Sg (gA g v) (eb v) [] [] []) .e0))
    (by simp [Sg, eb]) (by simp [Sg, enc, toB]) (by simp [Sg]) (by simp [Sg]) (by simp [Sg])
  have p4 : Function.update (Function.update (Function.update (Function.update (Sg (gA g v) (eb v) [] [] []) .e0 (.one :: (Sg (gA g v) (eb v) [] [] []) .e0)) .cur (enc (addB (Nat.bits v) [true] false))) .e0 []) .lz (lzF [true] ((Function.update (Sg (gA g v) (eb v) [] [] []) .e0 (.one :: (Sg (gA g v) (eb v) [] [] []) .e0)) .lz)) = Sg (gA g v) (eb (v + 1)) [] [] [] := by
    have : addB (Nat.bits v) [true] false = Nat.bits (v + 1) := by rw [bits_add, bits_one]
    rw [this]
    funext k; cases k <;> simp [Sg, lzF, eb]
  rw [p4] at e4b
  have e4 : (incP .cur).Exec (Sg (gA g v) (eb v) [] [] []) (Sg (gA g v) (eb (v + 1)) [] [] []) (1 + 1 + n4) :=
    StackProg.Exec.seq e4a e4b
  -- emit 2(v+1) into Rl
  have e5 := exec_pushAt .Rl .zero (Sg (gA g v) (eb (v + 1)) [] [] [])
  have p5 : Function.update (Sg (gA g v) (eb (v + 1)) [] [] []) .Rl (.zero :: (Sg (gA g v) (eb (v + 1)) [] [] []) .Rl) = Sg { gA g v with Rl := .zero :: (gA g v).Rl } (eb (v + 1)) [] [] [] := by
    funext k; cases k <;> rfl
  rw [p5] at e5
  obtain ⟨n6, hn6, e6⟩ := exec_emitTo .cur .Rl (by decide) (by decide) (by decide) (by decide)
    (by decide) (Sg { gA g v with Rl := .zero :: (gA g v).Rl } (eb (v + 1)) [] [] []) rfl rfl
  have p6 : Function.update (Sg { gA g v with Rl := .zero :: (gA g v).Rl } (eb (v + 1)) [] [] []) .Rl (.sep :: (((Sg { gA g v with Rl := .zero :: (gA g v).Rl } (eb (v + 1)) [] [] []) .cur).reverse ++ (Sg { gA g v with Rl := .zero :: (gA g v).Rl } (eb (v + 1)) [] [] []) .Rl)) = Sg { gA g v with Rl := .sep :: ((eb (v + 1)).reverse ++ (.zero :: (gA g v).Rl)) } (eb (v + 1)) [] [] [] := by
    funext k; cases k <;> rfl
  rw [p6] at e6
  -- S += v + 1
  obtain ⟨n7, hn7, e7⟩ := exec_addCopy .cur .S (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    g.S (v + 1) (Sg { gA g v with Rl := .sep :: ((eb (v + 1)).reverse ++ (.zero :: (gA g v).Rl)) } (eb (v + 1)) [] [] []) rfl rfl rfl rfl rfl rfl rfl
  have p7 : Function.update (Sg { gA g v with Rl := .sep :: ((eb (v + 1)).reverse ++ (.zero :: (gA g v).Rl)) } (eb (v + 1)) [] [] []) .S (enc (Nat.bits (g.S + (v + 1)))) = Sg { gA g v with Rl := .sep :: ((eb (v + 1)).reverse ++ (.zero :: (gA g v).Rl)), S := g.S + (v + 1) } (eb (v + 1)) [] [] [] := by
    funext k; cases k <;> rfl
  rw [p7] at e7
  -- P += v + 1, consuming cur
  obtain ⟨n8, hn8, e8⟩ := exec_addTo .cur .P (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Nat.bits g.P) (Nat.bits (v + 1)) [] (by rfl)
    (Sg { gA g v with Rl := .sep :: ((eb (v + 1)).reverse ++ (.zero :: (gA g v).Rl)), S := g.S + (v + 1) } (eb (v + 1)) [] [] []) rfl (by simp [Sg, eb]) rfl rfl (Or.inl rfl)
  have p8 : Function.update (Function.update (Function.update (Sg { gA g v with Rl := .sep :: ((eb (v + 1)).reverse ++ (.zero :: (gA g v).Rl)), S := g.S + (v + 1) } (eb (v + 1)) [] [] []) .P (enc (addB (Nat.bits g.P) (Nat.bits (v + 1)) false))) .cur []) .lz (lzF (Nat.bits (v + 1)) ((Sg { gA g v with Rl := .sep :: ((eb (v + 1)).reverse ++ (.zero :: (gA g v).Rl)), S := g.S + (v + 1) } (eb (v + 1)) [] [] []) .lz)) = Sg { gA g v with Rl := .sep :: ((eb (v + 1)).reverse ++ (.zero :: (gA g v).Rl)), S := g.S + (v + 1), P := g.P + (v + 1) } [] [] [] [] := by
    have hl : lzF (Nat.bits (v + 1)) [] = [] := (lzF_nil_iff _).2 (canon_bits_bval _).1
    rw [← bits_add]
    funext k; cases k <;> simp [Sg, hl, eb]
  rw [p8] at e8
  -- U += 1
  have e9 := exec_pushAt .U .one (Sg { gA g v with Rl := .sep :: ((eb (v + 1)).reverse ++ (.zero :: (gA g v).Rl)), S := g.S + (v + 1), P := g.P + (v + 1) } [] [] [] [])
  have p9 : Function.update (Sg { gA g v with Rl := .sep :: ((eb (v + 1)).reverse ++ (.zero :: (gA g v).Rl)), S := g.S + (v + 1), P := g.P + (v + 1) } [] [] [] []) .U (.one :: (Sg { gA g v with Rl := .sep :: ((eb (v + 1)).reverse ++ (.zero :: (gA g v).Rl)), S := g.S + (v + 1), P := g.P + (v + 1) } [] [] [] []) .U) = Sg { gA g v with Rl := .sep :: ((eb (v + 1)).reverse ++ (.zero :: (gA g v).Rl)), S := g.S + (v + 1), P := g.P + (v + 1), U := g.U + 1 } [] [] [] [] := by
    funext k; cases k <;> simp [Sg, gA, List.replicate_succ]
  rw [p9] at e9
  -- toggle the parity
  have e10 := StackProg.Exec.act parAct (Sg { gA g v with Rl := .sep :: ((eb (v + 1)).reverse ++ (.zero :: (gA g v).Rl)), S := g.S + (v + 1), P := g.P + (v + 1), U := g.U + 1 } [] [] [] [])
  have p10 : StackProg.applyAct parAct (Sg { gA g v with Rl := .sep :: ((eb (v + 1)).reverse ++ (.zero :: (gA g v).Rl)), S := g.S + (v + 1), P := g.P + (v + 1), U := g.U + 1 } [] [] [] []) = Sg (gB g v) [] [] [] [] := by
    funext k; cases k <;> cases hpar : g.par <;> simp [StackProg.applyAct, parAct, Sg, gB, gA, fl, StackAct.apply, hpar]
  rw [p10] at e10
  -- the pair step
  have hbnd : n1 + 1 + (n2 + 1 + (n3 + 1 + ((1 + 1 + n4) + 1 + (1 + 1 + (n6 + 1 + (n7 + 1 + (n8 + 1 + (1 + 1 + 1))))))))
      ≤ 200 * Z + 290 := by
    simp only [Sg, len_eb] at hn1 hn2 hn6
    have := l2 g.prev (by omega); have := l2 v (by omega); have := l2 (v + 1) (by omega)
    have := l1 g.S (by omega); have := l1 g.P (by omega); have := l1 (v + 1) (by omega)
    have := l1 v (by omega)
    simp only [List.length_cons, List.length_nil] at hn4
    omega
  cases hpar : g.par
  · -- the pair is not complete: skip
    have hfin : gB g v = stepG g v := by
      simp only [gB, gA, stepG, hpar]; rfl
    have e11 : (StackProg.branch (fun h => (h .par).isSome) skipP pairP).Exec (Sg (gB g v) [] [] [] []) (Sg (stepG g v) [] [] [] []) (1 + 1) := by
      rw [← hfin]; exact StackProg.Exec.branchTrue (by simp [Sg, gB, fl, hpar]) (exec_skip _)
    refine ⟨_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
      (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
        (StackProg.Exec.seq e8 (StackProg.Exec.seq e9 (StackProg.Exec.seq e10 e11)))))))))⟩
    omega
  · obtain ⟨n11, hn11, e11⟩ := exec_pairP (gB g v) [] Z (l2 _ (by simp [gB, gA]; split_ifs <;> omega))
    have e11' : (StackProg.branch (fun h => (h .par).isSome) skipP pairP).Exec (Sg (gB g v) [] [] [] []) _ (1 + n11) :=
      StackProg.Exec.branchFalse (by simp [Sg, gB, fl, hpar]) e11
    have hfin : ({ gB g v with P := 0, T := (gB g v).T + (gB g v).P, K := (gB g v).K + (gB g v).T + (gB g v).T + (gB g v).P + (gB g v).x1 + (gB g v).x1 } : G) = stepG g v := by
      simp only [gB, gA, stepG, hpar]; rfl
    rw [hfin] at e11'
    refine ⟨_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
      (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
        (StackProg.Exec.seq e8 (StackProg.Exec.seq e9 (StackProg.Exec.seq e10 e11')))))))))⟩
    omega

lemma exec_rest1 (g : G) (v V : ℕ) (hp : g.prev ≤ V) (hx : g.x1 ≤ V) (hS : g.S ≤ V) (hP : g.P ≤ V)
    (hT : g.T ≤ V) (hK : g.K ≤ V) (hv : v ≤ V) :
    ∃ n ≤ 500 * Nat.size (8 * V + 8) + 600,
      rest1.Exec (Sg g (eb v) [] [] [])
        (if g.prev < v then Sg (stepG g v) [] [] [] [] else Sg g (eb v) [.one] [] []) n := by
  set Z := Nat.size (8 * V + 8) with hZ
  have l2 : ∀ a, a ≤ 8 * V + 8 → Nat.size a ≤ Z := fun a ha => size_mono ha
  obtain ⟨n1, hn1, e1⟩ := exec_copy .cur .c1 .sc (by decide) (by decide) (by decide)
    (Sg g (eb v) [] [] []) rfl
  have p1 : Function.update (Sg g (eb v) [] [] []) .c1 ((Sg g (eb v) [] [] []) .cur ++ (Sg g (eb v) [] [] []) .c1) = Function.update (Sg g (eb v) [] [] []) .c1 (eb v) := by
    simp [Sg]
  rw [p1] at e1
  obtain ⟨n2, hn2, e2⟩ := exec_copy .prev .c2 .sc (by decide) (by decide) (by decide)
    (Function.update (Sg g (eb v) [] [] []) .c1 (eb v)) rfl
  have p2 : Function.update (Function.update (Sg g (eb v) [] [] []) .c1 (eb v)) .c2 ((Function.update (Sg g (eb v) [] [] []) .c1 (eb v)) .prev ++ (Function.update (Sg g (eb v) [] [] []) .c1 (eb v)) .c2) = Function.update (Function.update (Sg g (eb v) [] [] []) .c1 (eb v)) .c2 (eb g.prev) := by
    simp [Sg]
  rw [p2] at e2
  obtain ⟨n3, hn3, e3⟩ := exec_bcmpLoop .c2 .c1 (by decide) (by decide) (by decide) _
    (Nat.bits g.prev) (Nat.bits v) false
    (Function.update (Function.update (Sg g (eb v) [] [] []) .c1 (eb v)) .c2 (eb g.prev)) le_rfl
    (by simp [eb]) (by simp [eb]) (by simp [Sg, fl])
  have hb : bcmp (Nat.bits g.prev) (Nat.bits v) false = decide (g.prev < v) := by
    have := bcmp_spec (Nat.bits g.prev) (Nat.bits v) false
    rw [(canon_bits_bval _).2, (canon_bits_bval _).2] at this
    by_cases h : g.prev < v
    · simp [h, this]
    · simp only [h, decide_false]; simpa [h] using this
  have p3 : Function.update (Function.update (Function.update (Function.update (Function.update (Sg g (eb v) [] [] []) .c1 (eb v)) .c2 (eb g.prev)) .c2 []) .c1 []) .lt (fl (bcmp (Nat.bits g.prev) (Nat.bits v) false)) = Sg g (eb v) [] (fl (decide (g.prev < v))) [] := by
    rw [hb]; funext k; cases k <;> simp [Sg]
  rw [p3] at e3
  have e4 := StackProg.Exec.act ltAct (Sg g (eb v) [] (fl (decide (g.prev < v))) [])
  have hbnd : n1 + 1 + (n2 + 1 + (n3 + 1 + 1)) ≤ 30 * Z + 30 := by
    simp only [Sg, len_eb, Function.update_apply] at hn1 hn2
    simp [len_eb] at hn1 hn2
    rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len] at hn3
    have := l2 g.prev (by omega); have := l2 v (by omega)
    omega
  by_cases hlt : g.prev < v
  · have p4 : StackProg.applyAct ltAct (Sg g (eb v) [] (fl (decide (g.prev < v))) []) = Sg g (eb v) [] [] [] := by
      funext k; cases k <;> simp [StackProg.applyAct, ltAct, Sg, fl, hlt, StackAct.apply]
    rw [p4] at e4
    obtain ⟨n5, hn5, e5⟩ := exec_rest2 g v V hp hx hS hP hT hK hv
    rw [if_pos hlt]
    refine ⟨_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
      (StackProg.Exec.seq e4 (StackProg.Exec.branchFalse (by simp [badT, Sg]) e5))))⟩
    omega
  · have p4 : StackProg.applyAct ltAct (Sg g (eb v) [] (fl (decide (g.prev < v))) []) = Sg g (eb v) [.one] [] [] := by
      funext k; cases k <;> simp [StackProg.applyAct, ltAct, Sg, fl, hlt, StackAct.apply]
    rw [p4] at e4
    rw [if_neg hlt]
    refine ⟨_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
      (StackProg.Exec.seq e4 (StackProg.Exec.branchTrue (by simp [badT, Sg]) (exec_skip _)))))⟩
    omega

lemma exec_body (g : G) (y : List Bool) (r : List BSym) (hr : isDig r.head? = false) (V : ℕ)
    (hp : g.prev ≤ V) (hx : g.x1 ≤ V) (hS : g.S ≤ V) (hP : g.P ≤ V)
    (hT : g.T ≤ V) (hK : g.K ≤ V) (hv : bval y ≤ V) :
    ∃ t, ∃ n ≤ 500 * Nat.size (8 * V + 8) + 6 * y.length + 700,
      body.Exec (Sg { g with i := enc y ++ r } [] [] [] []) t n ∧
      ((r.head? = some .sep ∧ Canon y ∧ y ≠ [] ∧ g.prev < bval y) →
        t = Sg (stepG { g with i := r.tail } (bval y)) [] [] [] []) ∧
      (¬ (r.head? = some .sep ∧ Canon y ∧ y ≠ [] ∧ g.prev < bval y) →
        ∃ g' cur b lt lz, b ≠ [] ∧ t = Sg g' cur b lt lz) := by
  set b1 : List BSym := if y = [] then [.one] else [] with hb1
  have e0 := StackProg.Exec.act chkAct (Sg { g with i := enc y ++ r } [] [] [] [])
  have p0 : StackProg.applyAct chkAct (Sg { g with i := enc y ++ r } [] [] [] []) =
      Sg { g with i := enc y ++ r } [] b1 [] [] := by
    funext k
    rcases y with _ | ⟨b, y⟩
    · cases k <;> simp [StackProg.applyAct, chkAct, Sg, StackAct.apply, hb1, enc, hr]
    · cases k <;> cases b <;> simp [StackProg.applyAct, chkAct, Sg, StackAct.apply, hb1, enc, toB, isDig]
  rw [p0] at e0
  obtain ⟨n1, hn1, e1⟩ := exec_addTo .inp .cur (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) [] y r hr (Sg { g with i := enc y ++ r } [] b1 [] [])
    (by simp [Sg, enc]) rfl rfl rfl (Or.inl rfl)
  have p1 : Function.update (Function.update (Function.update (Sg { g with i := enc y ++ r } [] b1 [] []) .cur (enc (addB [] y false))) .inp r) .lz (lzF y ((Sg { g with i := enc y ++ r } [] b1 [] []) .lz)) = Sg { g with i := r } (enc y) b1 [] (lzF y []) := by
    rw [addB_nil_left]; funext k; cases k <;> simp [Sg]
  rw [p1] at e1
  have e2 := StackProg.Exec.act termAct (Sg { g with i := r } (enc y) b1 [] (lzF y []))
  set ok : Prop := r.head? = some .sep ∧ Canon y with hok
  set b3 : List BSym := if ok then b1 else .one :: b1 with hb3
  set r3 : List BSym := if ok then r.tail else r with hr3
  have p2 : StackProg.applyAct termAct (Sg { g with i := r } (enc y) b1 [] (lzF y [])) =
      Sg { g with i := r3 } (enc y) b3 [] (lzF y []) := by
    have hiff := lzF_nil_iff y
    by_cases hc : ok
    · have hl : lzF y [] = [] := hiff.2 hc.2
      have hr' : r3 = r.tail := by simp [hr3, hc]
      have hb' : b3 = b1 := by simp [hb3, hc]
      rw [hr', hb']
      funext k; cases k <;> simp [StackProg.applyAct, termAct, Sg, hc.1, hl, StackAct.apply]
    · have hr' : r3 = r := by simp [hr3, hc]
      have hb' : b3 = .one :: b1 := by simp [hb3, hc]
      rw [hr', hb']
      have hc' : ¬(decide (r.head? = some BSym.sep) = true ∧ lzF y [] = []) :=
        fun h => hc ⟨by simpa using h.1, hiff.1 h.2⟩
      funext k; cases k <;> simp [StackProg.applyAct, termAct, Sg, StackAct.apply] <;>
        split_ifs with h <;> first | rfl | exact absurd h hc'
  rw [p2] at e2
  by_cases hgood : ok ∧ y ≠ []
  · have hy : Nat.bits (bval y) = y := bits_bval hgood.1.2
    have hb3e : b3 = [] := by simp [hb3, hgood.1, hb1, hgood.2]
    have hr3e : r3 = r.tail := by simp [hr3, hgood.1]
    have hl : lzF y [] = [] := (lzF_nil_iff y).2 hgood.1.2
    have hst : Sg { g with i := r3 } (enc y) b3 [] (lzF y []) = Sg { g with i := r.tail } (eb (bval y)) [] [] [] := by
      rw [hb3e, hr3e, hl, eb, hy]
    rw [hst] at e2
    obtain ⟨n3, hn3, e3⟩ := exec_rest1 { g with i := r.tail } (bval y) V hp hx hS hP hT hK hv
    have e3' := StackProg.Exec.branchFalse (test := badT) (p := skipP) (by simp [badT, Sg]) e3
    refine ⟨_, _, ?_, StackProg.Exec.seq e0 (StackProg.Exec.seq e1 (StackProg.Exec.seq e2 e3')), ?_, ?_⟩
    · simp only [List.length_nil] at hn1; omega
    · intro h; rw [if_pos h.2.2.2]
    · intro h
      have hlt : ¬ g.prev < bval y := fun h' => h ⟨hgood.1.1, hgood.1.2, hgood.2, h'⟩
      rw [if_neg hlt]
      exact ⟨_, _, _, _, _, by simp, rfl⟩
  · have hb3n : b3 ≠ [] := by
      by_cases h1 : ok
      · have : y = [] := by by_contra h2; exact hgood ⟨h1, h2⟩
        simp [hb3, h1, hb1, this]
      · simp [hb3, h1]
    have e3 : (StackProg.branch badT skipP rest1).Exec (Sg { g with i := r3 } (enc y) b3 [] (lzF y []))
        (Sg { g with i := r3 } (enc y) b3 [] (lzF y [])) (1 + 1) := by
      refine StackProg.Exec.branchTrue ?_ (exec_skip _)
      simp only [badT, Sg]
      cases h : b3 with
      | nil => exact absurd h hb3n
      | cons _ _ => rfl
    refine ⟨_, _, ?_, StackProg.Exec.seq e0 (StackProg.Exec.seq e1 (StackProg.Exec.seq e2 e3)), ?_, ?_⟩
    · simp only [List.length_nil] at hn1; omega
    · intro h; exact absurd ⟨h.1, h.2.1⟩ (fun h' => hgood ⟨h', h.2.2.1⟩)
    · intro _; exact ⟨_, _, _, _, _, hb3n, rfl⟩

/-! ## The main loop -/

def procG : G → List ℕ → G
  | g, [] => g
  | g, v :: vs => procG (stepG g v) vs

lemma stepG_i (g : G) (v : ℕ) (a : List BSym) : stepG { g with i := a } v = { stepG g v with i := a } := by
  cases hp : g.par <;> simp [stepG, hp]

lemma procG_i : ∀ (xs : List ℕ) (g : G) (a : List BSym), procG { g with i := a } xs = { procG g xs with i := a } := by
  intro xs
  induction xs with
  | nil => intro g a; rfl
  | cons v xs ih => intro g a; simp only [procG]; rw [stepG_i, ih]

def Inv (L : ℕ) (g : G) : Prop :=
  g.U + g.i.length ≤ L ∧ g.S ≤ g.U * 2 ^ L ∧ g.prev ≤ g.S ∧ g.x1 ≤ g.S ∧ g.T + g.P ≤ g.S ∧
    g.K ≤ 5 * g.U * g.S ∧ g.Rl.length ≤ 2 * g.U * (L + 3)

def Vb (L : ℕ) : ℕ := 5 * L * (L * 2 ^ L) + 2 ^ L

lemma inv_vals {L : ℕ} {g : G} (h : Inv L g) :
    g.prev ≤ Vb L ∧ g.x1 ≤ Vb L ∧ g.S ≤ Vb L ∧ g.P ≤ Vb L ∧ g.T ≤ Vb L ∧ g.K ≤ Vb L := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
  have hU : g.U ≤ L := by omega
  have hS : g.S ≤ L * 2 ^ L := h2.trans (Nat.mul_le_mul_right _ hU)
  have hK : g.K ≤ 5 * L * (L * 2 ^ L) := h6.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hU) hS)
  have hSV : L * 2 ^ L ≤ 5 * L * (L * 2 ^ L) := by
    rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL; simp
    · have : 1 ≤ 5 * L := by omega
      calc L * 2 ^ L = 1 * (L * 2 ^ L) := by ring
        _ ≤ 5 * L * (L * 2 ^ L) := Nat.mul_le_mul_right _ this
  unfold Vb
  generalize 2 ^ L = Q at *
  generalize 5 * L * (L * Q) = W at *
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

lemma bval_lt (y : List Bool) : bval y < 2 ^ y.length := by
  induction y with
  | nil => simp [bval]
  | cons b y ih => simp only [bval, List.length_cons, pow_succ]; cases b <;> simp [Nat.bit] <;> omega

lemma poly_aux (L : ℕ) : 40 * L * L + 17 ≤ 2 ^ (2 * L + 7) := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    have : 2 ^ (2 * (L + 1) + 7) = 4 * 2 ^ (2 * L + 7) := by ring_nf
    rw [this]
    have h2 : 80 * L ≤ 120 * (L * L) + 11 := by
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · subst h0; norm_num
      · have : L ≤ L * L := Nat.le_mul_self L
        omega
    have h3 : 40 * (L + 1) * (L + 1) = 40 * (L * L) + 80 * L + 40 := by ring
    have h4 : 40 * L * L = 40 * (L * L) := by ring
    rw [h3]; rw [h4] at ih; omega

lemma size_Vb (L : ℕ) : Nat.size (8 * Vb L + 8) ≤ 3 * L + 7 := by
  rw [Nat.size_le]
  have h1 := poly_aux L
  have h2 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have h3 : 2 ^ (3 * L + 7) = 2 ^ L * 2 ^ (2 * L + 7) := by ring_nf
  rw [h3]; unfold Vb
  have h4 : 2 ^ L * (40 * L * L + 17) ≤ 2 ^ L * 2 ^ (2 * L + 7) := Nat.mul_le_mul_left _ h1
  nlinarith

lemma inv_step {L : ℕ} {g : G} (h : Inv L g) (y : List Bool) (r' : List BSym)
    (hi : g.i = enc y ++ .sep :: r') (hy : y ≠ []) (hlt : g.prev < bval y) :
    Inv L (stepG { g with i := r' } (bval y)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hlen : g.i.length = y.length + 1 + r'.length := by rw [hi]; simp [enc]; omega
  have hy1 : 1 ≤ y.length := List.length_pos_of_ne_nil hy
  have hv : bval y + 1 ≤ 2 ^ L := by
    have := bval_lt y
    have : 2 ^ y.length ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set v := bval y
  have hA : g.U + 1 + r'.length ≤ L := by omega
  have hB : g.S + (v + 1) ≤ (g.U + 1) * 2 ^ L := by rw [Nat.add_mul]; omega
  have e1 : 5 * (g.U + 1) * (g.S + (v + 1)) = 5 * g.U * (g.S + (v + 1)) + 5 * (g.S + (v + 1)) := by ring
  have e2 : 5 * g.U * g.S ≤ 5 * g.U * (g.S + (v + 1)) := Nat.mul_le_mul_left _ (by omega)
  have hC : ∀ x, x ≤ g.S + (v + 1) →
      g.K + g.T + g.T + (g.P + (v + 1)) + x + x ≤ 5 * (g.U + 1) * (g.S + (v + 1)) := by
    intro x hx; omega
  have hD : g.K ≤ 5 * (g.U + 1) * (g.S + (v + 1)) := by omega
  have hx1 : (if g.seen then g.x1 else v) ≤ g.S + (v + 1) := by split_ifs <;> omega
  have hsv : Nat.size v ≤ y.length := Nat.size_le.2 (bval_lt y)
  have hsv1 : Nat.size (v + 1) ≤ y.length + 1 := by
    apply Nat.size_le.2
    have := bval_lt y
    rw [pow_succ]; omega
  have hRl : (BSym.sep :: ((eb (v + 1)).reverse ++ (BSym.zero :: (if g.seen then g.Rl else BSym.sep :: ((eb v).reverse ++ (BSym.zero :: g.Rl)))))).length ≤ 2 * (g.U + 1) * (L + 3) := by
    have e3 : 2 * (g.U + 1) * (L + 3) = 2 * g.U * (L + 3) + 2 * (L + 3) := by ring
    rw [e3]
    split_ifs <;> simp [len_eb] <;> omega
  cases hp : g.par
  · simp only [stepG, hp, Bool.false_eq_true, ↓reduceIte]
    refine ⟨hA, hB, ?_, hx1, ?_, hD, hRl⟩
    · show v ≤ g.S + (v + 1); omega
    · show g.T + (g.P + (v + 1)) ≤ g.S + (v + 1); omega
  · simp only [stepG, hp, Bool.false_eq_true, ↓reduceIte]
    refine ⟨hA, hB, ?_, hx1, ?_, hC _ hx1, hRl⟩
    · show v ≤ g.S + (v + 1); omega
    · show g.T + (g.P + (v + 1)) + 0 ≤ g.S + (v + 1); omega

lemma round_cost (L : ℕ) (y : List Bool) (hy : y.length ≤ L) :
    500 * Nat.size (8 * Vb L + 8) + 6 * y.length + 700 + 3 ≤ 1600 * L + 4300 := by
  have := size_Vb L; omega

lemma loop_all (L : ℕ) : ∀ (M : ℕ) (g : G), g.i.length ≤ M → Inv L g →
    ∃ t n, n ≤ (g.i.length + 1) * (1600 * L + 4300) ∧ mainLoop.Exec (Sg g [] [] [] []) t n ∧
      (∀ xs : List ℕ, g.i = encNats xs → List.Chain (· < ·) g.prev xs →
        t = Sg { procG g xs with i := [] } [] [] [] []) ∧
      ((¬ ∃ xs : List ℕ, g.i = encNats xs ∧ List.Chain (· < ·) g.prev xs) →
        ∃ g' cur b lt lz, b ≠ [] ∧ t = Sg g' cur b lt lz) := by
  intro M
  induction M with
  | zero =>
    intro g hM hinv
    have hi : g.i = [] := List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨_, 1, by simp [hi], StackProg.Exec.loopFalse (by simp [loopTest, Sg, hi]), ?_, ?_⟩
    · intro xs hxs _
      have := encNats_eq_nil (hi ▸ hxs).symm; subst this
      simp only [procG]; rw [← hi]
    · intro h; exact absurd ⟨[], by simp [hi, encNats], List.Chain.nil⟩ h
  | succ M ih =>
    intro g hM hinv
    by_cases hnil : g.i = []
    · refine ⟨_, 1, by simp [hnil], StackProg.Exec.loopFalse (by simp [loopTest, Sg, hnil]), ?_, ?_⟩
      · intro xs hxs _
        have := encNats_eq_nil (hnil ▸ hxs).symm; subst this
        simp only [procG]; rw [← hnil]
      · intro h; exact absurd ⟨[], by simp [hnil, encNats], List.Chain.nil⟩ h
    obtain ⟨y, r, hi_eq, hr⟩ : ∃ y r, g.i = enc y ++ r ∧ isDig r.head? = false :=
      ⟨_, _, (split_digits g.i).1, (split_digits g.i).2⟩
    have hg : g = { g with i := enc y ++ r } := by rw [← hi_eq]
    have hlen : g.i.length = y.length + r.length := by rw [hi_eq]; simp [enc]
    have htest : loopTest (fun k => (Sg g [] [] [] [] k).head?) = true := by
      simp only [loopTest, Sg, List.head?_nil, Option.isNone_none, Bool.and_true]
      cases h : g.i with
      | nil => exact absurd h hnil
      | cons _ _ => rfl
    obtain ⟨hp, hx, hS, hP, hT, hK⟩ := inv_vals hinv
    have hyL : y.length ≤ L := by have := hinv.1; omega
    have hv : bval y ≤ Vb L := by
      have h1 := bval_lt y
      have h2 : 2 ^ y.length ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hyL
      unfold Vb; omega
    obtain ⟨t1, n, hn, eb1, hgood, hbad⟩ := exec_body g y r hr (Vb L) hp hx hS hP hT hK hv
    rw [← hg] at eb1
    have hrc := round_cost L y hyL
    by_cases hc : r.head? = some .sep ∧ Canon y ∧ y ≠ [] ∧ g.prev < bval y
    · have ht1 := hgood hc
      obtain ⟨r', rfl⟩ : ∃ r', r = .sep :: r' := by
        rcases r with _ | ⟨b, r'⟩
        · simp at hc
        · simp at hc; exact ⟨r', by rw [hc.1]⟩
      simp only [List.tail_cons] at ht1
      set g1 := stepG { g with i := r' } (bval y) with hg1
      have hinv1 : Inv L g1 := inv_step hinv y r' hi_eq hc.2.2.1 hc.2.2.2
      have hg1i : g1.i = r' := by rw [hg1, stepG_i]
      have hy1 : 1 ≤ y.length := List.length_pos_of_ne_nil hc.2.2.1
      obtain ⟨t, m, hm, hex, hval, hinv'⟩ := ih g1 (by rw [hg1i]; simp at hlen; omega) hinv1
      have hprev : g1.prev = bval y := by rw [hg1]; cases g.par <;> simp [stepG]
      rw [ht1] at eb1
      refine ⟨t, 1 + n + 1 + m, ?_, StackProg.Exec.loopTrue htest eb1 hex, ?_, ?_⟩
      · rw [hg1i] at hm
        have hl2 : g.i.length = y.length + 1 + r'.length := by simp at hlen; omega
        rw [hl2]
        have : (y.length + 1 + r'.length + 1) * (1600 * L + 4300) =
            (r'.length + 1) * (1600 * L + 4300) + (y.length + 1) * (1600 * L + 4300) := by ring
        rw [this]
        have : 1600 * L + 4300 ≤ (y.length + 1) * (1600 * L + 4300) := Nat.le_mul_of_pos_left _ (by omega)
        omega
      · intro xs hxs hch
        rcases xs with _ | ⟨k', xs'⟩
        · exact absurd (hxs.trans (by simp [encNats])) hnil
        rw [hi_eq, encNats_cons'] at hxs
        obtain ⟨h1, h2⟩ := enc_append_inj hr (by rfl) hxs
        simp only [List.cons.injEq, true_and] at h2
        have hkk : bval y = k' := by rw [h1, (canon_bits_bval k').2]
        obtain ⟨hch1, hch2⟩ : g.prev < k' ∧ List.Chain (· < ·) k' xs' := by
          cases hch with
          | cons_cons h1 h2 => exact ⟨h1, h2⟩
        have hch := And.intro hch1 hch2
        rw [hval xs' (by rw [hg1i, h2]) (by rw [hprev, hkk]; exact hch2)]
        simp only [procG, hg1, hkk, procG_i, stepG_i]
      · intro hall
        apply hinv'
        rintro ⟨xs', h', hch'⟩
        apply hall
        refine ⟨bval y :: xs', ?_, ?_⟩
        · rw [hi_eq, encNats_cons', bits_bval hc.2.1, ← hg1i, h']
        · refine List.Chain.cons hc.2.2.2 ?_
          have : g1.prev = bval y := by rw [hg1]; cases g.par <;> simp [stepG]
          rwa [this] at hch'
    · obtain ⟨g', cur, b, lt, lz, hb, ht1⟩ := hbad hc
      rw [ht1] at eb1
      refine ⟨_, 1 + n + 1 + 1, ?_, StackProg.Exec.loopTrue htest eb1 (StackProg.Exec.loopFalse ?_), ?_, ?_⟩
      · have : 1600 * L + 4300 ≤ (g.i.length + 1) * (1600 * L + 4300) := Nat.le_mul_of_pos_left _ (by omega)
        omega
      · simp only [loopTest, Sg]
        cases h : b with
        | nil => exact absurd h hb
        | cons _ _ => simp
      · intro xs hxs hch
        exfalso
        rcases xs with _ | ⟨k', xs'⟩
        · exact hnil hxs
        rw [hi_eq, encNats_cons'] at hxs
        obtain ⟨h1, h2⟩ := enc_append_inj hr (by rfl) hxs
        apply hc
        obtain ⟨hch1, hch2⟩ : g.prev < k' ∧ List.Chain (· < ·) k' xs' := by
          cases hch with
          | cons_cons h1 h2 => exact ⟨h1, h2⟩
        have hch := And.intro hch1 hch2
        subst h1 h2
        refine ⟨rfl, (canon_bits_bval k').1, ?_, ?_⟩
        · intro h0
          have := (canon_bits_bval k').2
          rw [h0] at this
          simp [bval] at this; omega
        · rw [(canon_bits_bval k').2]; exact hch.1
      · intro _; exact ⟨_, _, _, _, _, hb, rfl⟩

/-! ## The binary counter -/

def incAct (_ : Key → Option BSym) (k : Key) : StackAct BSym :=
  if k = .c2 then .pop else if k = .e0 then .push .one else .keep

def countBody : StackProg Key BSym :=
  .seq (.act incAct) (.seq (addLoop .e0 .Nb) (transferProg .tmp (fun k => decide (k = .Nb))))

def countLoop : StackProg Key BSym := .loop (fun h => (h .c2).isSome) countBody

lemma exec_count : ∀ (N b : ℕ) (s : Store), s .c2 = List.replicate N .one →
    s .Nb = enc (Nat.bits b) → s .e0 = [] → s .tmp = [] → s .car = [] → s .lz = [] →
    ∃ n ≤ N * (6 * (b + N) + 30) + 1, countLoop.Exec s
      (Function.update (Function.update s .c2 []) .Nb (enc (Nat.bits (b + N)))) n := by
  intro N
  induction N with
  | zero =>
    intro b s hc1 hbc _ _ _ _
    refine ⟨1, by simp, ?_⟩
    have : Function.update (Function.update s .c2 []) .Nb (enc (Nat.bits (b + 0))) = s := by
      funext k
      by_cases h1 : k = .Nb
      · subst h1; simp [hbc]
      by_cases h2 : k = .c2
      · subst h2; simp [hc1]
      · simp [h1, h2]
    rw [this]
    exact StackProg.Exec.loopFalse (by simp [hc1])
  | succ N ih =>
    intro b s hc1 hbc he0 htmp hcar hlz
    set s1 := StackProg.applyAct incAct s with hs1
    have h1c1 : s1 .c2 = List.replicate N .one := by
      simp [hs1, StackProg.applyAct, incAct, StackAct.apply, hc1, List.replicate_succ]
    have h1e0 : s1 .e0 = enc [true] ++ [] := by
      simp [hs1, StackProg.applyAct, incAct, StackAct.apply, he0, enc, toB]
    have h1oth : ∀ k, k ≠ .c2 → k ≠ .e0 → s1 k = s k := by
      intro k k1 k2; simp [hs1, StackProg.applyAct, incAct, StackAct.apply, k1, k2]
    obtain ⟨n1, hn1, e1⟩ := exec_addLoop .e0 .Nb (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) [] (by rfl) _ (Nat.bits b) [true] false s1 le_rfl
      (by rw [h1oth _ (by decide) (by decide), hbc]) h1e0
      (by rw [h1oth _ (by decide) (by decide), hcar]; rfl)
      (Or.inl (by rw [h1oth _ (by decide) (by decide), hlz]))
    set s2 := addPost .e0 .Nb (Nat.bits b) [true] false [] s1 with hs2
    have hadd : addB (Nat.bits b) [true] false = Nat.bits (b + 1) := by
      rw [bits_add, bits_one]
    obtain ⟨n2, hn2, e2⟩ := exec_transfer .tmp (fun k => decide (k = .Nb)) _ s2 rfl
    set s3 := transferStore .tmp (fun k => decide (k = .Nb)) s2 with hs3
    have h3 : ∀ k, s3 k = if k = .c2 then List.replicate N .one
        else if k = .Nb then enc (Nat.bits (b + 1)) else s k := by
      intro k
      by_cases k1 : k = .c2
      · subst k1; simp [hs3, hs2, transferStore, addPost, h1c1]
      by_cases k2 : k = .Nb
      · subst k2; simp [hs3, hs2, transferStore, addPost, hadd, htmp, h1oth]
      by_cases k3 : k = .e0
      · subst k3; simp [hs3, hs2, transferStore, addPost, he0]
      by_cases k4 : k = .tmp
      · subst k4; simp [hs3, hs2, transferStore, addPost, htmp]
      by_cases k5 : k = .car
      · subst k5; simp [hs3, hs2, transferStore, addPost, hcar]
      by_cases k6 : k = .lz
      · subst k6; simp [hs3, hs2, transferStore, addPost, hlz, lzF, h1oth]
      · simp [hs3, hs2, transferStore, addPost, k1, k2, k3, k4, k5, k6, h1oth]
    obtain ⟨m, hm, ex⟩ := ih (b + 1) s3 (by rw [h3]; simp) (by rw [h3]; simp)
      (by rw [h3]; simp [he0]) (by rw [h3]; simp [htmp]) (by rw [h3]; simp [hcar])
      (by rw [h3]; simp [hlz])
    have hfin : Function.update (Function.update s3 .c2 []) .Nb (enc (Nat.bits (b + 1 + N))) =
        Function.update (Function.update s .c2 []) .Nb (enc (Nat.bits (b + (N + 1)))) := by
      funext k
      by_cases k1 : k = .Nb
      · subst k1; simp [Nat.add_assoc, Nat.add_comm 1 N]
      by_cases k2 : k = .c2
      · subst k2; simp
      · simp [k1, k2, h3]
    rw [hfin] at ex
    have eb : countBody.Exec s s3 (1 + 1 + (n1 + 1 + n2)) :=
      StackProg.Exec.seq (StackProg.Exec.act incAct s) (StackProg.Exec.seq e1 e2)
    refine ⟨1 + (1 + 1 + (n1 + 1 + n2)) + 1 + m, ?_,
      StackProg.Exec.loopTrue (by simp [hc1, List.replicate_succ]) eb ex⟩
    have lb := len_bits_le b
    have lb1 := len_bits_le (b + 1)
    have : s2 .tmp = (enc (Nat.bits (b + 1))).reverse := by simp [hs2, addPost, hadd, h1oth, htmp]
    rw [this] at hn2
    simp only [enc, List.length_reverse, List.length_map, List.length_cons, List.length_nil,
      Bool.toNat_false] at hn1 hn2
    have hNb : N * (6 * (b + 1 + N) + 30) ≤ N * (6 * (b + (N + 1)) + 30) :=
      Nat.mul_le_mul_left _ (by omega)
    have : (N + 1) * (6 * (b + (N + 1)) + 30) = N * (6 * (b + (N + 1)) + 30) + (6 * (b + (N + 1)) + 30) := by ring
    omega


/-! ## The output phase -/

def repLoop : StackProg Key BSym := .loop (fun h => (h .c2).isSome) (.seq (popProg .c2) (emitTo .S .R))

lemma exec_rep : ∀ (N : ℕ) (s : Store), s .c2 = List.replicate N .one → s .W = [] → s .sc = [] →
    ∃ n ≤ N * (9 * (s .S).length + 12) + 1, repLoop.Exec s
      (Function.update (Function.update s .c2 [])
        .R ((List.replicate N (.sep :: (s .S).reverse)).flatten ++ s .R)) n := by
  intro N
  induction N with
  | zero =>
    intro s hc hW hsc
    refine ⟨1, by simp, ?_⟩
    have : Function.update (Function.update s .c2 []) .R
        ((List.replicate 0 (.sep :: (s .S).reverse)).flatten ++ s .R) = s := by
      funext k
      by_cases k1 : k = .R
      · subst k1; simp
      by_cases k2 : k = .c2
      · subst k2; simp [hc]
      · simp [k1, k2]
    rw [this]
    exact StackProg.Exec.loopFalse (by simp [hc])
  | succ N ih =>
    intro s hc hW hsc
    have e1 := StackProg.Exec.act (fun (_ : Key → Option BSym) (k : Key) => if k = .c2 then StackAct.pop (A := BSym) else .keep) s
    have p1 : StackProg.applyAct (fun (_ : Key → Option BSym) (k : Key) => if k = .c2 then StackAct.pop (A := BSym) else .keep) s = Function.update s .c2 (List.replicate N .one) := by
      funext k; by_cases hk : k = .c2
      · subst hk; simp [StackProg.applyAct, StackAct.apply, hc, List.replicate_succ]
      · simp [StackProg.applyAct, StackAct.apply, hk]
    rw [p1] at e1
    set s1 := Function.update s .c2 (List.replicate N .one) with hs1
    obtain ⟨n2, hn2, e2⟩ := exec_emitTo .S .R (by decide) (by decide) (by decide) (by decide)
      (by decide) s1 (by simp [hs1, hW]) (by simp [hs1, hsc])
    set s2 := Function.update s1 .R (.sep :: ((s1 .S).reverse ++ s1 .R)) with hs2
    obtain ⟨m, hm, e3⟩ := ih s2 (by simp [hs2, hs1]) (by simp [hs2, hs1, hW]) (by simp [hs2, hs1, hsc])
    have hfin : Function.update (Function.update s2 .c2 []) .R
        ((List.replicate N (.sep :: (s2 .S).reverse)).flatten ++ s2 .R) =
        Function.update (Function.update s .c2 []) .R
          ((List.replicate (N + 1) (.sep :: (s .S).reverse)).flatten ++ s .R) := by
      funext k
      by_cases k1 : k = .R
      · subst k1; simp [hs2, hs1, List.replicate_succ']
      by_cases k2 : k = .c2
      · subst k2; simp [k1]
      · simp [k1, k2, hs2, hs1]
    rw [hfin] at e3
    have eb2 : (StackProg.seq (popProg .c2) (emitTo .S .R)).Exec s s2 (1 + 1 + n2) :=
      StackProg.Exec.seq e1 e2
    refine ⟨1 + (1 + 1 + n2) + 1 + m, ?_, StackProg.Exec.loopTrue (by simp [hc, List.replicate_succ]) eb2 e3⟩
    have q2 : (s2 .S).length = (s .S).length := by simp [hs2, hs1]
    have q1 : (s1 .S).length = (s .S).length := by simp [hs1]
    rw [q1] at hn2; rw [q2] at hm
    have hNb : (N + 1) * (9 * (s .S).length + 12) = N * (9 * (s .S).length + 12) + (9 * (s .S).length + 12) := by ring
    omega

def outP : StackProg Key BSym :=
  (.seq (copyProg .U .c2 .sc)
    (.seq (pushAt .Nb .one)
    (.seq (pushAt .Nb .zero)
    (.seq (countLoop)
    (.seq (emitTo .Nb .R)
    (.seq (emitTo .K .R)
    (.seq (addTo .x1 .S)
    (.seq (copyProg .U .c2 .sc)
    (.seq (repLoop)
    (.seq (emitTo .S .R)
    (.seq (incP .S)
    (.seq (pushAt .R .zero)
    (.seq (emitTo .S .R)
    (.seq (copyProg .Rl .R .sc)
    (.seq (pushAt .R .zero)
    (.seq (pushAt .R .zero)
    (.seq (pushAt .R .one)
    (.seq (pushAt .R .sep)
    (transferProg .R (fun k => decide (k = .out)))))))))))))))))))))

/-- The final output in terms of the registers. -/
def outWord (g : G) : List BSym :=
  encNat (g.U + 2) ++ encNat g.K ++ (List.replicate (g.U + 1) (encNat (g.S + g.x1))).flatten ++
    encNat (2 * (g.S + g.x1 + 1)) ++ g.Rl.reverse ++ encNat 4

lemma encNat_double (m : ℕ) (hm : 0 < m) : encNat (2 * m) = .zero :: (enc (Nat.bits m) ++ [.sep]) := by
  have : Nat.bits (2 * m) = false :: Nat.bits m := by
    have h := Nat.bits_append_bit m false (fun h => absurd h (by omega))
    simpa [Nat.bit] using h
  simp [encNat, this, enc, toB]

lemma encNat_rev (k : ℕ) : (encNat k).reverse = .sep :: (eb k).reverse := by
  simp [encNat, eb, enc, toB]

lemma flat_rev (N : ℕ) (l : List BSym) :
    ((List.replicate N l.reverse).flatten).reverse = (List.replicate N l).flatten := by
  induction N with
  | zero => simp
  | succ N ih => rw [List.replicate_succ, List.flatten_cons, List.reverse_append, ih, List.reverse_reverse, List.replicate_succ', List.flatten_append]; simp


def Os (g : G) (c2 Nb : List BSym) : Store := fun k =>
  match k with
  | .c2 => c2 | .Nb => Nb | k => Sg g [] [] [] [] k

lemma bits_two : Nat.bits 2 = [false, true] := by
  have h := Nat.bits_append_bit 1 false (by simp)
  rw [bits_one] at h; simpa [Nat.bit] using h

set_option maxHeartbeats 1000000 in
lemma exec_outP (g : G) (V L : ℕ) (hU : g.U ≤ L) (hS : g.S ≤ V) (hx : g.x1 ≤ V) (hK : g.K ≤ V)
    (hRl : g.Rl.length ≤ 2 * g.U * (L + 3)) (hR : g.R = []) :
    ∃ t n, n ≤ 300 * (L + 1) * (Nat.size (8 * V + 8) + L + 10) ∧
      outP.Exec (Sg g [] [] [] []) t n ∧ t .out = outWord g := by
  set Z := Nat.size (8 * V + 8) with hZ
  have l1 : ∀ a, a ≤ 8 * V + 8 → (eb a).length ≤ Z := fun a ha => by rw [len_eb]; exact size_mono ha
  -- 1. c2 := U
  obtain ⟨n1, hn1, e1⟩ := exec_copy .U .c2 .sc (by decide) (by decide) (by decide) (Sg g [] [] [] []) rfl
  have p1 : Function.update (Sg g [] [] [] []) .c2 ((Sg g [] [] [] []) .U ++ (Sg g [] [] [] []) .c2) = Os g (List.replicate g.U .one) [] := by
    funext k; cases k <;> simp [Sg, Os]
  rw [p1] at e1
  -- 2, 3. Nb := 2
  have e2 := exec_pushAt .Nb .one (Os g (List.replicate g.U .one) [])
  have p2 : Function.update (Os g (List.replicate g.U .one) []) .Nb (.one :: (Os g (List.replicate g.U .one) []) .Nb) = Os g (List.replicate g.U .one) [.one] := by
    funext k; cases k <;> rfl
  rw [p2] at e2
  have e3 := exec_pushAt .Nb .zero (Os g (List.replicate g.U .one) [.one])
  have p3 : Function.update (Os g (List.replicate g.U .one) [.one]) .Nb (.zero :: (Os g (List.replicate g.U .one) [.one]) .Nb) = Os g (List.replicate g.U .one) [.zero, .one] := by
    funext k; cases k <;> rfl
  rw [p3] at e3
  -- 4. count
  obtain ⟨n4, hn4, e4⟩ := exec_count g.U 2 (Os g (List.replicate g.U .one) [.zero, .one]) rfl
    (by simp [Os, bits_two, enc, toB]) rfl rfl rfl rfl
  have p4 : Function.update (Function.update (Os g (List.replicate g.U .one) [.zero, .one]) .c2 []) .Nb (enc (Nat.bits (2 + g.U))) = Os g [] (eb (2 + g.U)) := by
    funext k; cases k <;> rfl
  rw [p4] at e4
  -- 5. emit N
  obtain ⟨n5, hn5, e5⟩ := exec_emitTo .Nb .R (by decide) (by decide) (by decide) (by decide) (by decide) (Os g [] (eb (2 + g.U))) rfl rfl
  set g5 : G := { g with R := .sep :: (eb (2 + g.U)).reverse } with hg5
  have p5 : Function.update (Os g [] (eb (2 + g.U))) .R (.sep :: (((Os g [] (eb (2 + g.U))) .Nb).reverse ++ (Os g [] (eb (2 + g.U))) .R)) = Os g5 [] (eb (2 + g.U)) := by
    funext k; cases k <;> simp [Os, Sg, hg5, hR]
  rw [p5] at e5
  -- 6. emit K
  obtain ⟨n6, hn6, e6⟩ := exec_emitTo .K .R (by decide) (by decide) (by decide) (by decide) (by decide) (Os g5 [] (eb (2 + g.U))) rfl rfl
  set g6 : G := { g5 with R := .sep :: ((eb g.K).reverse ++ g5.R) } with hg6
  have p6 : Function.update (Os g5 [] (eb (2 + g.U))) .R (.sep :: (((Os g5 [] (eb (2 + g.U))) .K).reverse ++ (Os g5 [] (eb (2 + g.U))) .R)) = Os g6 [] (eb (2 + g.U)) := by
    funext k; cases k <;> rfl
  rw [p6] at e6
  -- 7. S := S + x1
  obtain ⟨n7, hn7, e7⟩ := exec_addTo .x1 .S (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Nat.bits g.S) (Nat.bits g.x1) [] (by rfl) (Os g6 [] (eb (2 + g.U))) rfl (by simp [Os, Sg, eb, hg6, hg5]) rfl rfl (Or.inl rfl)
  set g7 : G := { g6 with S := g.S + g.x1, x1 := 0 } with hg7
  have p7 : Function.update (Function.update (Function.update (Os g6 [] (eb (2 + g.U))) .S (enc (addB (Nat.bits g.S) (Nat.bits g.x1) false))) .x1 []) .lz (lzF (Nat.bits g.x1) ((Os g6 [] (eb (2 + g.U))) .lz)) = Os g7 [] (eb (2 + g.U)) := by
    have hl : lzF (Nat.bits g.x1) [] = [] := (lzF_nil_iff _).2 (canon_bits_bval _).1
    rw [← bits_add]
    funext k; cases k <;> simp [Os, Sg, hl, hg7, hg6, hg5, eb, enc]
  rw [p7] at e7
  -- 8. c2 := U
  obtain ⟨n8, hn8, e8⟩ := exec_copy .U .c2 .sc (by decide) (by decide) (by decide) (Os g7 [] (eb (2 + g.U))) rfl
  have p8 : Function.update (Os g7 [] (eb (2 + g.U))) .c2 ((Os g7 [] (eb (2 + g.U))) .U ++ (Os g7 [] (eb (2 + g.U))) .c2) = Os g7 (List.replicate g.U .one) (eb (2 + g.U)) := by
    funext k; cases k <;> simp [Os, Sg, hg7, hg6, hg5]
  rw [p8] at e8
  -- 9. repeat
  obtain ⟨n9, hn9, e9⟩ := exec_rep g.U (Os g7 (List.replicate g.U .one) (eb (2 + g.U))) rfl rfl rfl
  set S2 := g.S + g.x1 with hS2
  set g9 : G := { g7 with R := (List.replicate g.U (.sep :: (eb S2).reverse)).flatten ++ g7.R } with hg9
  have p9 : Function.update (Function.update (Os g7 (List.replicate g.U .one) (eb (2 + g.U))) .c2 []) .R ((List.replicate g.U (.sep :: ((Os g7 (List.replicate g.U .one) (eb (2 + g.U))) .S).reverse)).flatten ++ (Os g7 (List.replicate g.U .one) (eb (2 + g.U))) .R) = Os g9 [] (eb (2 + g.U)) := by
    funext k; cases k <;> rfl
  rw [p9] at e9
  -- 10. emit S once more
  obtain ⟨n10, hn10, e10⟩ := exec_emitTo .S .R (by decide) (by decide) (by decide) (by decide) (by decide) (Os g9 [] (eb (2 + g.U))) rfl rfl
  set g10 : G := { g9 with R := .sep :: ((eb S2).reverse ++ g9.R) } with hg10
  have p10 : Function.update (Os g9 [] (eb (2 + g.U))) .R (.sep :: (((Os g9 [] (eb (2 + g.U))) .S).reverse ++ (Os g9 [] (eb (2 + g.U))) .R)) = Os g10 [] (eb (2 + g.U)) := by
    funext k; cases k <;> rfl
  rw [p10] at e10
  -- 11. S := S2 + 1
  have e11a := exec_pushAt .e0 .one (Os g10 [] (eb (2 + g.U)))
  obtain ⟨n11, hn11, e11b⟩ := exec_addTo .e0 .S (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Nat.bits S2) [true] [] (by rfl) (Function.update (Os g10 [] (eb (2 + g.U))) .e0 (.one :: (Os g10 [] (eb (2 + g.U))) .e0))
    (by simp [Os, Sg, eb, hg10, hg9, hg7]) (by simp [Os, Sg, enc, toB]) (by simp [Os, Sg]) (by simp [Os, Sg]) (by simp [Os, Sg])
  set g11 : G := { g10 with S := S2 + 1 } with hg11
  have p11 : Function.update (Function.update (Function.update (Function.update (Os g10 [] (eb (2 + g.U))) .e0 (.one :: (Os g10 [] (eb (2 + g.U))) .e0)) .S (enc (addB (Nat.bits S2) [true] false))) .e0 []) .lz (lzF [true] ((Function.update (Os g10 [] (eb (2 + g.U))) .e0 (.one :: (Os g10 [] (eb (2 + g.U))) .e0)) .lz)) = Os g11 [] (eb (2 + g.U)) := by
    have : addB (Nat.bits S2) [true] false = Nat.bits (S2 + 1) := by
      have h := bits_add S2 1; rw [bits_one] at h; exact h.symm
    rw [this]
    funext k; cases k <;> simp [Os, Sg, lzF, eb, hg11]
  rw [p11] at e11b
  have e11 : (incP .S).Exec (Os g10 [] (eb (2 + g.U))) (Os g11 [] (eb (2 + g.U))) (1 + 1 + n11) := StackProg.Exec.seq e11a e11b
  -- 12, 13. emit 2 (S2 + 1)
  have e12 := exec_pushAt .R .zero (Os g11 [] (eb (2 + g.U)))
  set g12 : G := { g11 with R := .zero :: g11.R } with hg12
  have p12 : Function.update (Os g11 [] (eb (2 + g.U))) .R (.zero :: (Os g11 [] (eb (2 + g.U))) .R) = Os g12 [] (eb (2 + g.U)) := by
    funext k; cases k <;> rfl
  rw [p12] at e12
  obtain ⟨n13, hn13, e13⟩ := exec_emitTo .S .R (by decide) (by decide) (by decide) (by decide) (by decide) (Os g12 [] (eb (2 + g.U))) rfl rfl
  set g13 : G := { g12 with R := .sep :: ((eb (S2 + 1)).reverse ++ g12.R) } with hg13
  have p13 : Function.update (Os g12 [] (eb (2 + g.U))) .R (.sep :: (((Os g12 [] (eb (2 + g.U))) .S).reverse ++ (Os g12 [] (eb (2 + g.U))) .R)) = Os g13 [] (eb (2 + g.U)) := by
    funext k; cases k <;> rfl
  rw [p13] at e13
  -- 14. R := Rl ++ R
  obtain ⟨n14, hn14, e14⟩ := exec_copy .Rl .R .sc (by decide) (by decide) (by decide) (Os g13 [] (eb (2 + g.U))) rfl
  set g14 : G := { g13 with R := g.Rl ++ g13.R } with hg14
  have p14 : Function.update (Os g13 [] (eb (2 + g.U))) .R ((Os g13 [] (eb (2 + g.U))) .Rl ++ (Os g13 [] (eb (2 + g.U))) .R) = Os g14 [] (eb (2 + g.U)) := by
    funext k; cases k <;> rfl
  rw [p14] at e14
  -- 15-18. the code of 4
  have e15 := exec_pushAt .R .zero (Os g14 [] (eb (2 + g.U)))
  have e16 := exec_pushAt .R .zero (Function.update (Os g14 [] (eb (2 + g.U))) .R (.zero :: (Os g14 [] (eb (2 + g.U))) .R))
  have e17 := exec_pushAt .R .one (Function.update (Function.update (Os g14 [] (eb (2 + g.U))) .R (.zero :: (Os g14 [] (eb (2 + g.U))) .R)) .R (.zero :: (Function.update (Os g14 [] (eb (2 + g.U))) .R (.zero :: (Os g14 [] (eb (2 + g.U))) .R)) .R))
  set s17 := Function.update (Function.update (Function.update (Os g14 [] (eb (2 + g.U))) .R (.zero :: (Os g14 [] (eb (2 + g.U))) .R)) .R (.zero :: (Function.update (Os g14 [] (eb (2 + g.U))) .R (.zero :: (Os g14 [] (eb (2 + g.U))) .R)) .R)) .R (.one :: (Function.update (Function.update (Os g14 [] (eb (2 + g.U))) .R (.zero :: (Os g14 [] (eb (2 + g.U))) .R)) .R (.zero :: (Function.update (Os g14 [] (eb (2 + g.U))) .R (.zero :: (Os g14 [] (eb (2 + g.U))) .R)) .R)) .R) with hs17
  have e18 := exec_pushAt .R .sep s17
  set s18 := Function.update s17 .R (.sep :: s17 .R) with hs18
  have hR18 : s18 .R = .sep :: .one :: .zero :: .zero :: g14.R := by simp [hs18, hs17, Os, Sg]
  -- 19. output
  obtain ⟨n19, hn19, e19⟩ := exec_transfer .R (fun k => decide (k = .out)) (s18 .R) s18 rfl
  refine ⟨_, _, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3 (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7 (StackProg.Exec.seq e8 (StackProg.Exec.seq e9 (StackProg.Exec.seq e10 (StackProg.Exec.seq e11 (StackProg.Exec.seq e12 (StackProg.Exec.seq e13 (StackProg.Exec.seq e14 (StackProg.Exec.seq e15 (StackProg.Exec.seq e16 (StackProg.Exec.seq e17 (StackProg.Exec.seq e18 e19))))))))))))))))), ?_⟩
  · have hZsz : ∀ a ≤ 8 * V + 8, Nat.size a ≤ Z := fun a ha => by
      have := l1 a ha; rwa [len_eb] at this
    have hb1 : (Sg g [] [] [] [] Key.U).length = g.U := by simp [Sg]
    have hb5 : (Os g [] (eb (2 + g.U)) Key.Nb).length ≤ L + 2 := by
      simp only [Os, len_eb]; have := len_bits_le (2 + g.U); rw [Nat.size_eq_bits_len] at this; omega
    have hb6 : (Os g5 [] (eb (2 + g.U)) Key.K).length ≤ Z := by
      simp only [Os, Sg, hg5, len_eb]; exact hZsz _ (by omega)
    have hb7a : g.S.bits.length ≤ Z := by rw [Nat.size_eq_bits_len]; exact hZsz _ (by omega)
    have hb7b : g.x1.bits.length ≤ Z := by rw [Nat.size_eq_bits_len]; exact hZsz _ (by omega)
    have hb8 : (Os g7 [] (eb (2 + g.U)) Key.U).length = g.U := by simp [Os, Sg, hg7, hg6, hg5]
    have hb9 : (Os g7 (List.replicate g.U BSym.one) (eb (2 + g.U)) Key.S).length ≤ Z := by
      simp only [Os, Sg, hg7, len_eb]; exact hZsz _ (by omega)
    have hb10 : (Os g9 [] (eb (2 + g.U)) Key.S).length ≤ Z := by
      simp only [Os, Sg, hg9, hg7, len_eb]; exact hZsz _ (by omega)
    have hb11 : S2.bits.length ≤ Z := by rw [Nat.size_eq_bits_len]; exact hZsz _ (by omega)
    have hb13 : (Os g12 [] (eb (2 + g.U)) Key.S).length ≤ Z := by
      simp only [Os, Sg, hg12, hg11, len_eb]; exact hZsz _ (by omega)
    have hb14 : (Os g13 [] (eb (2 + g.U)) Key.Rl).length ≤ 2 * g.U * (L + 3) := by
      simp only [Os, Sg, hg13, hg12, hg11, hg10, hg9, hg7, hg6, hg5]; exact hRl
    have hKZ : (eb g.K).length ≤ Z := l1 _ (by omega)
    have hS2Z : (eb S2).length ≤ Z := l1 _ (by omega)
    have hS21Z : (eb (S2 + 1)).length ≤ Z := l1 _ (by omega)
    have hUZ : (eb (2 + g.U)).length ≤ L + 2 := by
      rw [len_eb]; have := len_bits_le (2 + g.U); rw [Nat.size_eq_bits_len] at this; omega
    have hb19 : (s18 Key.R).length ≤ g.U * (Z + 1) + 2 * g.U * (L + 3) + 4 * Z + L + 12 := by
      rw [hR18]
      simp only [hg14, hg13, hg12, hg11, hg10, hg9, hg7, hg6, hg5, hR, List.length_cons,
        List.length_append, List.length_reverse, List.length_flatten, List.map_replicate,
        List.sum_replicate, smul_eq_mul]
      have hm : g.U * ((eb S2).length + 1) ≤ g.U * (Z + 1) := Nat.mul_le_mul_left _ (by omega)
      clear * - hm hS2Z hS21Z hKZ hUZ hRl
      omega
    rw [hb1] at hn1
    rw [hb8] at hn8
    have m4 : g.U * (6 * (2 + g.U) + 30) ≤ L * (6 * L + 42) := Nat.mul_le_mul hU (by omega)
    have m9 : g.U * (9 * (Os g7 (List.replicate g.U BSym.one) (eb (2 + g.U)) Key.S).length + 12) ≤
        L * (9 * Z + 12) := Nat.mul_le_mul hU (by omega)
    have m14 : 2 * g.U * (L + 3) ≤ 2 * L * (L + 3) := Nat.mul_le_mul_right _ (by omega)
    have m19 : g.U * (Z + 1) ≤ L * (Z + 1) := Nat.mul_le_mul_right _ hU
    have key : 300 * (L + 1) * (Z + L + 10) =
        300 * (L * Z) + 300 * (L * L) + 3300 * L + 300 * Z + 3000 := by ring
    have e1 : L * (6 * L + 42) = 6 * (L * L) + 42 * L := by ring
    have e2 : L * (9 * Z + 12) = 9 * (L * Z) + 12 * L := by ring
    have e3 : 2 * L * (L + 3) = 2 * (L * L) + 6 * L := by ring
    have e4 : L * (Z + 1) = L * Z + L := by ring
    have hn4' : n4 ≤ L * (6 * L + 42) + 1 := le_trans hn4 (Nat.add_le_add_right m4 1)
    have hn5' : n5 ≤ 9 * (L + 2) + 8 := le_trans hn5 (Nat.add_le_add_right (Nat.mul_le_mul_left 9 hb5) 8)
    have hn6' : n6 ≤ 9 * Z + 8 := le_trans hn6 (Nat.add_le_add_right (Nat.mul_le_mul_left 9 hb6) 8)
    have hn7' : n7 ≤ 6 * (Z + Z) + 10 :=
      le_trans hn7 (Nat.add_le_add_right (Nat.mul_le_mul_left 6 (Nat.add_le_add hb7a hb7b)) 10)
    have hn9' : n9 ≤ L * (9 * Z + 12) + 1 := le_trans hn9 (Nat.add_le_add_right m9 1)
    have hn10' : n10 ≤ 9 * Z + 8 :=
      le_trans hn10 (Nat.add_le_add_right (Nat.mul_le_mul_left 9 hb10) 8)
    have hn11' : n11 ≤ 6 * (Z + 1) + 10 :=
      le_trans hn11 (Nat.add_le_add_right (Nat.mul_le_mul_left 6 (Nat.add_le_add_right hb11 _)) 10)
    have hn13' : n13 ≤ 9 * Z + 8 :=
      le_trans hn13 (Nat.add_le_add_right (Nat.mul_le_mul_left 9 hb13) 8)
    have hn14' : n14 ≤ 6 * (2 * L * (L + 3)) + 3 :=
      le_trans hn14 (Nat.add_le_add_right (Nat.mul_le_mul_left 6 (le_trans hb14 m14)) 3)
    have hb19' : (s18 Key.R).length ≤ L * (Z + 1) + 2 * L * (L + 3) + 4 * Z + L + 12 :=
      le_trans hb19 (by omega)
    have hn19' : n19 ≤ 3 * (L * (Z + 1) + 2 * L * (L + 3) + 4 * Z + L + 12) + 1 :=
      le_trans hn19 (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hb19') 1)
    have hn1' : n1 ≤ 6 * L + 3 := by omega
    have hn8' : n8 ≤ 6 * L + 3 := by omega
    clear_value Z
    clear * - hn1' hn4' hn5' hn6' hn7' hn8' hn9' hn10' hn11' hn13' hn14' hn19' key e1 e2 e3 e4
    rw [key]
    rw [e1] at hn4'
    rw [e2] at hn9'
    rw [e3] at hn14' hn19'
    rw [e4] at hn19'
    linarith
  · have hout : (transferStore .R (fun k => decide (k = .out)) s18) .out = (s18 .R).reverse := by
      simp [transferStore, hs18, hs17, Os, Sg]
    rw [hout, hR18]
    simp only [hg14, hg13, hg12, hg11, hg10, hg9, hg7, hg6, hg5, hR, outWord]
    have h4 : encNat 4 = [.zero, .zero, .one, .sep] := by
      have : Nat.bits 4 = [false, false, true] := by
        have h := Nat.bits_append_bit 2 false (by simp)
        rw [bits_two] at h; simpa [Nat.bit] using h
      simp [encNat, this]
    have hd : encNat (2 * (S2 + 1)) = .zero :: (eb (S2 + 1) ++ [.sep]) := by
      rw [encNat_double _ (by omega)]; rfl
    rw [h4, hd, show g.U + 2 = 2 + g.U from by ring]
    simp [encNat_eq, eb, List.reverse_append]
    have hfr := flat_rev g.U (enc (Nat.bits S2) ++ [.sep])
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append] at hfr
    rw [hfr, List.replicate_succ', List.flatten_append]
    simp [hS2]
end TDEOTD


set_option autoImplicit false

namespace TDEOTD

open CookPvsNP ProjSchedTW.Complexity GTWSched.NPC

/-! ## Facts about the register model `procG` -/

lemma procG_cons (g : G) (v : ℕ) (vs : List ℕ) : procG g (v :: vs) = procG (stepG g v) vs := rfl

lemma stepG_U (g : G) (v : ℕ) : (stepG g v).U = g.U + 1 := by
  cases hp : g.par <;> simp [stepG, hp]
lemma stepG_R (g : G) (v : ℕ) : (stepG g v).R = g.R := by
  cases hp : g.par <;> simp [stepG, hp]
lemma stepG_seen (g : G) (v : ℕ) : (stepG g v).seen = true := by
  cases hp : g.par <;> simp [stepG, hp]
lemma stepG_par (g : G) (v : ℕ) : (stepG g v).par = !g.par := by
  cases hp : g.par <;> simp [stepG, hp]
lemma stepG_prev (g : G) (v : ℕ) : (stepG g v).prev = v := by
  cases hp : g.par <;> simp [stepG, hp]
lemma stepG_i' (g : G) (v : ℕ) : (stepG g v).i = g.i := by
  cases hp : g.par <;> simp [stepG, hp]
lemma stepG_x1 (g : G) (v : ℕ) : (stepG g v).x1 = if g.seen then g.x1 else v := by
  cases hp : g.par <;> simp [stepG, hp]
lemma stepG_S (g : G) (v : ℕ) : (stepG g v).S = g.S + (v + 1) := by
  cases hp : g.par <;> simp [stepG, hp]
lemma stepG_Rl (g : G) (v : ℕ) : (stepG g v).Rl =
    .sep :: ((eb (v + 1)).reverse ++ (.zero :: (if g.seen then g.Rl else
      .sep :: ((eb v).reverse ++ (.zero :: g.Rl))))) := by
  cases hp : g.par <;> simp [stepG, hp]

lemma procG_U : ∀ (xs : List ℕ) (g : G), (procG g xs).U = g.U + xs.length := by
  intro xs; induction xs with
  | nil => intro g; rfl
  | cons v vs ih => intro g; rw [procG_cons, ih, stepG_U]; simp; omega

lemma procG_R : ∀ (xs : List ℕ) (g : G), (procG g xs).R = g.R := by
  intro xs; induction xs with
  | nil => intro g; rfl
  | cons v vs ih => intro g; rw [procG_cons, ih, stepG_R]

lemma procG_seen : ∀ (xs : List ℕ) (g : G), (procG g xs).seen = (g.seen || !xs.isEmpty) := by
  intro xs; induction xs with
  | nil => intro g; simp [procG]
  | cons v vs ih => intro g; rw [procG_cons, ih, stepG_seen]; simp

lemma procG_par : ∀ (xs : List ℕ) (g : G), (procG g xs).par = (g.par != decide (xs.length % 2 = 1)) := by
  intro xs; induction xs with
  | nil => intro g; simp [procG]
  | cons v vs ih =>
    intro g; rw [procG_cons, ih, stepG_par]
    simp only [List.length_cons]
    cases g.par <;> by_cases h : vs.length % 2 = 1 <;> simp [h] <;> omega

lemma procG_x1 : ∀ (xs : List ℕ) (g : G), g.seen = true → (procG g xs).x1 = g.x1 := by
  intro xs; induction xs with
  | nil => intro g _; rfl
  | cons v vs ih => intro g hs; rw [procG_cons, ih _ (stepG_seen g v), stepG_x1, if_pos hs]

lemma procG_S : ∀ (xs : List ℕ) (g : G), (procG g xs).S = g.S + (xs.map (· + 1)).sum := by
  intro xs; induction xs with
  | nil => intro g; simp [procG]
  | cons v vs ih => intro g; rw [procG_cons, ih, stepG_S]; simp; omega

/-- the code of the doubled number `2m` (`m > 0`) as it is pushed in reverse. -/
lemma rev_dbl (m : ℕ) (hm : 0 < m) :
    (BSym.sep :: ((eb m).reverse ++ [BSym.zero])).reverse = encNat (2 * m) := by
  rw [encNat_double m hm]; simp [eb]

lemma procG_Rl : ∀ (xs : List ℕ) (g : G), g.seen = true →
    (procG g xs).Rl.reverse = g.Rl.reverse ++ (xs.map (fun v => encNat (2 * (v + 1)))).flatten := by
  intro xs; induction xs with
  | nil => intro g _; simp [procG]
  | cons v vs ih =>
    intro g hs
    rw [procG_cons, ih _ (stepG_seen g v), stepG_Rl, if_pos hs]
    have := rev_dbl (v + 1) (by omega)
    simp only [List.reverse_cons, List.reverse_append, List.map_cons, List.flatten_cons] at this ⊢
    rw [← this]; simp

lemma procG_inv (L : ℕ) : ∀ (xs : List ℕ) (g : G), g.i = encNats xs →
    List.Chain (· < ·) g.prev xs → Inv L g → Inv L { procG g xs with i := [] } := by
  intro xs; induction xs with
  | nil =>
    intro g _ _ h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨by simp [procG]; omega, h2, h3, h4, h5, h6, h7⟩
  | cons v vs ih =>
    intro g hi hc hinv
    have hc' : g.prev < v ∧ List.Chain (· < ·) v vs := by
      cases hc with
      | cons_cons h1 h2 => exact ⟨h1, h2⟩
    clear hc
    have hc := hc'
    have hv : v ≠ 0 := by omega
    have hy : Nat.bits v ≠ [] := by
      intro h; apply hv; rw [← (canon_bits_bval v).2, h]; rfl
    have hval : bval (Nat.bits v) = v := (canon_bits_bval v).2
    have hs := inv_step hinv (Nat.bits v) (encNats vs) (by rw [hi, encNats_cons']) hy
      (by rw [hval]; exact hc.1)
    rw [hval] at hs
    have key := ih (stepG { g with i := encNats vs } v)
      (by rw [stepG_i']) (by rw [stepG_prev]; exact hc.2) hs
    have e : { procG (stepG { g with i := encNats vs } v) vs with i := [] } =
        { procG g (v :: vs) with i := [] } := by
      rw [stepG_i, procG_i, procG_cons]
    rwa [e] at key

/-! ## The threshold register `K` -/

/-- the doubled pair sums `x_{2j} + x_{2j+1} + 2` (0-based). -/
def qv (xs : List ℕ) (j : ℕ) : ℕ := xs.getD (2 * j) 0 + xs.getD (2 * j + 1) 0 + 2

/-- the closed form of `K` after `m` pairs. -/
def kForm (xs : List ℕ) (m X : ℕ) : ℕ :=
  ∑ j ∈ Finset.range m, qv xs j * (2 * m - 2 * j - 1) + 2 * m * X

lemma stepG_ff (g : G) (v : ℕ) (hp : g.par = false) :
    (stepG g v).P = g.P + (v + 1) ∧ (stepG g v).T = g.T ∧ (stepG g v).K = g.K := by
  simp [stepG, hp]

lemma stepG_tt (g : G) (v : ℕ) (hp : g.par = true) :
    (stepG g v).P = 0 ∧ (stepG g v).T = g.T + (g.P + (v + 1)) ∧
      (stepG g v).K = g.K + g.T + g.T + (g.P + (v + 1)) + (if g.seen then g.x1 else v) +
        (if g.seen then g.x1 else v) := by
  simp [stepG, hp]

lemma qv_cons2 (a b : ℕ) (r : List ℕ) (j : ℕ) : qv (a :: b :: r) (j + 1) = qv r j := by
  simp only [qv, show 2 * (j + 1) = 2 * j + 1 + 1 by ring, show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring,
    List.getD_cons_succ]

lemma qv_cons2_zero (a b : ℕ) (r : List ℕ) : qv (a :: b :: r) 0 = a + b + 2 := by
  simp [qv]

lemma kForm_cons2 (a b : ℕ) (r : List ℕ) (m X : ℕ) :
    kForm (a :: b :: r) (m + 1) X = kForm r m X + (a + b + 2) * (2 * m + 1) + 2 * X := by
  unfold kForm
  rw [Finset.sum_range_succ', qv_cons2_zero]
  have : ∑ j ∈ Finset.range m, qv (a :: b :: r) (j + 1) * (2 * (m + 1) - 2 * (j + 1) - 1) =
      ∑ j ∈ Finset.range m, qv r j * (2 * m - 2 * j - 1) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [qv_cons2]; congr 1; omega
  rw [this]
  have e : 2 * (m + 1) - 2 * 0 - 1 = 2 * m + 1 := by omega
  rw [e]; ring

lemma procG_pairs : ∀ (m : ℕ) (ys : List ℕ) (g : G), ys.length = 2 * m → g.par = false →
    g.P = 0 → g.seen = true →
    (procG g ys).K = g.K + 2 * m * g.T + kForm ys m g.x1 := by
  intro m
  induction m with
  | zero =>
    intro ys g hl _ _ _
    have : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [procG, kForm]
  | succ m ih =>
    intro ys g hl hp hP hs
    obtain ⟨a, b, r, rfl⟩ : ∃ a b r, ys = a :: b :: r := by
      rcases ys with _ | ⟨a, _ | ⟨b, r⟩⟩
      · simp at hl
      · simp at hl; omega
      · exact ⟨a, b, r, rfl⟩
    simp only [List.length_cons] at hl
    set g1 := stepG g a with hg1
    set g2 := stepG g1 b with hg2
    have hp1 : g1.par = true := by rw [hg1, stepG_par, hp]; rfl
    obtain ⟨hP1, hT1, hK1⟩ := stepG_ff g a hp
    have hs1 : g1.seen = true := stepG_seen g a
    have hx1 : g1.x1 = g.x1 := by rw [hg1, stepG_x1, if_pos hs]
    obtain ⟨hP2, hT2, hK2⟩ := stepG_tt g1 b hp1
    have hp2 : g2.par = false := by rw [hg2, stepG_par, hp1]; rfl
    have hs2 : g2.seen = true := stepG_seen g1 b
    have hx2 : g2.x1 = g.x1 := by rw [hg2, stepG_x1, if_pos hs1, hx1]
    have key := ih r g2 (by omega) hp2 hP2 hs2
    rw [procG_cons, procG_cons, ← hg1, ← hg2, key, kForm_cons2, hx2, hK2, hT2]
    rw [if_pos hs1, hx1, hK1, hT1, hP1, hP]
    ring

/-! ## Rescaling and re-indexing total discrepancy instances -/

lemma tdYes_scale {N : ℕ} (l M : Fin N → ℝ) (k : ℝ) :
    TDYesReal (fun i => 2 * l i) (fun i => 2 * M i) (2 * k) ↔ TDYesReal l M k := by
  constructor
  · rintro ⟨s, ⟨h0, hov⟩, hc⟩
    refine ⟨fun i => s i / 2, ⟨fun i => by have := h0 i; positivity, fun i j hij => ?_⟩, ?_⟩
    · rcases hov i j hij with h | h
      · left; simp only at h ⊢; linarith
      · right; simp only at h ⊢; linarith
    · unfold midCost mid at hc ⊢
      have : ∑ i, |s i + 2 * l i / 2 - 2 * M i| = 2 * ∑ i, |s i / 2 + l i / 2 - M i| := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [show s i + 2 * l i / 2 - 2 * M i = 2 * (s i / 2 + l i / 2 - M i) by ring, abs_mul]
        norm_num
      linarith
  · rintro ⟨s, ⟨h0, hov⟩, hc⟩
    refine ⟨fun i => 2 * s i, ⟨fun i => by have := h0 i; positivity, fun i j hij => ?_⟩, ?_⟩
    · rcases hov i j hij with h | h
      · left; simp only; linarith
      · right; simp only; linarith
    · unfold midCost mid at hc ⊢
      have : ∑ i, |2 * s i + 2 * l i / 2 - 2 * M i| = 2 * ∑ i, |s i + l i / 2 - M i| := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [show 2 * s i + 2 * l i / 2 - 2 * M i = 2 * (s i + l i / 2 - M i) by ring, abs_mul]
        norm_num
      linarith

lemma tdYes_cast {N N' : ℕ} (h : N = N') (l M : Fin N' → ℝ) (k : ℝ) :
    TDYesReal (fun i : Fin N => l (Fin.cast h i)) (fun i => M (Fin.cast h i)) k ↔ TDYesReal l M k := by
  subst h; rfl

/-! ## Shifting an even-odd instance by one -/

def partner (p : ℕ) : ℕ := if p % 2 = 0 then p + 1 else p - 1

lemma partner_props (p : ℕ) : partner p ≠ p ∧ partner p / 2 = p / 2 ∧ partner (partner p) = p := by
  unfold partner; split_ifs <;> omega

lemma eo_card {x : List ℕ} (hx : Even x.length) (X : Finset (Fin x.length))
    (hX : ∀ p q : Fin x.length, p ≠ q → p.val / 2 = q.val / 2 → (p ∈ X ↔ q ∉ X)) :
    X.card = Xᶜ.card := by
  obtain ⟨n, hn⟩ := hx
  have hlt : ∀ p : Fin x.length, partner p.val < x.length := by
    intro p; have := p.isLt; unfold partner; split_ifs <;> omega
  let f : Fin x.length → Fin x.length := fun p => ⟨partner p.val, hlt p⟩
  have hf : ∀ p, f p ≠ p ∧ (f p).val / 2 = p.val / 2 ∧ f (f p) = p := by
    intro p
    obtain ⟨h1, h2, h3⟩ := partner_props p.val
    refine ⟨fun e => h1 (congrArg Fin.val e), h2, Fin.ext h3⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have := congrArg f hab
    rwa [(hf a).2.2, (hf b).2.2] at this
  apply le_antisymm
  · apply Finset.card_le_card_of_injOn f
    · intro p hp
      simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hp ⊢
      exact (hX p (f p) (fun e => (hf p).1 e.symm) (hf p).2.1.symm).1 hp
    · exact hinj.injOn
  · apply Finset.card_le_card_of_injOn f
    · intro p hp
      simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hp ⊢
      by_contra hc
      exact hp ((hX p (f p) (fun e => (hf p).1 e.symm) (hf p).2.1.symm).2 hc)
    · exact hinj.injOn

lemma eoYes_shift (x : List ℕ) (hx : Even x.length) :
    EOYes (x.map (· + 1)) ↔ EOYes x := by
  have hlen : (x.map (· + 1)).length = x.length := List.length_map _
  set e : Fin x.length ≃ Fin (x.map (· + 1)).length := finCongr hlen.symm with he
  have hget : ∀ p : Fin x.length, (x.map (· + 1)).get (e p) = x.get p + 1 := by
    intro p; simp [he]
  have hsum : ∀ Y : Finset (Fin x.length),
      ∑ q ∈ Y.map e.toEmbedding, (x.map (· + 1)).get q = ∑ p ∈ Y, x.get p + Y.card := by
    intro Y
    rw [Finset.sum_map]
    simp only [Equiv.coe_toEmbedding, hget, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
      mul_one]
  have hcompl : ∀ Y : Finset (Fin x.length), (Y.map e.toEmbedding)ᶜ = Yᶜ.map e.toEmbedding := by
    intro Y; ext q
    simp only [Finset.mem_compl, Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · intro h; exact ⟨e.symm q, fun hm => h ⟨e.symm q, hm, by simp⟩, by simp⟩
    · rintro ⟨p, hp, rfl⟩ ⟨p', hp', he'⟩
      exact hp (e.injective he' ▸ hp')
  have hval : ∀ p : Fin x.length, (e p).val = p.val := by intro p; simp [he]
  constructor
  · rintro ⟨X, hX, hs⟩
    set Y := X.map e.symm.toEmbedding with hY
    have hXY : X = Y.map e.toEmbedding := by
      ext q; simp [hY]
    have hYc : ∀ p q : Fin x.length, p ≠ q → p.val / 2 = q.val / 2 → (p ∈ Y ↔ q ∉ Y) := by
      intro p q hpq hd
      have := hX (e p) (e q) (fun h => hpq (e.injective h)) (by rw [hval, hval]; exact hd)
      rw [hXY] at this
      simpa using this
    refine ⟨Y, hYc, ?_⟩
    rw [hXY, hcompl, hsum, hsum] at hs
    have := eo_card hx Y hYc
    omega
  · rintro ⟨Y, hY, hs⟩
    refine ⟨Y.map e.toEmbedding, ?_, ?_⟩
    · intro p q hpq hd
      have h := hY (e.symm p) (e.symm q) (fun h => hpq (e.symm.injective h))
        (by have := hval (e.symm p); have := hval (e.symm q); simp at *; omega)
      simp only [Finset.mem_map, Equiv.coe_toEmbedding]
      constructor
      · rintro ⟨p', hp', rfl⟩ ⟨q', hq', hq''⟩
        have : e.symm q = q' := by rw [← hq'']; simp
        rw [this] at h; simp at h; exact h.1 hp' hq'
      · intro hq
        refine ⟨e.symm p, ?_, by simp⟩
        rw [h]; intro hq'; exact hq ⟨e.symm q, hq', by simp⟩
    · rw [hcompl, hsum, hsum, eo_card hx Y hY, hs]

/-! ## The instance written by the machine -/

def aOf (xs : List ℕ) : ℕ := xs.getD 0 0
def SOf (xs : List ℕ) : ℕ := (xs.map (· + 1)).sum
def Mlist (xs : List ℕ) : List ℕ :=
  List.replicate (xs.length + 1) (SOf xs + aOf xs) ++ [2 * (SOf xs + aOf xs + 1)]
def llist (xs : List ℕ) : List ℕ := 2 * aOf xs :: (xs.map (fun v => 2 * (v + 1)) ++ [4])
def Mf (xs : List ℕ) (j : Fin (xs.length + 2)) : ℕ := (Mlist xs).getD j 0
def lf (xs : List ℕ) (j : Fin (xs.length + 2)) : ℕ := (llist xs).getD j 0
def Kv (xs : List ℕ) : ℕ := kForm xs (xs.length / 2) (aOf xs)

lemma Mlist_length (xs : List ℕ) : (Mlist xs).length = xs.length + 2 := by simp [Mlist]
lemma llist_length (xs : List ℕ) : (llist xs).length = xs.length + 2 := by simp [llist]

lemma ofFn_getD (L : List ℕ) (N : ℕ) (h : L.length = N) :
    List.ofFn (fun j : Fin N => L.getD j 0) = L := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, h2]

lemma sum_range_getD (L : List ℕ) : ∑ i ∈ Finset.range L.length, (L.getD i 0 : ℝ) = (L.sum : ℝ) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.sum_cons]
    rw [ih]; push_cast; ring

lemma getD_map_succ (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    (xs.map (· + 1)).getD i 0 = xs.getD i 0 + 1 := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma lf_eq (xs : List ℕ) (hx : EOInstance xs) (h : xs.length + 2 = 2 * ((xs.map (· + 1)).length / 2) + 2)
    (j : Fin (xs.length + 2)) :
    (lf xs j : ℝ) = 2 * dLen (xs.map (· + 1)) (Fin.cast h j) := by
  obtain ⟨hev, hpos, hall, -⟩ := hx
  have hlen : (xs.map (· + 1)).length = xs.length := List.length_map _
  have hn : 2 * ((xs.map (· + 1)).length / 2) = xs.length := by
    rw [hlen]; obtain ⟨m, hm⟩ := hev; omega
  unfold lf dLen
  simp only [Fin.val_cast]
  rcases Nat.eq_zero_or_pos j.val with h0 | h0
  · rw [if_pos h0, h0]
    rw [getD_map_succ xs 0 hpos]
    simp [llist, aOf]
  · rw [if_neg (by omega)]
    by_cases hj : j.val ≤ 2 * ((xs.map (· + 1)).length / 2)
    · rw [if_pos hj, getD_map_succ xs _ (by omega)]
      obtain ⟨i, hi⟩ : ∃ i, j.val = i + 1 := ⟨j.val - 1, by omega⟩
      rw [hi]
      simp only [llist, List.getD_cons_succ, Nat.add_sub_cancel]
      rw [List.getD_append _ _ _ _ (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, show i < xs.length by omega]
    · rw [if_neg hj]
      have hj' : j.val = xs.length + 1 := by have := j.isLt; omega
      rw [hj']
      simp only [llist, List.getD_cons_succ]
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp; norm_num

lemma dM_eq (xs : List ℕ) (hx : EOInstance xs) :
    2 * dM (xs.map (· + 1)) = (SOf xs : ℝ) + aOf xs := by
  obtain ⟨hev, hpos, hall, -⟩ := hx
  have hlen : (xs.map (· + 1)).length = xs.length := List.length_map _
  have hn : 2 * ((xs.map (· + 1)).length / 2) = xs.length := by
    rw [hlen]; obtain ⟨m, hm⟩ := hev; omega
  unfold dM
  rw [Finset.mul_sum, Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.coe_castSucc, Fin.val_succ]
  unfold dLen
  simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_zero, if_true, Nat.add_one_ne_zero, if_false]
  rw [getD_map_succ xs 0 hpos]
  have hs : ∀ i : Fin (2 * ((xs.map (· + 1)).length / 2)),
      2 * ((if (i : ℕ) + 1 ≤ 2 * ((xs.map (· + 1)).length / 2) then
        (((xs.map (· + 1)).getD ((i : ℕ) + 1 - 1) 0 : ℕ) : ℝ) else 2) / 2) =
        ((xs.getD i 0 : ℕ) : ℝ) + 1 := by
    intro i
    rw [if_pos (by have := i.isLt; omega), Nat.add_sub_cancel,
      getD_map_succ xs _ (by have := i.isLt; omega)]
    push_cast; ring
  rw [Finset.sum_congr rfl (fun i _ => hs i)]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((xs.getD i 0 : ℕ) : ℝ) + 1), hn, Finset.sum_add_distrib,
    sum_range_getD]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  unfold SOf aOf
  have : (((xs.map (· + 1)).sum : ℕ) : ℝ) = (xs.sum : ℝ) + xs.length := by
    have h1 : (xs.map (· + 1)).sum = xs.sum + xs.length := by
      induction xs with
      | nil => simp
      | cons a xs ih => simp [List.sum_cons]; omega
    rw [h1]; push_cast; ring
  rw [this]; push_cast; ring

lemma dLen_last (x : List ℕ) : dLen x (Fin.last _) = 2 := by
  unfold dLen; simp

lemma Mf_eq (xs : List ℕ) (hx : EOInstance xs) (h : xs.length + 2 = 2 * ((xs.map (· + 1)).length / 2) + 2)
    (j : Fin (xs.length + 2)) :
    (Mf xs j : ℝ) = 2 * dMid (xs.map (· + 1)) (Fin.cast h j) := by
  have hdM := dM_eq xs hx
  obtain ⟨hev, hpos, hall, -⟩ := hx
  have hlen : (xs.map (· + 1)).length = xs.length := List.length_map _
  have hn : 2 * ((xs.map (· + 1)).length / 2) = xs.length := by
    rw [hlen]; obtain ⟨m, hm⟩ := hev; omega
  unfold Mf dMid
  simp only [Fin.val_cast]
  by_cases hj : j.val ≤ 2 * ((xs.map (· + 1)).length / 2)
  · rw [if_pos hj, hdM]
    simp only [Mlist]
    rw [List.getD_append _ _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, show j.val < xs.length + 1 by omega]
  · rw [if_neg hj, dLen_last]
    have hj' : j.val = xs.length + 1 := by have := j.isLt; omega
    simp only [Mlist, hj']
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_replicate, Nat.sub_self, List.getD_cons_zero]
    have : 2 * (2 * dM (xs.map (· + 1)) + 2 / 2) = 2 * (2 * dM (xs.map (· + 1))) + 2 := by ring
    rw [this, hdM]; push_cast; ring

lemma K_eq (xs : List ℕ) (hx : EOInstance xs) : (Kv xs : ℝ) = 2 * dK (xs.map (· + 1)) := by
  obtain ⟨hev, hpos, hall, -⟩ := hx
  have hlen : (xs.map (· + 1)).length = xs.length := List.length_map _
  have hn2 : 2 * ((xs.map (· + 1)).length / 2) = xs.length := by
    rw [hlen]; obtain ⟨m, hm⟩ := hev; omega
  have hKv : Kv xs = kForm xs ((xs.map (· + 1)).length / 2) (aOf xs) := by
    unfold Kv; rw [hlen]
  rw [hKv]
  unfold dK kStar kForm
  beta_reduce
  have hl0 : dLen (xs.map (· + 1))
      (Fin.castSucc (0 : Fin (2 * ((xs.map (· + 1)).length / 2) + 1))) = (aOf xs : ℝ) := by
    unfold dLen
    simp only [Fin.coe_castSucc, Fin.val_zero, if_true]
    rw [getD_map_succ xs 0 hpos]; unfold aOf; push_cast; ring
  rw [hl0]
  have hterm : ∀ j : Fin ((xs.map (· + 1)).length / 2),
      (dLen (xs.map (· + 1)) (evenTask j).castSucc + dLen (xs.map (· + 1)) (oddTask j).castSucc) *
        ((((xs.map (· + 1)).length / 2 : ℕ) : ℝ) - (j : ℝ) - 1 / 2) =
        ((qv xs j * (2 * ((xs.map (· + 1)).length / 2) - 2 * j - 1) : ℕ) : ℝ) / 2 := by
    intro j
    have hj := j.isLt
    unfold dLen evenTask oddTask
    simp only [Fin.coe_castSucc]
    rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega),
      show 2 * (j : ℕ) + 2 - 1 = 2 * j + 1 by omega, show 2 * (j : ℕ) + 1 - 1 = 2 * j by omega,
      getD_map_succ xs _ (by omega), getD_map_succ xs _ (by omega)]
    unfold qv
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_div,
    Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      ((qv xs j * (2 * ((xs.map (· + 1)).length / 2) - 2 * j - 1) : ℕ) : ℝ))]
  push_cast; ring

lemma eoInst_shift (xs : List ℕ) (hx : EOInstance xs) : EOInstance (xs.map (· + 1)) := by
  obtain ⟨hev, hpos, hall, hpw⟩ := hx
  refine ⟨by simpa using hev, by simpa using hpos, ?_, ?_⟩
  · intro v hv; simp only [List.mem_map] at hv; obtain ⟨u, -, rfl⟩ := hv; omega
  · rw [List.pairwise_map]; exact hpw.imp (fun h => by omega)

theorem inst_iff (xs : List ℕ) (hx : EOInstance xs) :
    TDYesReal (fun j => ((lf xs j : ℕ) : ℝ)) (fun j => ((Mf xs j : ℕ) : ℝ)) ((Kv xs : ℕ) : ℝ) ↔
      EOYes xs := by
  have hx' := eoInst_shift xs hx
  have hlen : (xs.map (· + 1)).length = xs.length := List.length_map _
  have h : xs.length + 2 = 2 * ((xs.map (· + 1)).length / 2) + 2 := by
    rw [hlen]; obtain ⟨m, hm⟩ := hx.1; omega
  have hx1 : 1 < (xs.map (· + 1)).getD 0 0 := by
    rw [getD_map_succ xs 0 hx.2.1]
    have := hx.2.2.1 (xs.getD 0 0) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx.2.1]; simp)
    omega
  have e1 : (fun j => ((lf xs j : ℕ) : ℝ)) = fun j => 2 * dLen (xs.map (· + 1)) (Fin.cast h j) :=
    funext (lf_eq xs hx h)
  have e2 : (fun j => ((Mf xs j : ℕ) : ℝ)) = fun j => 2 * dMid (xs.map (· + 1)) (Fin.cast h j) :=
    funext (Mf_eq xs hx h)
  rw [e1, e2, K_eq xs hx, tdYes_scale (fun j => dLen (xs.map (· + 1)) (Fin.cast h j))
    (fun j => dMid (xs.map (· + 1)) (Fin.cast h j)), tdYes_cast h,
    ← theorem_1_reduction _ hx' hx1, eoYes_shift xs hx.1]

/-! ## The run from the initial registers -/

def g0 (w : List BSym) : G :=
  { i := w, prev := 0, x1 := 0, S := 0, P := 0, T := 0, K := 0, U := 0, par := false,
    seen := false, Rl := [], R := [] }

lemma g0_store (w : List BSym) : (fun j => if j = Key.inp then w else []) = Sg (g0 w) [] [] [] [] := by
  funext k; cases k <;> simp [Sg, g0, eb, enc, fl, Nat.bits]

lemma run_x1 (w : List BSym) (a : ℕ) (r : List ℕ) : (procG (g0 w) (a :: r)).x1 = a := by
  rw [procG_cons, procG_x1 _ _ (stepG_seen _ _), stepG_x1]; simp [g0]

lemma run_Rl (w : List BSym) (a : ℕ) (r : List ℕ) (ha : 0 < a) :
    (procG (g0 w) (a :: r)).Rl.reverse =
      encNat (2 * a) ++ ((a :: r).map (fun v => encNat (2 * (v + 1)))).flatten := by
  rw [procG_cons, procG_Rl _ _ (stepG_seen _ _), stepG_Rl]
  simp only [g0, Bool.false_eq_true, if_false]
  have h1 := rev_dbl a ha
  have h2 := rev_dbl (a + 1) (by omega)
  simp only [List.reverse_cons, List.reverse_append, List.reverse_nil, List.nil_append,
    List.map_cons, List.flatten_cons, List.append_assoc] at h1 h2 ⊢
  rw [← h1, ← h2]; simp

lemma run_K (w : List BSym) (xs : List ℕ) (m : ℕ) (hl : xs.length = 2 * (m + 1)) :
    (procG (g0 w) xs).K = kForm xs (m + 1) (aOf xs) := by
  obtain ⟨a, b, r, rfl⟩ : ∃ a b r, xs = a :: b :: r := by
    rcases xs with _ | ⟨a, _ | ⟨b, r⟩⟩
    · simp at hl
    · simp at hl; omega
    · exact ⟨a, b, r, rfl⟩
  simp only [List.length_cons] at hl
  set g1 := stepG (g0 w) a with hg1
  set g2 := stepG g1 b with hg2
  have hp1 : g1.par = true := by rw [hg1, stepG_par]; rfl
  obtain ⟨hP1, hT1, hK1⟩ := stepG_ff (g0 w) a rfl
  have hs1 : g1.seen = true := stepG_seen _ a
  have hx1 : g1.x1 = a := by rw [hg1, stepG_x1]; simp [g0]
  obtain ⟨hP2, hT2, hK2⟩ := stepG_tt g1 b hp1
  have hp2 : g2.par = false := by rw [hg2, stepG_par, hp1]; rfl
  have hs2 : g2.seen = true := stepG_seen g1 b
  have hx2 : g2.x1 = a := by rw [hg2, stepG_x1, if_pos hs1, hx1]
  rw [procG_cons, procG_cons, ← hg1, ← hg2, procG_pairs m r g2 (by omega) hp2 hP2 hs2,
    kForm_cons2, hx2, hK2, hT2, if_pos hs1, hx1, hK1, hT1, hP1]
  simp only [g0, aOf, List.getD_cons_zero]
  ring

lemma kForm_pos (xs : List ℕ) (m : ℕ) (X : ℕ) (hX : 0 < X) : 0 < kForm xs (m + 1) X := by
  unfold kForm; positivity

lemma encNats_replicate (n v : ℕ) : encNats (List.replicate n v) = (List.replicate n (encNat v)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.replicate_succ, List.flatten_cons, ← ih]; simp [encNats]

lemma encNats_map (xs : List ℕ) (f : ℕ → ℕ) :
    encNats (xs.map f) = (xs.map (fun v => encNat (f v))).flatten := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons, List.flatten_cons, ← ih]; simp [encNats]

lemma ofFn_Mf (xs : List ℕ) : List.ofFn (Mf xs) = Mlist xs :=
  ofFn_getD (Mlist xs) _ (Mlist_length xs)

lemma ofFn_lf (xs : List ℕ) : List.ofFn (lf xs) = llist xs :=
  ofFn_getD (llist xs) _ (llist_length xs)

lemma outWord_eq (w : List BSym) (xs : List ℕ) (hx : EOInstance xs) :
    outWord { procG (g0 w) xs with i := [] } = tdCode (xs.length + 2) (Kv xs) (Mf xs) (lf xs) := by
  obtain ⟨hev, hpos, hall, -⟩ := hx
  obtain ⟨a, r, rfl⟩ : ∃ a r, xs = a :: r := by
    rcases xs with _ | ⟨a, r⟩
    · simp at hpos
    · exact ⟨a, r, rfl⟩
  have ha : 0 < a := hall a (by simp)
  obtain ⟨m, hm⟩ : ∃ m, (a :: r).length = 2 * (m + 1) := by
    obtain ⟨k, hk⟩ := hev; exact ⟨k - 1, by simp at hk ⊢; omega⟩
  have hU := procG_U (a :: r) (g0 w)
  have hK := run_K w (a :: r) m hm
  have hS := procG_S (a :: r) (g0 w)
  have hx1 := run_x1 w a r
  have hRl := run_Rl w a r ha
  have hKv : Kv (a :: r) = kForm (a :: r) (m + 1) (aOf (a :: r)) := by
    unfold Kv; rw [hm]; congr 1; omega
  unfold outWord tdCode
  simp only [hU, hK, hS, hx1, hRl]
  rw [ofFn_Mf, ofFn_lf, hKv]
  simp only [g0, zero_add, Mlist, llist, SOf, aOf, List.getD_cons_zero]
  simp only [encNats, List.flatMap_cons, List.flatMap_append, List.append_assoc]
  rw [show List.flatMap encNat (List.replicate ((a :: r).length + 1) ((List.map (· + 1) (a :: r)).sum + a)) =
    encNats (List.replicate ((a :: r).length + 1) ((List.map (· + 1) (a :: r)).sum + a)) from rfl,
    encNats_replicate,
    show List.flatMap encNat (List.map (fun v => 2 * (v + 1)) (a :: r)) =
      encNats (List.map (fun v => 2 * (v + 1)) (a :: r)) from rfl, encNats_map]
  simp

namespace Inj

lemma encInts_cons (z : ℤ) (l : List ℤ) : encInts (z :: l) = encInt z ++ encInts l := by
  simp [encInts]

def bval' : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bval' l)

lemma bval'_bits (n : ℕ) : bval' (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bval']
  | bit b n hn ih => rw [Nat.bits_append_bit _ _ hn]; simp [bval', ih]

lemma sep_split_inj : ∀ {u u' R R' : List BSym}, BSym.sep ∉ u → BSym.sep ∉ u' →
    u ++ BSym.sep :: R = u' ++ BSym.sep :: R' → u = u' ∧ R = R' := by
  intro u
  induction u with
  | nil =>
    intro u' R R' _ hu' h
    rcases u' with _ | ⟨a, u'⟩
    · simpa using h
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hu'
  | cons a u ih =>
    intro u' R R' hu hu' h
    rcases u' with _ | ⟨b, u'⟩
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hu
    · simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := ih (fun hm => hu (List.mem_cons_of_mem _ hm))
        (fun hm => hu' (List.mem_cons_of_mem _ hm)) h.2
      exact ⟨by rw [h.1, h1], h2⟩

def digU (z : ℤ) : List BSym :=
  (if z < 0 then [BSym.minus] else []) ++
    (Nat.bits z.natAbs).map (fun b => if b then BSym.one else BSym.zero)

lemma encInt_eq_digU (z : ℤ) : encInt z = digU z ++ [BSym.sep] := by
  simp [encInt, encNat, digU]

lemma sep_not_mem_digU (z : ℤ) : BSym.sep ∉ digU z := by
  simp only [digU, List.mem_append, List.mem_map, not_or]
  constructor
  · split_ifs <;> simp
  · rintro ⟨b, -, hb⟩; cases b <;> simp at hb

lemma map_bits_inj {a b : List Bool}
    (h : a.map (fun b => if b then BSym.one else BSym.zero) =
      b.map (fun b => if b then BSym.one else BSym.zero)) : a = b := by
  refine List.map_injective_iff.mpr ?_ h
  intro x y hxy; cases x <;> cases y <;> simp_all

lemma digU_inj {z z' : ℤ} (h : digU z = digU z') : z = z' := by
  have key : ∀ {z z' : ℤ}, digU z = digU z' → (z < 0 ↔ z' < 0) := by
    intro z z' h
    by_contra hne
    simp only [digU] at h
    rcases lt_or_ge z 0 with hz | hz <;> rcases lt_or_ge z' 0 with hz' | hz'
    · exact hne (iff_of_true hz hz')
    · rw [if_pos hz, if_neg (not_lt.2 hz')] at h
      cases hb : Nat.bits z'.natAbs with
      | nil => rw [hb] at h; simp at h
      | cons c l => rw [hb] at h; cases c <;> simp at h
    · rw [if_neg (not_lt.2 hz), if_pos hz'] at h
      cases hb : Nat.bits z.natAbs with
      | nil => rw [hb] at h; simp at h
      | cons c l => rw [hb] at h; cases c <;> simp at h
    · exact hne (iff_of_false (not_lt.2 hz) (not_lt.2 hz'))
  have hs := key h
  have habs : z.natAbs = z'.natAbs := by
    simp only [digU] at h
    by_cases hz : z < 0
    · rw [if_pos hz, if_pos (hs.1 hz)] at h
      simp only [List.singleton_append, List.cons.injEq, true_and] at h
      rw [← bval'_bits z.natAbs, ← bval'_bits z'.natAbs, map_bits_inj h]
    · rw [if_neg hz, if_neg (fun h' => hz (hs.2 h'))] at h
      simp only [List.nil_append] at h
      rw [← bval'_bits z.natAbs, ← bval'_bits z'.natAbs, map_bits_inj h]
  omega

lemma encInts_inj : ∀ (l l' : List ℤ), encInts l = encInts l' → l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' h
    rcases l' with _ | ⟨z, l'⟩
    · rfl
    · rw [encInts_cons, encInt_eq_digU] at h; simp [encInts] at h
  | cons z l ih =>
    intro l' h
    rcases l' with _ | ⟨z', l'⟩
    · rw [encInts_cons, encInt_eq_digU] at h; simp [encInts] at h
    · rw [encInts_cons, encInts_cons, encInt_eq_digU, encInt_eq_digU] at h
      simp only [List.append_assoc, List.singleton_append] at h
      obtain ⟨h1, h2⟩ := sep_split_inj (sep_not_mem_digU z) (sep_not_mem_digU z') h
      rw [digU_inj h1, ih l' h2]

lemma none_split_inj {α β : Type} : ∀ {w w' : List α} {y y' : List β},
    w.map (some ∘ Sum.inl) ++ (none : Option (α ⊕ β)) :: y.map (some ∘ Sum.inr) =
      w'.map (some ∘ Sum.inl) ++ none :: y'.map (some ∘ Sum.inr) → w = w' ∧ y = y' := by
  intro w
  induction w with
  | nil =>
    intro w' y y' h
    rcases w' with _ | ⟨a, w'⟩
    · simp only [List.map_nil, List.nil_append, List.cons.injEq, true_and] at h
      exact ⟨rfl, List.map_injective_iff.2 (fun a b hab => by
        simpa using hab) h⟩
    · simp at h
  | cons a w ih =>
    intro w' y y' h
    rcases w' with _ | ⟨b, w'⟩
    · simp at h
    · simp only [List.map_cons, List.cons_append, List.cons.injEq, Function.comp_apply,
        Option.some.injEq, Sum.inl.injEq] at h
      obtain ⟨h1, h2⟩ := ih h.2
      exact ⟨by rw [h.1, h1], h2⟩

lemma encNats_eq (d : List ℕ) : encNats d = encInts (d.map (fun k : ℕ => (k : ℤ))) := by
  induction d with
  | nil => rfl
  | cons a d ih =>
    simp only [encNats, List.flatMap_cons, List.map_cons, encInts] at ih ⊢
    rw [ih]
    simp [encInt]

lemma encNats_inj {d d' : List ℕ} (h : encNats d = encNats d') : d = d' := by
  rw [encNats_eq, encNats_eq] at h
  exact (List.map_injective_iff.2 (Nat.cast_injective (R := ℤ))) (encInts_inj _ _ h)


end Inj

theorem poly_gen (c d : ℕ) : ∃ K, ∀ n : ℕ, c * (n + 1) ^ d ≤ n ^ K + K := by
  refine ⟨c * (c * 2 ^ d + 1) ^ d + d + 1, fun n => ?_⟩
  by_cases hn : n ≤ c * 2 ^ d
  · have h1 : c * (n + 1) ^ d ≤ c * (c * 2 ^ d + 1) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega
  · push Not at hn
    have hn1 : 1 ≤ n := by omega
    have h2 : (n + 1) ^ d ≤ (2 * n) ^ d := Nat.pow_le_pow_left (by omega) _
    have h3 : c * (n + 1) ^ d ≤ c * 2 ^ d * n ^ d := by
      calc c * (n + 1) ^ d ≤ c * (2 * n) ^ d := Nat.mul_le_mul_left _ h2
        _ = c * 2 ^ d * n ^ d := by rw [mul_pow, mul_assoc]
    have h4 : c * 2 ^ d * n ^ d ≤ n * n ^ d := Nat.mul_le_mul_right _ hn.le
    have h5 : n * n ^ d = n ^ (d + 1) := by ring
    have h6 : n ^ (d + 1) ≤ n ^ (c * (c * 2 ^ d + 1) ^ d + d + 1) :=
      Nat.pow_le_pow_right hn1 (by omega)
    omega


/-! ## The whole reduction machine -/

lemma bndEO (L : ℕ) : (L + 1) * (1600 * L + 4300) + 300 * (L + 1) * (4 * L + 17) + 2 ≤
    20000 * (L + 1) ^ 2 := by
  ring_nf; omega

def finalP : StackProg Key BSym :=
  .branch (fun h => (h .bad).isNone && (h .par).isNone && (h .seen).isSome) outP skipP

def eoProg : StackProg Key BSym := .seq mainLoop finalP

open Classical in
noncomputable def F (w : List BSym) : List BSym :=
  if h : ∃ xs, w = encNats xs ∧ EOInstance xs then
    tdCode (h.choose.length + 2) (Kv h.choose) (Mf h.choose) (lf h.choose) else []

lemma F_of (w : List BSym) (xs : List ℕ) (hw : w = encNats xs) (hx : EOInstance xs) :
    F w = tdCode (xs.length + 2) (Kv xs) (Mf xs) (lf xs) := by
  have h : ∃ xs, w = encNats xs ∧ EOInstance xs := ⟨xs, hw, hx⟩
  unfold F; rw [dif_pos h]
  have : h.choose = xs := Inj.encNats_inj (h.choose_spec.1.symm.trans hw)
  rw [this]

lemma F_none (w : List BSym) (h : ¬ ∃ xs, w = encNats xs ∧ EOInstance xs) : F w = [] := by
  unfold F; rw [dif_neg h]

lemma eoInst_iff (xs : List ℕ) :
    EOInstance xs ↔ List.Chain (· < ·) 0 xs ∧ Even xs.length ∧ xs ≠ [] := by
  rw [show List.Chain (· < ·) 0 xs ↔ List.Pairwise (· < ·) (0 :: xs) from
    List.isChain_iff_pairwise, List.pairwise_cons]
  unfold EOInstance
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h3, h4⟩, h1, List.ne_nil_of_length_pos h2⟩
  · rintro ⟨⟨h3, h4⟩, h1, h2⟩; exact ⟨h1, List.length_pos_of_ne_nil h2, h3, h4⟩

lemma inv_g0 (w : List BSym) : Inv w.length (g0 w) := by
  refine ⟨by simp [g0], by simp [g0], by simp [g0], by simp [g0], by simp [g0], by simp [g0],
    by simp [g0]⟩

set_option maxHeartbeats 1000000 in
theorem run_eo (w : List BSym) : ∃ s n, n ≤ 20000 * (w.length + 1) ^ 2 ∧
    eoProg.Exec (fun j => if j = Key.inp then w else []) s n ∧ s .out = F w := by
  rw [g0_store]
  set L := w.length with hL
  obtain ⟨t, n1, hn1, e1, hsucc, hfail⟩ := loop_all L w.length (g0 w) le_rfl (inv_g0 w)
  have hgi : (g0 w).i.length = L := rfl
  rw [hgi] at hn1
  by_cases hs : ∃ xs : List ℕ, (g0 w).i = encNats xs ∧ List.Chain (· < ·) (g0 w).prev xs
  · obtain ⟨xs, hxs, hch⟩ := hs
    have ht := hsucc xs hxs hch
    set g1 := { procG (g0 w) xs with i := [] } with hg1
    have hinv := procG_inv L xs (g0 w) hxs hch (inv_g0 w)
    by_cases hgood : Even xs.length ∧ xs ≠ []
    · have hpar : g1.par = false := by
        simp only [hg1, procG_par]
        have : xs.length % 2 = 0 := Nat.even_iff.1 hgood.1
        simp [g0, this]
      have hseen : g1.seen = true := by
        simp only [hg1, procG_seen]
        simp [g0, hgood.2]
      obtain ⟨hv1, hv2, hv3, hv4, hv5, hv6⟩ := inv_vals hinv
      obtain ⟨hi1, -, -, -, -, -, hi7⟩ := hinv
      obtain ⟨t2, n2, hn2, e2, hout⟩ := exec_outP g1 (Vb L) L (by simpa using hi1) hv3 hv2 hv6
        hi7 (by simp [hg1, procG_R, g0])
      refine ⟨t2, n1 + 1 + (1 + n2), ?_, StackProg.Exec.seq e1 (StackProg.Exec.branchTrue ?_ ?_), ?_⟩
      · have h1 := size_Vb L
        have h2 : 300 * (L + 1) * (Nat.size (8 * Vb L + 8) + L + 10) ≤ 300 * (L + 1) * (4 * L + 17) :=
          Nat.mul_le_mul_left _ (by omega)
        have h3 := bndEO L
        clear * - h1 h2 h3 hn1 hn2
        omega
      · rw [ht]; simp [Sg, fl, hpar, hseen]
      · rw [ht]; exact e2
      · rw [hout, F_of w xs hxs ((eoInst_iff xs).2 ⟨hch, hgood⟩), hg1,
          outWord_eq w xs ((eoInst_iff xs).2 ⟨hch, hgood⟩)]
    · have e2 := exec_skip t
      refine ⟨t, n1 + 1 + (1 + 1), ?_, StackProg.Exec.seq e1 (StackProg.Exec.branchFalse ?_ e2), ?_⟩
      · nlinarith
      · rw [ht]
        simp only [Sg, fl]
        by_cases hp : g1.par = true
        · simp [hp]
        · have hpar : g1.par = false := by simpa using hp
          have hev : ¬ (xs.length % 2 = 1) := by
            intro h; simp only [hg1, procG_par] at hpar; simp [g0, h] at hpar
          have hne : xs = [] := by
            by_contra hne; exact hgood ⟨Nat.even_iff.2 (by omega), hne⟩
          have : g1.seen = false := by simp [hg1, procG_seen, g0, hne]
          simp [hpar, this]
      · rw [ht, F_none]
        · simp [Sg]
        · rintro ⟨xs', hw', hx'⟩
          have : xs' = xs := Inj.encNats_inj (hw'.symm.trans hxs)
          subst this
          obtain ⟨-, h1, h2⟩ := (eoInst_iff xs').1 hx'
          exact hgood ⟨h1, h2⟩
  · obtain ⟨g', cur, b, lt, lz, hb, ht⟩ := hfail hs
    have e2 := exec_skip t
    refine ⟨t, n1 + 1 + (1 + 1), ?_, StackProg.Exec.seq e1 (StackProg.Exec.branchFalse ?_ e2), ?_⟩
    · nlinarith
    · rw [ht]
      obtain ⟨x, l, rfl⟩ := List.exists_cons_of_ne_nil hb
      simp [Sg]
    · rw [ht, F_none]
      · simp [Sg]
      · rintro ⟨xs', hw', hx'⟩
        exact hs ⟨xs', hw', ((eoInst_iff xs').1 hx').1⟩

/-! ## The reduction -/

lemma getD_mem_of_lt (L : List ℕ) (j : ℕ) (hj : j < L.length) : L.getD j 0 ∈ L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; simp

lemma Mf_pos (xs : List ℕ) (hx : EOInstance xs) (j : Fin (xs.length + 2)) : 0 < Mf xs j := by
  have ha : 0 < aOf xs := hx.2.2.1 _ (getD_mem_of_lt xs 0 hx.2.1)
  have hmem := getD_mem_of_lt (Mlist xs) j (by rw [Mlist_length]; exact j.isLt)
  unfold Mf
  generalize (Mlist xs).getD j 0 = v at hmem ⊢
  simp only [Mlist, List.mem_append, List.mem_replicate, List.mem_singleton] at hmem
  rcases hmem with ⟨-, h⟩ | h <;> omega

lemma lf_pos (xs : List ℕ) (hx : EOInstance xs) (j : Fin (xs.length + 2)) : 0 < lf xs j := by
  have ha : 0 < aOf xs := hx.2.2.1 _ (getD_mem_of_lt xs 0 hx.2.1)
  have hmem := getD_mem_of_lt (llist xs) j (by rw [llist_length]; exact j.isLt)
  unfold lf
  generalize (llist xs).getD j 0 = u at hmem ⊢
  simp only [llist, List.mem_cons, List.mem_append, List.mem_map, List.mem_singleton,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with h | ⟨v, -, h⟩ | h <;> omega

lemma Kv_pos (xs : List ℕ) (hx : EOInstance xs) : 0 < Kv xs := by
  have ha : 0 < aOf xs := hx.2.2.1 _ (getD_mem_of_lt xs 0 hx.2.1)
  obtain ⟨m, hm⟩ : ∃ m, xs.length / 2 = m + 1 := by
    obtain ⟨k, hk⟩ := hx.1; have := hx.2.1; exact ⟨xs.length / 2 - 1, by omega⟩
  unfold Kv; rw [hm]; exact kForm_pos _ _ _ ha

lemma tdCode_ne_nil (N k : ℕ) (M l : Fin N → ℕ) : tdCode N k M l ≠ [] := by
  simp [tdCode, encNats, encNat]

theorem evenOdd_red : PolyReducible evenOddLang tdLang := by
  classical
  obtain ⟨K, hK⟩ := poly_gen 20000 2
  refine ⟨F, CookPvsNP.stack_program_polytime eoProg Key.inp Key.out F K (fun w => ?_),
    fun w => ?_⟩
  · obtain ⟨s, n, hn, he, hs⟩ := run_eo w
    exact ⟨s, n, le_trans hn (hK _), he, hs⟩
  · constructor
    · rintro ⟨x, hx, hy, rfl⟩
      rw [F_of _ x rfl hx]
      exact ⟨x.length + 2, Kv x, Mf x, lf x, by omega, Kv_pos x hx, Mf_pos x hx, lf_pos x hx,
        (inst_iff x hx).2 hy, rfl⟩
    · intro hF
      by_cases h : ∃ xs, w = encNats xs ∧ EOInstance xs
      · obtain ⟨xs, hw, hx⟩ := h
        rw [F_of w xs hw hx] at hF
        obtain ⟨N, k, M, l, -, -, -, -, hY, he⟩ := hF
        have hl := Inj.encNats_inj he
        simp only [List.cons.injEq] at hl
        obtain ⟨hN, hk, hML⟩ := hl
        subst hN; subst hk
        have hlen : (List.ofFn (Mf xs)).length = (List.ofFn M).length := by simp
        obtain ⟨hM, hL⟩ := List.append_inj hML hlen
        have hM' : Mf xs = M := List.ofFn_injective hM
        have hL' : lf xs = l := List.ofFn_injective hL
        subst hM'; subst hL'
        exact ⟨xs, hx, (inst_iff xs hx).1 hY, hw⟩
      · rw [F_none w h] at hF
        obtain ⟨N, k, M, l, -, -, -, -, -, he⟩ := hF
        exact absurd he.symm (tdCode_ne_nil N k M l)

end TDEOTD

theorem solution : CookPvsNP.PolyReducible GTWSched.NPC.evenOddLang GTWSched.NPC.tdLang :=
  TDEOTD.evenOdd_red

