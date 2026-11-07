-- Prove2me | solution 1 for GTWSched.NPC.positivePartition_polyReducible_evenOdd
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T20:18:56.774689+00:00
-- url     : https://prove2.me/submissions/8f0f925b-2c21-48b3-8d31-f54e40114428

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems
import Theorems.Thm_CookPvsNP_stack_program_polytime

set_option autoImplicit false

namespace GTWPPEO

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
  | inp | acc | tmp | car | lz | bad | T | sc | e0 | R | out
  deriving DecidableEq

instance : Fintype Key where
  elems := {.inp, .acc, .tmp, .car, .lz, .bad, .T, .sc, .e0, .R, .out}
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


/-! ## Building blocks of the machine -/

lemma length_addB_le (x y : List Bool) (c : Bool) :
    (addB x y c).length ≤ x.length + y.length + 1 := by
  induction x, y, c using addB.induct <;> simp_all [addB] <;> omega

def pushR (a : BSym) : StackProg Key BSym := .act (fun _ k => if k = .R then .push a else .keep)

/-- Append the binary code of the accumulator, then a separator, to the reversed output `R`. -/
def emitAcc : StackProg Key BSym :=
  .seq (copyProg .acc .T .sc) (.seq (transferProg .T (fun k => decide (k = .R))) (pushR .sep))

lemma exec_emitAcc (s : Store) (hT : s .T = []) (hsc : s .sc = []) :
    ∃ n ≤ 9 * (s .acc).length + 8,
      emitAcc.Exec s (Function.update s .R (.sep :: ((s .acc).reverse ++ s .R))) n := by
  obtain ⟨n1, hn1, e1⟩ := exec_copy .acc .T .sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s .T (s .acc ++ s .T) with hs1
  obtain ⟨n2, hn2, e2⟩ := exec_transfer .T (fun k => decide (k = .R)) (s1 .T) s1 rfl
  set s2 := transferStore .T (fun k => decide (k = .R)) s1 with hs2
  have e3 : (pushR .sep).Exec s2 (StackProg.applyAct
      (fun (_ : Key → Option BSym) (k : Key) => if k = .R then StackAct.push BSym.sep else .keep) s2) 1 :=
    StackProg.Exec.act _ _
  have hfin : StackProg.applyAct
      (fun (_ : Key → Option BSym) (k : Key) => if k = .R then StackAct.push BSym.sep else .keep) s2
        = Function.update s .R (.sep :: ((s .acc).reverse ++ s .R)) := by
    funext k
    by_cases k1 : k = .R
    · subst k1; simp [StackProg.applyAct, StackAct.apply, hs2, hs1, transferStore, hT]
    by_cases k2 : k = .T
    · subst k2; simp [StackProg.applyAct, StackAct.apply, hs2, hs1, transferStore, hT]
    · simp [StackProg.applyAct, StackAct.apply, hs2, hs1, transferStore, k1, k2]
  rw [hfin] at e3
  refine ⟨n1 + 1 + (n2 + 1 + 1), ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 e3)⟩
  have : (s1 .T).length = (s .acc).length := by simp [hs1, hT]
  omega

/-- Add the binary number on top of `src` into the accumulator. -/
def addInto (src : Key) : StackProg Key BSym :=
  .seq (addLoop src .acc) (transferProg .tmp (fun k => decide (k = .acc)))

lemma exec_addInto (src : Key) (h1 : src ≠ .acc) (h2 : src ≠ .tmp) (h3 : src ≠ .car)
    (h4 : src ≠ .lz) (x y : List Bool) (r : List BSym) (hr : isDig r.head? = false) (s : Store)
    (hacc : s .acc = enc x) (hsrc : s src = enc y ++ r) (hcar : s .car = []) (htmp : s .tmp = [])
    (hlz : s .lz = [] ∨ s .lz = [.one]) :
    ∃ n ≤ 6 * (x.length + y.length) + 10, (addInto src).Exec s
      (Function.update (Function.update (Function.update s .acc (enc (addB x y false))) src r)
        .lz (lzF y (s .lz))) n := by
  obtain ⟨n1, hn1, e1⟩ := exec_addLoop src .acc h1 h2 h3 h4 (by decide) (by decide) (by decide)
    r hr _ x y false s le_rfl hacc hsrc (by rw [hcar]; rfl) hlz
  set s1 := addPost src .acc x y false r s with hs1
  obtain ⟨n2, hn2, e2⟩ := exec_transfer .tmp (fun k => decide (k = .acc)) (s1 .tmp) s1 rfl
  have hfin : transferStore .tmp (fun k => decide (k = .acc)) s1 =
      Function.update (Function.update (Function.update s .acc (enc (addB x y false))) src r)
        .lz (lzF y (s .lz)) := by
    have h2' : Key.tmp ≠ src := Ne.symm h2
    funext k
    by_cases k1 : k = .lz
    · subst k1; simp [transferStore, hs1, addPost, h4.symm, Ne.symm h4]
    by_cases k2 : k = src
    · subst k2; simp [transferStore, hs1, addPost, h1, h2, k1]
    by_cases k3 : k = .acc
    · subst k3; simp [transferStore, hs1, addPost, htmp, Ne.symm h1, h2']
    by_cases k4 : k = .tmp
    · subst k4; simp [transferStore, hs1, addPost, htmp, Ne.symm h2]
    by_cases k5 : k = .car
    · subst k5; simp [transferStore, hs1, addPost, hcar, Ne.symm h3, k2]
    · simp [transferStore, hs1, addPost, k1, k2, k3, k4, k5]
  rw [hfin] at e2
  have h2' : Key.tmp ≠ src := Ne.symm h2
  refine ⟨n1 + 1 + n2, ?_, StackProg.Exec.seq e1 e2⟩
  have hl := length_addB_le x y false
  have : (s1 .tmp).length = (addB x y false).length := by
    simp [hs1, addPost, htmp, enc, h2']
  simp only [Bool.toNat_false] at hn1
  omega

def pushE0 : StackProg Key BSym := .act (fun _ k => if k = .e0 then .push .one else .keep)

/-- Increment the accumulator. -/
def incAcc : StackProg Key BSym := .seq pushE0 (addInto .e0)

lemma exec_incAcc (x : List Bool) (s : Store) (hacc : s .acc = enc x) (he0 : s .e0 = [])
    (hcar : s .car = []) (htmp : s .tmp = []) (hlz : s .lz = [] ∨ s .lz = [.one]) :
    ∃ n ≤ 6 * x.length + 20, incAcc.Exec s
      (Function.update (Function.update s .acc (enc (addB x [true] false))) .lz []) n := by
  have e1 : pushE0.Exec s (StackProg.applyAct
      (fun (_ : Key → Option BSym) (k : Key) => if k = .e0 then StackAct.push BSym.one else .keep) s) 1 :=
    StackProg.Exec.act _ _
  set s1 := StackProg.applyAct
      (fun (_ : Key → Option BSym) (k : Key) => if k = .e0 then StackAct.push BSym.one else .keep) s
    with hs1
  have v1 : ∀ k, k ≠ .e0 → s1 k = s k := by
    intro k hk; simp [hs1, StackProg.applyAct, StackAct.apply, hk]
  obtain ⟨n2, hn2, e2⟩ := exec_addInto .e0 (by decide) (by decide) (by decide) (by decide)
    x [true] [] (by rfl) s1 (by rw [v1 _ (by decide), hacc])
    (by simp [hs1, StackProg.applyAct, StackAct.apply, he0, enc, toB])
    (by rw [v1 _ (by decide), hcar]) (by rw [v1 _ (by decide), htmp])
    (by rw [v1 _ (by decide)]; exact hlz)
  have hfin : Function.update (Function.update (Function.update s1 .acc
      (enc (addB x [true] false))) .e0 []) .lz (lzF [true] (s1 .lz)) =
      Function.update (Function.update s .acc (enc (addB x [true] false))) .lz [] := by
    funext k
    by_cases k1 : k = .lz
    · subst k1; simp [lzF]
    by_cases k2 : k = .e0
    · subst k2; simp [he0]
    by_cases k3 : k = .acc
    · subst k3; simp
    · simp [k1, k2, k3, v1 k k2]
  rw [hfin] at e2
  refine ⟨1 + 1 + n2, ?_, StackProg.Exec.seq e1 e2⟩
  simp at hn2
  omega

/-! ## One round of the main loop -/

/-- `chk`: flag the input as bad if the next number has no binary digit (it is `0`, or the
input is malformed). -/
def chkAct (h : Key → Option BSym) (k : Key) : StackAct BSym :=
  if k = .bad then (if isDig (h .inp) then .keep else .push .one) else .keep

/-- `term`: the number must be followed by a separator and have no leading zero. -/
def termAct (h : Key → Option BSym) (k : Key) : StackAct BSym :=
  if decide (h .inp = some .sep) && (h .lz).isNone then
    (if k = .inp then .pop else .keep)
  else (if k = .bad then .push .one else .keep)

def body : StackProg Key BSym :=
  .seq (.act chkAct) (.seq emitAcc (.seq (addInto .inp) (.seq (.act termAct) (.seq emitAcc incAcc))))

def loopTest (h : Key → Option BSym) : Bool := (h .inp).isSome && (h .bad).isNone

def mainLoop : StackProg Key BSym := .loop loopTest body

/-- The stores between rounds: input, accumulator, bad flag, leading-zero flag, reversed output. -/
def St (i a b z r : List BSym) : Store := fun k =>
  match k with
  | .inp => i | .acc => a | .bad => b | .lz => z | .R => r | _ => []

lemma iter (x y : List Bool) (r R : List BSym) (hr : isDig r.head? = false) :
    ∃ n ≤ 40 * (x.length + y.length) + 100,
      body.Exec (St (enc y ++ r) (enc x) [] [] R)
        (St (if r.head? = some .sep ∧ Canon y then r.tail else r)
          (enc (addB (addB x y false) [true] false))
          (if r.head? = some .sep ∧ Canon y then (if y = [] then [.one] else [])
            else .one :: (if y = [] then [.one] else []))
          []
          (.sep :: ((enc (addB x y false)).reverse ++ (.sep :: ((enc x).reverse ++ R))))) n := by
  set b1 : List BSym := if y = [] then [.one] else [] with hb1
  -- step 0: the check
  have e0 := StackProg.Exec.act chkAct (St (enc y ++ r) (enc x) [] [] R)
  have p0 : StackProg.applyAct chkAct (St (enc y ++ r) (enc x) [] [] R) =
      St (enc y ++ r) (enc x) b1 [] R := by
    funext k
    rcases y with _ | ⟨b, y⟩
    · cases k <;> simp [StackProg.applyAct, chkAct, St, StackAct.apply, hb1, enc, hr]
    · cases k <;> cases b <;> simp [StackProg.applyAct, chkAct, St, StackAct.apply, hb1, enc, toB, isDig]
  rw [p0] at e0
  -- step 1: emit the accumulator
  obtain ⟨n1, hn1, e1⟩ := exec_emitAcc (St (enc y ++ r) (enc x) b1 [] R) rfl rfl
  have p1 : Function.update (St (enc y ++ r) (enc x) b1 [] R) .R
      (.sep :: ((St (enc y ++ r) (enc x) b1 [] R .acc).reverse ++ St (enc y ++ r) (enc x) b1 [] R .R))
      = St (enc y ++ r) (enc x) b1 [] (.sep :: ((enc x).reverse ++ R)) := by
    funext k; cases k <;> simp [St]
  rw [p1] at e1
  set R1 : List BSym := .sep :: ((enc x).reverse ++ R) with hR1
  -- step 2: add the number
  obtain ⟨n2, hn2, e2⟩ := exec_addInto .inp (by decide) (by decide) (by decide) (by decide)
    x y r hr (St (enc y ++ r) (enc x) b1 [] R1) rfl rfl rfl rfl (Or.inl rfl)
  set a2 := addB x y false with ha2
  have p2 : Function.update (Function.update (Function.update (St (enc y ++ r) (enc x) b1 [] R1)
      .acc (enc a2)) .inp r) .lz (lzF y (St (enc y ++ r) (enc x) b1 [] R1 .lz)) =
      St r (enc a2) b1 (lzF y []) R1 := by
    funext k; cases k <;> simp [St]
  rw [p2] at e2
  -- step 3: the terminator test
  have e3 := StackProg.Exec.act termAct (St r (enc a2) b1 (lzF y []) R1)
  set ok : Prop := r.head? = some .sep ∧ Canon y with hok
  set b3 : List BSym := if ok then b1 else .one :: b1 with hb3
  set r3 : List BSym := if ok then r.tail else r with hr3
  have p3 : StackProg.applyAct termAct (St r (enc a2) b1 (lzF y []) R1) =
      St r3 (enc a2) b3 (lzF y []) R1 := by
    have hiff := lzF_nil_iff y
    by_cases hc : ok
    · have hl : lzF y [] = [] := hiff.2 hc.2
      have hr' : r3 = r.tail := by simp [hr3, hc]
      have hb' : b3 = b1 := by simp [hb3, hc]
      rw [hr', hb']
      funext k; cases k <;> simp [StackProg.applyAct, termAct, St, hc.1, hl, StackAct.apply]
    · have hr' : r3 = r := by simp [hr3, hc]
      have hb' : b3 = .one :: b1 := by simp [hb3, hc]
      rw [hr', hb']
      have hcond : (decide (r.head? = some BSym.sep) && (lzF y []).head?.isNone) = false := by
        apply Bool.eq_false_iff.mpr
        intro h; apply hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none,
          List.head?_eq_none_iff] at h
        exact ⟨h.1, hiff.1 h.2⟩
      have hc' : ¬(decide (r.head? = some BSym.sep) = true ∧ lzF y [] = []) :=
        fun h => hc ⟨by simpa using h.1, hiff.1 h.2⟩
      funext k; cases k <;> simp [StackProg.applyAct, termAct, St, StackAct.apply] <;>
        split_ifs with h <;> first | rfl | exact absurd h hc'
  rw [p3] at e3
  -- step 4: emit the new accumulator
  obtain ⟨n4, hn4, e4⟩ := exec_emitAcc (St r3 (enc a2) b3 (lzF y []) R1) rfl rfl
  have p4 : Function.update (St r3 (enc a2) b3 (lzF y []) R1) .R
      (.sep :: ((St r3 (enc a2) b3 (lzF y []) R1 .acc).reverse ++ St r3 (enc a2) b3 (lzF y []) R1 .R))
      = St r3 (enc a2) b3 (lzF y []) (.sep :: ((enc a2).reverse ++ R1)) := by
    funext k; cases k <;> simp [St]
  rw [p4] at e4
  -- step 5: increment
  obtain ⟨n5, hn5, e5⟩ := exec_incAcc a2 (St r3 (enc a2) b3 (lzF y []) (.sep :: ((enc a2).reverse ++ R1)))
    rfl rfl rfl rfl (lzF_cases y [] (Or.inl rfl))
  have p5 : Function.update (Function.update
      (St r3 (enc a2) b3 (lzF y []) (.sep :: ((enc a2).reverse ++ R1))) .acc
      (enc (addB a2 [true] false))) .lz [] =
      St r3 (enc (addB a2 [true] false)) b3 [] (.sep :: ((enc a2).reverse ++ R1)) := by
    funext k; cases k <;> simp [St]
  rw [p5] at e5
  refine ⟨1 + 1 + (n1 + 1 + (n2 + 1 + (1 + 1 + (n4 + 1 + n5)))), ?_,
    StackProg.Exec.seq e0 (StackProg.Exec.seq e1 (StackProg.Exec.seq e2
      (StackProg.Exec.seq e3 (StackProg.Exec.seq e4 e5))))⟩
  have hl := length_addB_le x y false
  simp only [St, enc, List.length_map] at hn1 hn4
  rw [← ha2] at hl
  omega

/-! ## The whole main loop -/

def pb (L A : ℕ) : ℕ := (L + 1) * (40 * (A + 3 * L) + 110) + 1

lemma pb_step (A Y R A' n m : ℕ) (hA : A' ≤ A + Y + 3) (hn : n ≤ 40 * (A + Y) + 100)
    (hm : m ≤ pb R A') : 1 + n + 1 + m ≤ pb (Y + 1 + R) A := by
  unfold pb at *
  have h1 : (R + 1) * (40 * (A' + 3 * R) + 110) ≤ (R + 1) * (40 * (A + 3 * (Y + 1 + R)) + 110) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : (Y + 1 + R + 1) * (40 * (A + 3 * (Y + 1 + R)) + 110) =
      (R + 1) * (40 * (A + 3 * (Y + 1 + R)) + 110) + (Y + 1) * (40 * (A + 3 * (Y + 1 + R)) + 110) := by
    ring
  have h3 : 40 * (A + 3 * (Y + 1 + R)) + 110 ≤ (Y + 1) * (40 * (A + 3 * (Y + 1 + R)) + 110) :=
    Nat.le_mul_of_pos_left _ (by omega)
  rw [h2]; omega

lemma pb_ge (L A : ℕ) : 40 * (A + L) + 110 ≤ pb L A := by
  unfold pb
  have : 40 * (A + 3 * L) + 110 ≤ (L + 1) * (40 * (A + 3 * L) + 110) :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

lemma encNat_rev (k : ℕ) : (encNat k).reverse = .sep :: (enc (Nat.bits k)).reverse := by
  simp [encNat_eq]

lemma loop_nil (a : ℕ) (R : List BSym) :
    ∃ t n, n ≤ pb ([] : List BSym).length (Nat.bits a).length ∧
      mainLoop.Exec (St [] (enc (Nat.bits a)) [] [] R) t n ∧
      (∀ sl : List ℕ, (∀ v ∈ sl, 0 < v) → ([] : List BSym) = encNats sl →
        ∃ a' : ℕ, t = St [] (enc (Nat.bits a')) [] [] ((encNats (eoAux a sl)).reverse ++ R)) ∧
      ((∀ sl : List ℕ, (∀ v ∈ sl, 0 < v) → ([] : List BSym) ≠ encNats sl) →
        ∃ i' a' b' z' R', b' ≠ [] ∧ t = St i' a' b' z' R') := by
  refine ⟨_, 1, by simp [pb], StackProg.Exec.loopFalse (by simp [loopTest, St]), ?_, ?_⟩
  · intro sl _ hsl
    have := encNats_eq_nil hsl.symm; subst this
    exact ⟨a, by simp [eoAux, encNats]⟩
  · intro h; exact absurd rfl (h [] (by simp))

lemma loop_all : ∀ (L : ℕ) (i : List BSym) (a : ℕ) (R : List BSym), i.length ≤ L →
    ∃ t n, n ≤ pb i.length (Nat.bits a).length ∧
      mainLoop.Exec (St i (enc (Nat.bits a)) [] [] R) t n ∧
      (∀ sl : List ℕ, (∀ v ∈ sl, 0 < v) → i = encNats sl →
        ∃ a' : ℕ, t = St [] (enc (Nat.bits a')) [] [] ((encNats (eoAux a sl)).reverse ++ R)) ∧
      ((∀ sl : List ℕ, (∀ v ∈ sl, 0 < v) → i ≠ encNats sl) →
        ∃ i' a' b' z' R', b' ≠ [] ∧ t = St i' a' b' z' R') := by
  intro L
  induction L with
  | zero =>
    intro i a R hi
    have : i = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; exact loop_nil a R
  | succ L ih =>
    intro i a R hi
    by_cases hnil : i = []
    · subst hnil; exact loop_nil a R
    obtain ⟨y, r, hi_eq, hr⟩ : ∃ y r, i = enc y ++ r ∧ isDig r.head? = false :=
      ⟨_, _, (split_digits i).1, (split_digits i).2⟩
    subst hi_eq
    have htest : loopTest (fun k => (St (enc y ++ r) (enc (Nat.bits a)) [] [] R k).head?) = true := by
      simp only [loopTest, St, List.head?_nil, Option.isNone_none, Bool.and_true]
      cases h : (enc y ++ r) with
      | nil => exact absurd h hnil
      | cons _ _ => rfl
    obtain ⟨n, hn, eb⟩ := iter (Nat.bits a) y r R hr
    have hlen : (enc y ++ r).length = y.length + r.length := by simp [enc]
    by_cases hc : (r.head? = some .sep ∧ Canon y) ∧ y ≠ []
    · rw [if_pos hc.1, if_pos hc.1, if_neg hc.2] at eb
      obtain ⟨r', rfl⟩ : ∃ r', r = .sep :: r' := by
        rcases r with _ | ⟨b, r'⟩
        · simp at hc
        · simp at hc; exact ⟨r', by rw [hc.1.1]⟩
      set k := bval y with hk
      have hy : Nat.bits k = y := bits_bval hc.1.2
      have hadd : addB (Nat.bits a) y false = Nat.bits (a + k) := by rw [← hy, bits_add]
      have hadd2 : addB (Nat.bits (a + k)) [true] false = Nat.bits (a + k + 1) := by
        have := bits_add (a + k) 1; rw [bits_one] at this; exact this.symm
      rw [hadd, hadd2] at eb
      simp only [List.tail_cons] at eb
      obtain ⟨t, m, hm, hex, hval, hinv⟩ := ih r' (a + k + 1)
        (.sep :: ((enc (Nat.bits (a + k))).reverse ++ (.sep :: ((enc (Nat.bits a)).reverse ++ R))))
        (by simp at hlen hi; omega)
      have hA : (Nat.bits (a + k + 1)).length ≤ (Nat.bits a).length + y.length + 3 := by
        rw [← hadd2, ← hadd]
        have := length_addB_le (addB (Nat.bits a) y false) [true] false
        have := length_addB_le (Nat.bits a) y false
        simp at *; omega
      refine ⟨t, 1 + n + 1 + m, ?_, StackProg.Exec.loopTrue htest eb hex, ?_, ?_⟩
      · have := pb_step _ _ _ _ _ _ hA (by simpa [enc] using hn) hm
        simpa [hlen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      · intro sl hpos hsl
        rcases sl with _ | ⟨k', sl'⟩
        · exact absurd hsl (by simp [encNats])
        rw [encNats_cons'] at hsl
        obtain ⟨h1, h2⟩ := enc_append_inj hr (by rfl) hsl
        simp only [List.cons.injEq, true_and] at h2
        have hkk : k = k' := by rw [hk, h1, (canon_bits_bval k').2]
        obtain ⟨a', ha'⟩ := hval sl' (fun v hv => hpos v (by simp [hv])) h2
        refine ⟨a', ?_⟩
        rw [ha', ← hkk]
        simp [eoAux, encNats, encNat_eq]
      · intro hall
        apply hinv
        intro sl' hpos h'
        apply hall (k :: sl')
        · intro v hv
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · rw [hk]; exact bval_pos hc.1.2 hc.2
          · exact hpos v hv
        · rw [encNats_cons', hy, h']
    · have hbad : (if r.head? = some .sep ∧ Canon y then (if y = [] then [.one] else [])
            else BSym.one :: (if y = [] then [.one] else [])) ≠ [] := by
        by_cases h1 : r.head? = some .sep ∧ Canon y
        · have : y = [] := by by_contra h2; exact hc ⟨h1, h2⟩
          rw [if_pos h1, if_pos this]; simp
        · rw [if_neg h1]; simp
      refine ⟨_, 1 + n + 1 + 1, ?_,
        StackProg.Exec.loopTrue htest eb (StackProg.Exec.loopFalse ?_), ?_, ?_⟩
      · have := pb_ge (enc y ++ r).length (Nat.bits a).length
        rw [hlen] at this ⊢; omega
      · simp only [loopTest, St]
        cases h : (if r.head? = some .sep ∧ Canon y then (if y = [] then [BSym.one] else [])
            else BSym.one :: (if y = [] then [BSym.one] else [])) with
        | nil => exact absurd h hbad
        | cons _ _ => simp
      · intro sl hpos hsl
        exfalso
        rcases sl with _ | ⟨k', sl'⟩
        · exact hnil hsl
        rw [encNats_cons'] at hsl
        obtain ⟨h1, h2⟩ := enc_append_inj hr (by rfl) hsl
        apply hc; subst h1 h2
        refine ⟨⟨rfl, (canon_bits_bval k').1⟩, ?_⟩
        intro h0
        have := (canon_bits_bval k').2
        rw [h0] at this
        have hp := hpos k' (by simp)
        simp [bval] at this; omega
      · intro _; exact ⟨_, _, _, _, _, hbad, rfl⟩


lemma len_eo : ∀ (sl : List ℕ) (a : ℕ), (encNats (eoAux a sl)).length ≤
    ((encNats sl).length + 1) * (2 * (Nat.bits a).length + 6 * (encNats sl).length + 4) := by
  intro sl
  induction sl with
  | nil => intro a; simp [eoAux, encNats]
  | cons k sl ih =>
    intro a
    have e1 : encNats (eoAux a (k :: sl)) = encNat a ++ encNat (a + k) ++ encNats (eoAux (a + k + 1) sl) := by
      simp [eoAux, encNats]
    rw [e1, encNats_cons']
    have h1 := ih (a + k + 1)
    have hA1 : (Nat.bits (a + k)).length ≤ (Nat.bits a).length + (Nat.bits k).length + 1 := by
      rw [bits_add]; exact length_addB_le _ _ _
    have hA2 : (Nat.bits (a + k + 1)).length ≤ (Nat.bits (a + k)).length + 2 := by
      have := bits_add (a + k) 1; rw [bits_one] at this; rw [this]
      have := length_addB_le (Nat.bits (a + k)) [true] false; simpa using this
    simp only [List.length_append, encNat, List.length_map, List.length_cons, List.length_nil, enc] at h1 ⊢
    set A := (Nat.bits a).length
    set Y := (Nat.bits k).length
    set E := (encNats sl).length
    set A' := (Nat.bits (a + k + 1)).length
    have m1 : (E + 1) * (2 * A' + 6 * E + 4) ≤ (E + 1) * (2 * A + 2 * Y + 6 + 6 * E + 4) :=
      Nat.mul_le_mul_left _ (by omega)
    have m2 : (Y + (E + 1) + 1) * (2 * A + 6 * (Y + (E + 1)) + 4) =
        (E + 1) * (2 * A + 2 * Y + 6 + 6 * E + 4) + (E + 1) * (4 * Y) +
          (Y + 1) * (2 * A + 6 * (Y + (E + 1)) + 4) := by ring
    have m3 : 2 * A + Y + 4 ≤ (Y + 1) * (2 * A + 6 * (Y + (E + 1)) + 4) := by
      nlinarith
    rw [m2]; omega

/-! ## The whole machine -/

def initAct (_ : Key → Option BSym) (k : Key) : StackAct BSym :=
  if k = .acc then .push .one else .keep

def skipP : StackProg Key BSym := .act (fun _ _ => .keep)

def mainProg : StackProg Key BSym :=
  .seq (.act initAct) (.seq mainLoop
    (.branch (fun h => (h .bad).isSome) skipP (transferProg .R (fun k => decide (k = .out)))))

lemma encNats_inj : ∀ {a b : List ℕ}, encNats a = encNats b → a = b := by
  intro a
  induction a with
  | nil => intro b h; exact (encNats_eq_nil h.symm).symm
  | cons k a ih =>
    intro b h
    rcases b with _ | ⟨k', b⟩
    · exact absurd (encNats_eq_nil h) (by simp)
    rw [encNats_cons', encNats_cons'] at h
    obtain ⟨h1, h2⟩ := enc_append_inj (by rfl) (by rfl) h
    simp only [List.cons.injEq, true_and] at h2
    have hk : k = k' := by
      rw [← (canon_bits_bval k).2, ← (canon_bits_bval k').2, h1]
    rw [hk, ih h2]

open Classical in
/-- The reduction: a code of a nonempty list `Y` of positive integers is sent to the code of
the even-odd instance `X` of LEMMA 1; every other string is sent to the empty string. -/
noncomputable def Fred (w : List BSym) : List BSym :=
  if h : ∃ sl : List ℕ, sl ≠ [] ∧ (∀ v ∈ sl, 0 < v) ∧ w = encNats sl then
    encNats (eoOfPartition h.choose) else []

lemma Fred_valid (sl : List ℕ) (hne : sl ≠ []) (hpos : ∀ v ∈ sl, 0 < v) :
    Fred (encNats sl) = encNats (eoOfPartition sl) := by
  have h : ∃ s : List ℕ, s ≠ [] ∧ (∀ v ∈ s, 0 < v) ∧ encNats sl = encNats s := ⟨sl, hne, hpos, rfl⟩
  rw [Fred, dif_pos h, show h.choose = sl from (encNats_inj h.choose_spec.2.2).symm]

lemma Fred_invalid {w : List BSym}
    (hw : ¬ ∃ sl : List ℕ, sl ≠ [] ∧ (∀ v ∈ sl, 0 < v) ∧ w = encNats sl) : Fred w = [] := by
  rw [Fred, dif_neg hw]

lemma absorb2000 (L : ℕ) : 400 * (L + 1) ^ 2 + 400 ≤ L ^ 2000 + 2000 := by
  rcases L with _ | _ | L
  · norm_num
  · norm_num
  · have key : 400 * (L + 1 + 1 + 1) ^ 2 + 400 ≤ (L + 2) ^ 14 := by
      have h1 : 2 ^ 12 ≤ (L + 2) ^ 12 := Nat.pow_le_pow_left (by omega) 12
      have h2 : (L + 2) ^ 14 = (L + 2) ^ 2 * (L + 2) ^ 12 := by ring
      have h4 : (L + 1 + 1 + 1) ^ 2 ≤ 4 * (L + 2) ^ 2 := by
        have h : L + 1 + 1 + 1 ≤ 2 * (L + 2) := by omega
        calc (L + 1 + 1 + 1) ^ 2 ≤ (2 * (L + 2)) ^ 2 := Nat.pow_le_pow_left h 2
          _ = 4 * (L + 2) ^ 2 := by ring
      have h5 : 1 ≤ (L + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
      rw [h2]
      generalize (L + 2) ^ 12 = X at h1
      generalize (L + 1 + 1 + 1) ^ 2 = Z at h4 ⊢
      generalize (L + 2) ^ 2 = Y at h4 h5 ⊢
      have hYX : Y * 4096 ≤ Y * X := Nat.mul_le_mul_left _ (by simpa using h1)
      omega
    have h3 : (L + 2) ^ 14 ≤ (L + 2) ^ 2000 := Nat.pow_le_pow_right (by omega) (by norm_num)
    calc 400 * (L + 1 + 1 + 1) ^ 2 + 400 ≤ (L + 2) ^ 14 := key
      _ ≤ (L + 2) ^ 2000 := h3
      _ ≤ (L + 1 + 1) ^ 2000 + 2000 := Nat.le_add_right _ _

lemma exec_main (w : List BSym) : ∃ t n, n ≤ 400 * (w.length + 1) ^ 2 + 400 ∧
    mainProg.Exec (fun j => if j = .inp then w else []) t n ∧ t .out = Fred w := by
  set s0 : Store := fun j => if j = .inp then w else [] with hs0
  have e1 := StackProg.Exec.act initAct s0
  have p1 : StackProg.applyAct initAct s0 = St w (enc (Nat.bits 1)) [] [] [] := by
    rw [bits_one]
    funext k; cases k <;> simp [StackProg.applyAct, initAct, StackAct.apply, St, hs0, enc, toB]
  rw [p1] at e1
  obtain ⟨t, n2, hn2, e2, hval, hinv⟩ := loop_all w.length w 1 [] le_rfl
  have hpb : pb w.length (Nat.bits 1).length = (w.length + 1) * (40 * (1 + 3 * w.length) + 110) + 1 := by
    simp [pb, bits_one]
  rw [hpb] at hn2
  by_cases hw : ∃ sl : List ℕ, (∀ v ∈ sl, 0 < v) ∧ w = encNats sl
  · obtain ⟨sl, hpos, hsl⟩ := hw
    obtain ⟨a', ht⟩ := hval sl hpos hsl
    subst ht
    obtain ⟨n3, hn3, e3⟩ := exec_transfer .R (fun k => decide (k = .out))
      ((encNats (eoAux 1 sl)).reverse ++ [])
      (St [] (enc (Nat.bits a')) [] [] ((encNats (eoAux 1 sl)).reverse ++ [])) rfl
    refine ⟨_, 1 + 1 + (n2 + 1 + (1 + n3)), ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2
      (StackProg.Exec.branchFalse (by simp [St]) e3)), ?_⟩
    · have h3 := len_eo sl 1
      rw [← hsl, bits_one] at h3
      have h3' : (encNats (eoAux 1 sl)).length ≤ (w.length + 1) * (6 * w.length + 6) :=
        le_trans h3 (le_of_eq (by simp; ring))
      simp only [List.append_nil, List.length_reverse] at hn3
      have : n3 ≤ 3 * ((w.length + 1) * (6 * w.length + 6)) + 1 := by omega
      nlinarith
    · simp only [transferStore, St]
      simp only [List.append_nil, List.reverse_reverse]
      by_cases hne : sl = []
      · subst hne
        have : ¬ ∃ s : List ℕ, s ≠ [] ∧ (∀ v ∈ s, 0 < v) ∧ w = encNats s := by
          rintro ⟨s, hs, -, hws⟩
          rw [hsl] at hws
          exact hs (encNats_eq_nil hws.symm)
        rw [Fred_invalid this]; simp [eoAux, encNats]
      · rw [hsl, Fred_valid sl hne hpos]; rfl
  · obtain ⟨i', a', b', z', R', hb', rfl⟩ := hinv (fun sl hp h => hw ⟨sl, hp, h⟩)
    have hbr : (fun h : Key → Option BSym => (h .bad).isSome)
        (fun k => (St i' a' b' z' R' k).head?) = true := by
      cases b' with
      | nil => exact absurd rfl hb'
      | cons _ _ => simp [St]
    refine ⟨_, 1 + 1 + (n2 + 1 + (1 + 1)), ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2
      (StackProg.Exec.branchTrue hbr (StackProg.Exec.act _ _))), ?_⟩
    · have hq : (w.length + 1) * (40 * (1 + 3 * w.length) + 110) ≤ 400 * (w.length + 1) ^ 2 :=
        calc (w.length + 1) * (40 * (1 + 3 * w.length) + 110)
            ≤ (w.length + 1) * (400 * (w.length + 1)) := Nat.mul_le_mul_left _ (by omega)
          _ = 400 * (w.length + 1) ^ 2 := by ring
      omega
    · rw [Fred_invalid (fun ⟨sl, _, hp, h⟩ => hw ⟨sl, hp, h⟩)]
      rfl

theorem Fred_exec (w : List BSym) : ∃ s n, n ≤ w.length ^ 2000 + 2000 ∧
    mainProg.Exec (fun j => if j = .inp then w else []) s n ∧ s .out = Fred w := by
  obtain ⟨t, n, hn, e, ho⟩ := exec_main w
  exact ⟨t, n, le_trans hn (absorb2000 _), e, ho⟩

/-! ## The construction of LEMMA 1 (entries only need to be positive) -/

section Constr
open Classical
lemma eoAux_length (ys : List ℕ) : ∀ a, (eoAux a ys).length = 2 * ys.length := by
  induction ys with
  | nil => intro a; simp [eoAux]
  | cons y ys ih => intro a; simp [eoAux, ih]; ring

lemma eoAux_ge (ys : List ℕ) : ∀ a, ∀ v ∈ eoAux a ys, a ≤ v := by
  induction ys with
  | nil => intro a v hv; simp [eoAux] at hv
  | cons y ys ih =>
    intro a v hv
    simp only [eoAux, List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    · exact le_rfl
    · omega
    · have := ih (a+y+1) v hv; omega

lemma eoAux_pairwise (ys : List ℕ) (hy : ∀ v ∈ ys, 0 < v) :
    ∀ a, (eoAux a ys).Pairwise (· < ·) := by
  induction ys with
  | nil => intro a; simp [eoAux]
  | cons y ys ih =>
    intro a
    have hy0 : 0 < y := hy y (by simp)
    have hrest := ih (fun v hv => hy v (by simp [hv])) (a+y+1)
    simp only [eoAux]
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ hrest)
    · intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · omega
      · have := eoAux_ge ys (a+y+1) b hb; omega
    · intro b hb
      have := eoAux_ge ys (a+y+1) b hb; omega

lemma eoAux_getD (ys : List ℕ) : ∀ (a i : ℕ), i < ys.length →
    (eoAux a ys).getD (2*i) 0 = a + ∑ j ∈ Finset.range i, (ys.getD j 0 + 1) ∧
    (eoAux a ys).getD (2*i+1) 0 = a + ∑ j ∈ Finset.range i, (ys.getD j 0 + 1) + ys.getD i 0 := by
  induction ys with
  | nil => intro a i hi; simp at hi
  | cons y ys ih =>
    intro a i hi
    cases i with
    | zero => simp [eoAux]
    | succ i =>
      have hi' : i < ys.length := by simpa using hi
      obtain ⟨h1, h2⟩ := ih (a+y+1) i hi'
      rw [Finset.sum_range_succ']
      constructor
      · have : (eoAux a (y :: ys)).getD (2*(i+1)) 0 = (eoAux (a+y+1) ys).getD (2*i) 0 := by
          simp [eoAux, show 2*(i+1) = 2*i+1+1 by ring]
        rw [this, h1]; simp; omega
      · have : (eoAux a (y :: ys)).getD (2*(i+1)+1) 0 = (eoAux (a+y+1) ys).getD (2*i+1) 0 := by
          simp [eoAux, show 2*(i+1)+1 = 2*i+1+1+1 by ring]
        rw [this, h2]; simp; omega

lemma sum_fin_pred (l : List ℕ) (A : Finset (Fin l.length)) :
    ∑ i ∈ A, l.get i = ∑ p ∈ Finset.range l.length,
      if (∃ h : p < l.length, (⟨p, h⟩ : Fin l.length) ∈ A) then l.getD p 0 else 0 := by
  rw [Finset.sum_range (fun p => if (∃ h : p < l.length, (⟨p, h⟩ : Fin l.length) ∈ A) then l.getD p 0 else 0)]
  have key : ∀ i : Fin l.length, (if (∃ h : i.val < l.length, (⟨i.val, h⟩ : Fin l.length) ∈ A) then l.getD i.val 0 else 0)
      = if i ∈ A then l.get i else 0 := by
    intro i
    have e1 : (∃ h : i.val < l.length, (⟨i.val, h⟩ : Fin l.length) ∈ A) ↔ i ∈ A := by
      constructor
      · rintro ⟨h, hh⟩; exact hh
      · intro h; exact ⟨i.isLt, h⟩
    have e2 : l.getD i.val 0 = l.get i := by simp [List.getD_eq_getElem?_getD]
    by_cases hi : i ∈ A
    · rw [if_pos (e1.mpr hi), if_pos hi, e2]
    · rw [if_neg (fun h => hi (e1.mp h)), if_neg hi]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  rw [Finset.sum_ite_mem]
  simp

lemma sum_range_pairs (h : ℕ → ℕ) (n : ℕ) :
    ∑ p ∈ Finset.range (2*n), h p = ∑ i ∈ Finset.range n, (h (2*i) + h (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring


lemma sum_cancel (L R g h : ℕ → ℕ) (n : ℕ)
    (term : ∀ i ∈ Finset.range n, L i + g i = R i + h i) :
    (∑ i ∈ Finset.range n, L i = ∑ i ∈ Finset.range n, R i) ↔
      (∑ i ∈ Finset.range n, h i = ∑ i ∈ Finset.range n, g i) := by
  have e1 := Finset.sum_congr rfl term
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at e1
  constructor <;> intro h <;> omega

lemma core_alg (x : List ℕ) (n : ℕ) (hlen : x.length = 2*n) (yv : ℕ → ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hQ : ∀ i < n, Q (2*i) ↔ ¬ Q (2*i+1))
    (hxo : ∀ i < n, x.getD (2*i+1) 0 = x.getD (2*i) 0 + yv i) :
    (∑ p ∈ Finset.range x.length, (if Q p then x.getD p 0 else 0) =
      ∑ p ∈ Finset.range x.length, (if ¬ Q p then x.getD p 0 else 0)) ↔
    (∑ i ∈ Finset.range n, (if Q (2*i+1) then yv i else 0) =
      ∑ i ∈ Finset.range n, (if ¬ Q (2*i+1) then yv i else 0)) := by
  rw [hlen, sum_range_pairs (fun p => if Q p then x.getD p 0 else 0),
    sum_range_pairs (fun p => if ¬ Q p then x.getD p 0 else 0)]
  have term : ∀ i ∈ Finset.range n,
      ((if Q (2*i) then x.getD (2*i) 0 else 0) + (if Q (2*i+1) then x.getD (2*i+1) 0 else 0))
        + (if ¬ Q (2*i+1) then yv i else 0)
      = ((if ¬ Q (2*i) then x.getD (2*i) 0 else 0) + (if ¬ Q (2*i+1) then x.getD (2*i+1) 0 else 0))
        + (if Q (2*i+1) then yv i else 0) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have h1 := hxo i hi'
    have h2 := hQ i hi'
    by_cases h : Q (2*i+1)
    · have h3 : ¬ Q (2*i) := fun h4 => (h2.mp h4) h
      simp only [h, h3, not_true_eq_false, not_false_eq_true, if_true, if_false]
      omega
    · have h3 : Q (2*i) := h2.mpr h
      simp only [h, h3, not_true_eq_false, not_false_eq_true, if_true, if_false]
      omega
  exact sum_cancel _ _ _ _ n term


lemma eoyes_iff (y : List ℕ) :
    EOYes (eoOfPartition y) ↔ ∃ g : ℕ → Prop,
      ∑ i ∈ Finset.range y.length, (if g i then y.getD i 0 else 0) =
      ∑ i ∈ Finset.range y.length, (if ¬ g i then y.getD i 0 else 0) := by
  unfold eoOfPartition
  set x := eoAux 1 y with hx
  have hlen : x.length = 2 * y.length := eoAux_length y 1
  have hxo : ∀ i < y.length, x.getD (2*i+1) 0 = x.getD (2*i) 0 + y.getD i 0 := by
    intro i hi
    obtain ⟨h1, h2⟩ := eoAux_getD y 1 i hi
    rw [hx, h1, h2]
  constructor
  · rintro ⟨X1, hpair, hsum⟩
    set Q : ℕ → Prop := fun p => ∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1 with hQdef
    have hQ : ∀ i < y.length, Q (2*i) ↔ ¬ Q (2*i+1) := by
      intro i hi
      have h1 : 2*i < x.length := by omega
      have h2 : 2*i+1 < x.length := by omega
      have := hpair ⟨2*i, h1⟩ ⟨2*i+1, h2⟩ (by simp [Fin.ext_iff]) (by simp; omega)
      constructor
      · rintro ⟨h, hh⟩ ⟨h', hh'⟩
        exact (this.mp hh) hh'
      · intro hn
        have hn' : (⟨2*i+1, h2⟩ : Fin x.length) ∉ X1 := fun hh => hn ⟨h2, hh⟩
        exact ⟨h1, this.mpr hn'⟩
    refine ⟨fun i => Q (2*i+1), ?_⟩
    have e1 := sum_fin_pred x X1
    have e2 := sum_fin_pred x X1ᶜ
    have e3 : ∑ p ∈ Finset.range x.length, (if (∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1ᶜ)
        then x.getD p 0 else 0) = ∑ p ∈ Finset.range x.length, (if ¬ Q p then x.getD p 0 else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := Finset.mem_range.mp hp
      have : (∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1ᶜ) ↔ ¬ Q p := by
        constructor
        · rintro ⟨h, hh⟩ ⟨h', hh'⟩
          exact (Finset.mem_compl.mp hh) hh'
        · intro hn
          refine ⟨hp', ?_⟩
          rw [Finset.mem_compl]
          intro hc; exact hn ⟨hp', hc⟩
      exact if_congr this rfl rfl
    have e4 : ∑ p ∈ Finset.range x.length, (if (∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1)
          then x.getD p 0 else 0) = ∑ p ∈ Finset.range x.length, (if Q p then x.getD p 0 else 0) :=
      Finset.sum_congr rfl (fun p _ => if_congr Iff.rfl rfl rfl)
    rw [e1, e2, e3, e4] at hsum
    have this := (core_alg x y.length hlen (fun i => y.getD i 0) Q hQ hxo).mp hsum
    convert this using 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> congr
  · rintro ⟨g, hg⟩
    set P : ℕ → Prop := fun p => if p % 2 = 1 then g (p / 2) else ¬ g (p / 2) with hP
    set X1 : Finset (Fin x.length) := Finset.univ.filter (fun p => P p.val) with hX1
    refine ⟨X1, ?_, ?_⟩
    · intro p q hpq hdiv
      have hmod : p.val % 2 ≠ q.val % 2 := by
        intro h; apply hpq; apply Fin.ext; omega
      simp only [hX1, Finset.mem_filter, Finset.mem_univ, true_and, hP]
      by_cases hp : p.val % 2 = 1
      · have hq : q.val % 2 ≠ 1 := by omega
        simp [hp, hq, hdiv]
      · have hq : q.val % 2 = 1 := by omega
        simp [hp, hq, hdiv]
    · set Q : ℕ → Prop := fun p => p < x.length ∧ P p with hQdef
      have e1 := sum_fin_pred x X1
      have e2 := sum_fin_pred x X1ᶜ
      have eQ : ∀ p, (∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1) ↔ Q p := by
        intro p
        constructor
        · rintro ⟨h, hh⟩
          exact ⟨h, by simpa [hX1] using hh⟩
        · rintro ⟨h, hh⟩
          exact ⟨h, by simpa [hX1] using hh⟩
      have e3 : ∑ p ∈ Finset.range x.length, (if (∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1ᶜ)
          then x.getD p 0 else 0) = ∑ p ∈ Finset.range x.length, (if ¬ Q p then x.getD p 0 else 0) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp' := Finset.mem_range.mp hp
        have : (∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1ᶜ) ↔ ¬ Q p := by
          constructor
          · rintro ⟨h, hh⟩ hc
            exact (Finset.mem_compl.mp hh) ((eQ p).mpr hc |>.choose_spec)
          · intro hn
            refine ⟨hp', ?_⟩
            rw [Finset.mem_compl]
            intro hc; exact hn ((eQ p).mp ⟨hp', hc⟩)
        exact if_congr this rfl rfl
      have e4 : ∑ p ∈ Finset.range x.length, (if (∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1)
          then x.getD p 0 else 0) = ∑ p ∈ Finset.range x.length, (if Q p then x.getD p 0 else 0) :=
        Finset.sum_congr rfl (fun p _ => if_congr (eQ p) rfl rfl)
      rw [e1, e2, e3, e4]
      have hQ : ∀ i < y.length, Q (2*i) ↔ ¬ Q (2*i+1) := by
        intro i hi
        simp only [hQdef, hP]
        have h1 : 2*i < x.length := by omega
        have h2 : 2*i+1 < x.length := by omega
        simp [h1, h2, show (2*i) % 2 ≠ 1 by omega, show (2*i+1) % 2 = 1 by omega,
          show (2*i)/2 = i by omega, show (2*i+1)/2 = i by omega]
      refine (core_alg x y.length hlen (fun i => y.getD i 0) Q hQ hxo).mpr ?_
      have hQg : ∀ i < y.length, Q (2*i+1) ↔ g i := by
        intro i hi
        simp only [hQdef, hP]
        have h2 : 2*i+1 < x.length := by omega
        simp [h2, show (2*i+1) % 2 = 1 by omega, show (2*i+1)/2 = i by omega]
      have s1 : ∑ i ∈ Finset.range y.length, (if Q (2*i+1) then y.getD i 0 else 0) =
          ∑ i ∈ Finset.range y.length, (if g i then y.getD i 0 else 0) :=
        Finset.sum_congr rfl (fun i hi => if_congr (hQg i (Finset.mem_range.mp hi)) rfl rfl)
      have s2 : ∑ i ∈ Finset.range y.length, (if ¬ Q (2*i+1) then y.getD i 0 else 0) =
          ∑ i ∈ Finset.range y.length, (if ¬ g i then y.getD i 0 else 0) :=
        Finset.sum_congr rfl (fun i hi => if_congr (not_congr (hQg i (Finset.mem_range.mp hi))) rfl rfl)
      rw [s1, s2]; exact hg


lemma pred_sum_iff (l : List ℕ) (g : ℕ → Prop) (A : Finset (Fin l.length))
    (hA : ∀ p (h : p < l.length), (⟨p, h⟩ : Fin l.length) ∈ A ↔ g p) :
    ∑ i ∈ A, l.get i = ∑ p ∈ Finset.range l.length, (if g p then l.getD p 0 else 0) ∧
    ∑ i ∈ Aᶜ, l.get i = ∑ p ∈ Finset.range l.length, (if ¬ g p then l.getD p 0 else 0) := by
  constructor
  · rw [sum_fin_pred]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.mem_range.mp hp
    have : (∃ h : p < l.length, (⟨p, h⟩ : Fin l.length) ∈ A) ↔ g p :=
      ⟨fun ⟨h, hh⟩ => (hA p h).mp hh, fun hg => ⟨hp', (hA p hp').mpr hg⟩⟩
    by_cases hg : g p
    · rw [if_pos (this.mpr hg), if_pos hg]
    · rw [if_neg (fun h => hg (this.mp h)), if_neg hg]
  · rw [sum_fin_pred]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.mem_range.mp hp
    have : (∃ h : p < l.length, (⟨p, h⟩ : Fin l.length) ∈ Aᶜ) ↔ ¬ g p := by
      constructor
      · rintro ⟨h, hh⟩ hg
        exact (Finset.mem_compl.mp hh) ((hA p h).mpr hg)
      · intro hg
        exact ⟨hp', Finset.mem_compl.mpr (fun hh => hg ((hA p hp').mp hh))⟩
    by_cases hg : g p
    · rw [if_neg (fun h => (this.mp h) hg), if_neg (not_not.mpr hg)]
    · rw [if_pos (this.mpr hg), if_pos hg]

lemma partition_iff (y : List ℕ) :
    PartitionYes y ↔ ∃ g : ℕ → Prop,
      ∑ i ∈ Finset.range y.length, (if g i then y.getD i 0 else 0) =
      ∑ i ∈ Finset.range y.length, (if ¬ g i then y.getD i 0 else 0) := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨fun p => ∃ h : p < y.length, (⟨p, h⟩ : Fin y.length) ∈ A, ?_⟩
    have := pred_sum_iff y (fun p => ∃ h : p < y.length, (⟨p, h⟩ : Fin y.length) ∈ A) A
      (fun p h => ⟨fun hh => ⟨h, hh⟩, fun ⟨h', hh⟩ => hh⟩)
    rw [← this.1, ← this.2]; exact hA
  · rintro ⟨g, hg⟩
    refine ⟨Finset.univ.filter (fun i : Fin y.length => g i.val), ?_⟩
    have := pred_sum_iff y g (Finset.univ.filter (fun i : Fin y.length => g i.val))
      (fun p h => by simp)
    rw [this.1, this.2]; exact hg

theorem lemma_1_core (y : List ℕ) (hy : y ≠ []) (hy1 : ∀ v ∈ y, 0 < v) :
    EOInstance (eoOfPartition y) ∧ (PartitionYes y ↔ EOYes (eoOfPartition y)) := by
  refine ⟨?_, (partition_iff y).trans (eoyes_iff y).symm⟩
  unfold EOInstance eoOfPartition
  refine ⟨?_, ?_, ?_, eoAux_pairwise y hy1 1⟩
  · rw [eoAux_length]; exact ⟨y.length, by ring⟩
  · rw [eoAux_length]
    have := List.length_pos_of_ne_nil hy
    omega
  · intro v hv
    have := eoAux_ge y 1 v hv
    omega

end Constr

/-! ## Correctness of the reduction -/

theorem Fred_correct (w : List BSym) : w ∈ positivePartitionLang ↔ Fred w ∈ evenOddLang := by
  constructor
  · rintro ⟨y, hne, hpos, hyes, rfl⟩
    rw [Fred_valid y hne hpos]
    obtain ⟨hinst, hiff⟩ := lemma_1_core y hne hpos
    exact ⟨_, hinst, hiff.1 hyes, rfl⟩
  · rintro ⟨x, hinst, hyes, hx⟩
    by_cases hw : ∃ sl : List ℕ, sl ≠ [] ∧ (∀ v ∈ sl, 0 < v) ∧ w = encNats sl
    · obtain ⟨sl, hne, hpos, rfl⟩ := hw
      rw [Fred_valid sl hne hpos] at hx
      have hxe := encNats_inj hx
      subst hxe
      obtain ⟨-, hiff⟩ := lemma_1_core sl hne hpos
      exact ⟨sl, hne, hpos, hiff.2 hyes, rfl⟩
    · rw [Fred_invalid hw] at hx
      have := encNats_eq_nil hx.symm
      subst this
      exact absurd hinst.2.1 (by simp)

end GTWPPEO

open GTWSched.NPC CookPvsNP ProjSchedTW.Complexity in
theorem solution : PolyReducible positivePartitionLang evenOddLang :=
  ⟨GTWPPEO.Fred, CookPvsNP.stack_program_polytime GTWPPEO.mainProg .inp .out GTWPPEO.Fred 2000
    GTWPPEO.Fred_exec, GTWPPEO.Fred_correct⟩
