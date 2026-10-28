-- Prove2me | solution 1 for BitDFT.trim_reverse_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:28:14.141992+00:00
-- url     : https://prove2.me/submissions/32b1357e-64a1-4c35-babd-a71f77cff358

import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn
import Definitions.Def_BitDFT_BinaryCounter
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Induction
import Definitions.Def_BitDFT_TrimReverse
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.GetD


namespace BitDFT.CanonicalHeaders
open IntMul

theorem bin_succ (k z : ℕ) : bin (k+1) z = bin k (z/2) ++ [z.testBit 0] := by
  unfold bin
  rw [List.ofFn_succ',List.concat_eq_append]
  congr 1
  · congr 1
    funext i
    rw [Nat.testBit_div_two]
    congr 1
    simp only [Fin.val_castSucc]
    omega
  · simp

theorem val_append_bit (w : List Bool) (b : Bool) : val (w++[b]) = 2*val w+b.toNat := by
  simp [val,List.foldl_append]

theorem low_bit (z : ℕ) : (z.testBit 0).toNat = z%2 := by
  have h := Nat.mod_lt z (by decide : 0 < 2)
  simp only [Nat.testBit_eq_decide_div_mod_eq,Nat.pow_zero,Nat.div_one]
  by_cases hz : z%2 = 1
  · simp [hz]
  · have h0 : z%2 = 0 := by omega
    simp [h0]

theorem val_bin (k z : ℕ) (hz : z < 2^k) : val (bin k z) = z := by
  induction k generalizing z with
  | zero =>
    have h : z=0 := by simpa using hz
    subst z
    rfl
  | succ k ih =>
    rw [bin_succ,val_append_bit,ih,low_bit]
    · omega
    · have hpow : 2^(k+1) = 2^k*2 := pow_succ _ _
      omega

theorem canonical (n : ℕ) (hn : 1 ≤ n) :
    ∃ tail, bin n.size n = true::tail ∧ tail.length+1=n.size ∧ val (true::tail)=n := by
  have hs : 0 < n.size := Nat.size_pos.mpr (by omega)
  have hb : n.testBit (n.size-1) = true := by
    apply Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt
    · exact Nat.lt_size.mp (by omega)
    · simpa [Nat.sub_add_cancel hs] using Nat.lt_size_self n
  have hval := val_bin n.size n (Nat.lt_size_self n)
  have hlen : (bin n.size n).length = n.size := by simp [bin]
  cases he : bin n.size n with
  | nil => simp [he] at hlen; omega
  | cons b tail =>
    have hhead := congrArg (fun l : List Bool => l[0]?) he
    have hzero : n.size-1-0 = n.size-1 := by omega
    simp [bin,List.getElem?_ofFn,hs,hzero,hb] at hhead
    subst b
    refine ⟨tail,rfl,?_,?_⟩
    · simpa [he] using hlen
    · simpa [he] using hval

end BitDFT.CanonicalHeaders



namespace BitDFT.BinaryCounter

private theorem val_append_bit (w : List Bool) (b : Bool) :
    IntMul.val (w++[b]) = 2*IntMul.val w+b.toNat := by
  simp [IntMul.val,List.foldl_append]

private theorem value_reverse (w : List Bool) : value w.reverse = IntMul.val w := by
  suffices h : ∀ a : List Bool, value a = IntMul.val a.reverse by simpa using h w.reverse
  intro a
  induction a with
  | nil => rfl
  | cons b a ih =>
    rw [List.reverse_cons,val_append_bit]
    simp only [value,ih]
    omega

private theorem value_append (a b : List Bool) :
    value (a++b) = value a + 2^a.length*value b := by
  induction a with
  | nil => simp [value]
  | cons x a ih => simp [value,ih,pow_succ]; ring

private theorem value_zero (a : List Bool) : value a = 0 ↔ ∀ b ∈ a, b = false := by
  induction a with
  | nil => simp [value]
  | cons b a ih => cases b <;> simp [value,ih]

/-- On a canonical nonzero binary field, the power-of-two flag is exactly the
    assertion that every bit after the first one is zero. -/
theorem power_flag (tail : List Bool) :
    IntMul.val (true::tail) = 2^tail.length ↔ ∀ b ∈ tail, b = false := by
  rw [← value_reverse,List.reverse_cons,value_append]
  simp only [List.length_reverse,value,Bool.toNat_true,Nat.mul_zero,Nat.add_zero,Nat.mul_one]
  have hz : value tail.reverse = 0 ↔ ∀ b ∈ tail, b = false := by
    simpa using value_zero tail.reverse
  constructor
  · intro h
    apply hz.mp
    omega
  · intro h
    rw [hz.mpr h]
    simp


private theorem value_lt (a : List Bool) : value a < 2^a.length := by
  induction a with
  | nil => simp [value]
  | cons b a ih => cases b <;> simp [value,pow_succ] <;> omega

private theorem leading_one_value (tail : List Bool) :
    IntMul.val (true::tail) = value tail.reverse + 2^tail.length := by
  rw [← value_reverse,List.reverse_cons,value_append]
  simp [value]

theorem canonical_size (tail : List Bool) : (IntMul.val (true::tail)).size = tail.length+1 := by
  have hv : value tail.reverse < 2^tail.length := by simpa using value_lt tail.reverse
  have he := leading_one_value tail
  have hlo : 2^tail.length ≤ IntMul.val (true::tail) := by omega
  have hhi : IntMul.val (true::tail) < 2^(tail.length+1) := by rw [pow_succ]; omega
  have hslo := Nat.lt_size.mpr hlo
  have hshi := Nat.size_le.mpr hhi
  omega

theorem canonical_positive (tail : List Bool) : 1 ≤ IntMul.val (true::tail) := by
  have he := leading_one_value tail
  have hp : 0 < 2^tail.length := pow_pos (by decide) _
  omega

end BitDFT.BinaryCounter



namespace BitDFT.TrimWord
open IntMul BinaryCounter

private theorem value_zero_append (w : List Bool) : value (w++[false]) = value w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [value,ih]

theorem split_positive (w : List Bool) (hw : 0 < value w) :
    ∃ u k, w = u++[true]++List.replicate k false := by
  induction w using List.reverseRecOn with
  | nil => simp [value] at hw
  | append_singleton w b ih =>
    cases b with
    | true => exact ⟨w,0,by simp⟩
    | false =>
      rw [value_zero_append] at hw
      obtain ⟨u,k,h⟩ := ih hw
      refine ⟨u,k+1,?_⟩
      rw [h,List.replicate_add]
      simp [List.append_assoc]

theorem bin_val (w : List Bool) : bin w.length (val w) = w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w b ih =>
    simp only [List.length_append,List.length_singleton]
    rw [CanonicalHeaders.bin_succ,CanonicalHeaders.val_append_bit]
    have hdiv : (2*val w+b.toNat)/2 = val w := by cases b <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega
    rw [hdiv,ih]
    congr 1
    cases b <;> simp [Nat.testBit_eq_decide_div_mod_eq]

end BitDFT.TrimWord



namespace BitDFT.TrimReverse
open IntMul

private theorem cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem protect_same (a : Sym) (d : Move)
    (h : a = .start → d ≠ .left) : protect a (a,d) = (a,d) := by
  by_cases ha : a = .start
  · simp [protect, HeaderReader.protect, ha, h ha]
  · simp [protect, HeaderReader.protect, ha]

private theorem positive_not_start (w : List Bool) (p : ℕ) (hp : 0 < p) :
    machine.tapeOf (w.map machine.bitSym) p ≠ TapeCopy.Sym.start := by
  cases p with
  | zero => omega
  | succ p =>
    simp only [MultitapeTM.tapeOf]
    by_cases h : p < w.length
    · rw [List.getD_eq_getElem _ _ (by simpa using h)]
      simp only [List.getElem_map]
      cases w[p] <;> decide
    · rw [List.getD_eq_default _ _ (by simpa using (Nat.le_of_not_gt h))]
      decide

private theorem tape_append (w : List Sym) (a : Sym) :
    Function.update (machine.tapeOf w) (w.length + 1) a = machine.tapeOf (w ++ [a]) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p = w.length
    · subst p; simp [MultitapeTM.tapeOf, List.getD_append_right]
    · rw [Function.update_of_ne (by omega : p+1 ≠ w.length+1)]
      simp only [MultitapeTM.tapeOf]
      by_cases hlt : p < w.length
      · rw [List.getD_append _ _ _ _ hlt]
      · have hge : w.length ≤ p := by omega
        rw [List.getD_eq_default _ _ hge, List.getD_append_right _ _ _ _ hge]
        exact (List.getD_eq_default _ _ (by simp; omega)).symm

private theorem tape_erase (w : List Sym) (a : Sym) :
    Function.update (machine.tapeOf (w ++ [a])) (w.length + 1) .blank = machine.tapeOf w := by
  rw [← tape_append]
  rw [Function.update_idem]
  have he : machine.tapeOf w (w.length+1) = TapeCopy.Sym.blank := by
    simp [MultitapeTM.tapeOf]
  rw [← he]
  exact Function.update_eq_self _ _

private theorem keep_step (base : machine.Cfg) (q q' : State) (src dst : List Bool)
    (p p' : ℕ) (d : Move)
    (ht : transition q (fun i => (frame base q src dst p).cells i ((frame base q src dst p).head i)) =
      (q',fun i => ((frame base q src dst p).cells i ((frame base q src dst p).head i),
        if i = 2 then d else Move.stay)))
    (hp : (match d with | .left => p-1 | .stay => p | .right => p+1) = p') :
    machine.step (frame base q src dst p) = frame base q' src dst p' := by
  let c := frame base q src dst p
  change transition c.state (fun i => c.cells i (c.head i)) = _ at ht
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [c,frame]
    cases d <;> exact hp

theorem start_step (base : machine.Cfg) (w : List Bool) :
    machine.step (initial base w) = frame base .scan w [] 1 := by
  let c := initial base w
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.scan,fun i => (c.cells i (c.head i),if i = 3 then Move.right else Move.stay)) := by
    apply Prod.ext
    · rfl
    · funext i
      change protect _ (_,_) = _
      apply protect_same
      intro _; split <;> decide
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [c,initial,frame]

theorem scan_step (base : machine.Cfg) (pre : List Bool) (b : Bool) (rest dst : List Bool) :
    machine.step (frame base .scan (pre++b::rest) dst (pre.length+1)) =
      frame base .scan (pre++b::rest) dst (pre.length+2) := by
  let c := frame base .scan (pre++b::rest) dst (pre.length+1)
  have h2 : c.cells 2 (c.head 2) = machine.bitSym b := by simp [c,frame,MultitapeTM.tapeOf]
  have hb : c.cells 2 (c.head 2) = TapeCopy.Sym.zero ∨ c.cells 2 (c.head 2) = TapeCopy.Sym.one := by
    rw [h2]; cases b <;> simp [MultitapeTM.bitSym]
  apply keep_step _ _ _ _ _ _ _ .right _ (by simp)
  apply Prod.ext
  · change (raw .scan (fun i => c.cells i (c.head i))).1 = _
    simp [raw,hb]
  · funext i
    change protect (c.cells i (c.head i)) ((raw .scan (fun j => c.cells j (c.head j))).2 i) = _
    simp only [raw,hb,if_true]
    apply protect_same
    intro _; split <;> decide

theorem scan_run (base : machine.Cfg) (pre rest dst : List Bool) :
    machine.step^[rest.length] (frame base .scan (pre++rest) dst (pre.length+1)) =
      frame base .scan (pre++rest) dst (pre.length+rest.length+1) := by
  induction rest generalizing pre with
  | nil => simp
  | cons b rest ih =>
    rw [List.length_cons,Function.iterate_succ_apply,scan_step]
    have h := ih (pre++[b])
    simpa [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem scan_done (base : machine.Cfg) (w dst : List Bool) :
    machine.step (frame base .scan w dst (w.length+1)) = frame base .trim w dst w.length := by
  let c := frame base .scan w dst (w.length+1)
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.blank := by simp [c,frame,MultitapeTM.tapeOf]
  apply keep_step _ _ _ _ _ _ _ .left _ (by simp)
  apply Prod.ext
  · change (raw .scan (fun i => c.cells i (c.head i))).1 = _
    simp [raw,h2]
  · funext i
    change protect (c.cells i (c.head i)) ((raw .scan (fun j => c.cells j (c.head j))).2 i) = _
    simp only [raw,h2,reduceCtorEq,or_self,if_false]
    apply protect_same
    by_cases hi : i = 2
    · subst i; simp [h2]
    · simp [hi]

theorem trim_step (base : machine.Cfg) (w dst : List Bool) :
    machine.step (frame base .trim (w++[false]) dst (w.length+1)) =
      frame base .trim w dst w.length := by
  let c := frame base .trim (w++[false]) dst (w.length+1)
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.zero := by simp [c,frame,MultitapeTM.tapeOf,MultitapeTM.bitSym]
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.trim,fun i => (if i = 2 then TapeCopy.Sym.blank else c.cells i (c.head i),if i = 2 then Move.left else Move.stay)) := by
    apply Prod.ext
    · change (raw .trim (fun i => c.cells i (c.head i))).1 = _
      simp [raw,h2]
    · funext i
      change protect (c.cells i (c.head i)) ((raw .trim (fun j => c.cells j (c.head j))).2 i) = _
      simp only [raw,h2,if_true]
      by_cases hi : i = 2
      · subst i; simp [h2,protect,HeaderReader.protect]
      · simp only [hi,if_false]; exact protect_same _ .stay (by intro _; decide)
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · simpa [c,frame,List.map_append,MultitapeTM.bitSym] using tape_erase (w.map machine.bitSym) (machine.bitSym false)
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [c,frame]

theorem trim_run (base : machine.Cfg) (w dst : List Bool) (k : ℕ) :
    machine.step^[k] (frame base .trim (w++List.replicate k false) dst (w.length+k)) =
      frame base .trim w dst w.length := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k+1=k+1 from rfl,List.replicate_add]
    simp only [List.replicate_one,← List.append_assoc]
    have hlen : w.length+k+1=(w++List.replicate k false).length+1 := by simp
    rw [show w.length+(k+1)=w.length+k+1 by omega,hlen,
      Function.iterate_succ_apply,trim_step]
    simpa using ih

theorem trim_done (base : machine.Cfg) (w dst : List Bool) :
    machine.step (frame base .trim (w++[true]) dst (w.length+1)) =
      frame base .copy (w++[true]) dst (w.length+1) := by
  let c := frame base .trim (w++[true]) dst (w.length+1)
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.one := by simp [c,frame,MultitapeTM.tapeOf,MultitapeTM.bitSym]
  apply keep_step _ _ _ _ _ _ _ .stay _ rfl
  apply Prod.ext
  · change (raw .trim (fun i => c.cells i (c.head i))).1 = _
    simp [raw,h2]
  · funext i
    change protect (c.cells i (c.head i)) ((raw .trim (fun j => c.cells j (c.head j))).2 i) = _
    simp only [raw,h2,reduceCtorEq,if_false,ite_self]
    exact protect_same _ .stay (by intro _; decide)

theorem copy_step (base : machine.Cfg) (pre dst : List Bool) (b : Bool) :
    machine.step (frame base .copy (pre++[b]) dst (pre.length+1)) =
      frame base .copy pre (dst++[b]) pre.length := by
  let c := frame base .copy (pre++[b]) dst (pre.length+1)
  have h2 : c.cells 2 (c.head 2) = machine.bitSym b := by simp [c,frame,MultitapeTM.tapeOf]
  have hn : c.cells 2 (c.head 2) ≠ TapeCopy.Sym.start := by rw [h2]; cases b <;> decide
  have h3 : c.cells 3 (c.head 3) = TapeCopy.Sym.blank := by simp [c,frame,MultitapeTM.tapeOf]
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.copy,fun i => (if i = 2 then TapeCopy.Sym.blank else if i = 3 then machine.bitSym b else c.cells i (c.head i),
        if i = 2 then Move.left else if i = 3 then Move.right else Move.stay)) := by
    apply Prod.ext
    · change (raw .copy (fun i => c.cells i (c.head i))).1 = _
      simp [raw,hn]
    · funext i
      change protect (c.cells i (c.head i)) ((raw .copy (fun j => c.cells j (c.head j))).2 i) = _
      simp only [raw,hn,if_false]
      fin_cases i
      · exact protect_same _ .stay (by intro _; decide)
      · exact protect_same _ .stay (by intro _; decide)
      · simp [h2,protect,HeaderReader.protect]; cases b <;> simp [MultitapeTM.bitSym]
      · simp [h2,h3,protect,HeaderReader.protect]; cases b <;> simp [MultitapeTM.bitSym]
      · exact protect_same _ .stay (by intro _; decide)
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · simpa [c,frame,List.map_append] using tape_erase (pre.map machine.bitSym) (machine.bitSym b)
    · simpa [c,frame,List.map_append] using tape_append (dst.map machine.bitSym) (machine.bitSym b)
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [c,frame]

theorem copy_run (base : machine.Cfg) (src dst : List Bool) :
    machine.step^[src.length] (frame base .copy src dst src.length) =
      frame base .copy [] (dst++src.reverse) 0 := by
  induction src using List.reverseRecOn generalizing dst with
  | nil => simp
  | append_singleton pre b ih =>
    simp only [List.length_append,List.length_singleton]
    rw [Function.iterate_succ_apply,copy_step,ih]
    simp [List.reverse_append,List.append_assoc]

theorem copy_done (base : machine.Cfg) (dst : List Bool) :
    machine.step (frame base .copy [] dst 0) = frame base .halt [] dst 0 := by
  let c := frame base .copy [] dst 0
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.start := rfl
  apply keep_step _ _ _ _ _ _ _ .stay _ rfl
  apply Prod.ext
  · change (raw .copy (fun i => c.cells i (c.head i))).1 = _
    simp [raw,h2]
  · funext i
    change protect (c.cells i (c.head i)) ((raw .copy (fun j => c.cells j (c.head j))).2 i) = _
    simp only [raw,h2,if_true,ite_self]
    exact protect_same _ .stay (by intro _; decide)

theorem trim_reverse_run (base : machine.Cfg) (u : List Bool) (k : ℕ) :
    let w := u++[true]++List.replicate k false
    machine.step^[2*w.length+4] (initial base w) =
      frame base .halt [] (true::u.reverse) 0 := by
  dsimp only
  let w := u++[true]++List.replicate k false
  have ht : machine.step^[2*w.length+4] (initial base w) =
      machine.step^[1] (machine.step^[(u++[true]).length] (machine.step^[1]
        (machine.step^[k] (machine.step^[1] (machine.step^[w.length]
          (machine.step^[1] (initial base w))))))) := by
    simp only [← Function.iterate_add_apply]
    congr 1
    simp [w]
    omega
  rw [ht]
  simp only [Function.iterate_one]
  rw [start_step]
  have hscan := scan_run base [] w []
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hscan
  rw [hscan,scan_done]
  change machine.step (machine.step^[(u++[true]).length] (machine.step
    (machine.step^[k] (frame base .trim (u++[true]++List.replicate k false) []
      (u++[true]++List.replicate k false).length)))) = _
  rw [show (u++[true]++List.replicate k false).length = (u++[true]).length+k by simp; omega,trim_run]
  rw [show (u++[true]).length = u.length+1 by simp,trim_done]
  have hcopy := copy_run base (u++[true]) []
  simp only [List.length_append,List.length_singleton,List.nil_append] at hcopy
  rw [hcopy,copy_done]
  simp

end BitDFT.TrimReverse




namespace BitDFT.TrimWord
open IntMul BinaryCounter

theorem value_to_val (w : List Bool) : value w = val w.reverse := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [List.reverse_cons,CanonicalHeaders.val_append_bit]
    simp only [value,ih]
    omega

theorem value_zero_padding (w : List Bool) (k : ℕ) :
    value (w++List.replicate k false) = value w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_add]
    simp only [List.replicate_one,← List.append_assoc,value_zero_append,ih]

theorem canonical_output (u : List Bool) (k : ℕ) :
    let w := u++[true]++List.replicate k false
    bin (value w).size (value w) = true::u.reverse := by
  dsimp only
  rw [value_zero_padding,value_to_val]
  simp only [List.reverse_append,List.reverse_singleton,List.singleton_append]
  have h := bin_val (true::u.reverse)
  rw [BinaryCounter.canonical_size]
  simpa only [List.length_cons,List.length_reverse] using h

end BitDFT.TrimWord
open BitDFT BitDFT.TrimReverse IntMul

theorem solution (base : machine.Cfg) (w : List Bool) (hw : 0 < BinaryCounter.value w) :
    machine.step^[2*w.length+4] (initial base w) =
      frame base .halt [] (bin (BinaryCounter.value w).size (BinaryCounter.value w)) 0 := by
  obtain ⟨u,k,rfl⟩ := TrimWord.split_positive w hw
  rw [TrimWord.canonical_output]
  exact trim_reverse_run base u k
