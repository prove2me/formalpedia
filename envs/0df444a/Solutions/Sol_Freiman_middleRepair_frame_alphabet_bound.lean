-- Prove2me | solution 1 for Freiman.middleRepair_frame_alphabet_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:45:32.251802+00:00
-- url     : https://prove2.me/submissions/8339c5fa-98cc-4840-8d39-0e7ebc808c8f

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Choose
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.List.GetD

open Freiman

namespace M8_Freiman_middleRepair_frame_alphabet_bound

theorem normalized_idem (c : MiddleCore) :
    middleNormalized (middleNormalized c) = middleNormalized c := by
  by_cases h : middleWidth c.right ≤ middleWidth c.left
  · simp only [middleNormalized, if_pos h]
  · have hrev : middleWidth c.left ≤ middleWidth c.right := le_of_lt (lt_of_not_ge h)
    simp only [middleNormalized, if_neg h, if_pos hrev]

theorem normalized_regular (c : MiddleCore) (h : middleRegular c) :
    middleRegular (middleNormalized c) := by
  unfold middleNormalized
  split_ifs
  · exact h
  · exact ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

theorem normalized_cover (c : MiddleCore) :
    middleCover (middleNormalized c) = middleCover c := by
  simp only [middleCover, middleBounds, normalized_idem]

theorem child_normalized (c : MiddleCore) (u v : List ℕ+) :
    middleRepairChild (middleNormalized c) u v = middleRepairChild c u v := by
  simp only [middleRepairChild, middleRepairRawChild, normalized_idem]

theorem normalized_good (c : MiddleCore) :
    middleRepairGood (middleNormalized c) ↔ middleRepairGood c := by
  simp only [middleRepairGood, child_normalized]

theorem normalize_core (s : MiddleRepairFrame) :
    (middleRepairNormalizeFrame s).core = middleNormalized s.core := by
  unfold middleRepairNormalizeFrame middleNormalized
  split_ifs <;> rfl

theorem normalize_invariant (s : MiddleRepairFrame) :
    middleRepairFrameInvariant (middleRepairNormalizeFrame s) := by
  unfold middleRepairNormalizeFrame
  split_ifs with h
  · exact h
  · exact le_of_lt (lt_of_not_ge h)

theorem normalize_physical (s : MiddleRepairFrame) :
    middleRepairPhysical (middleRepairNormalizeFrame s) = middleRepairPhysical s := by
  unfold middleRepairNormalizeFrame
  split_ifs with h
  · rfl
  · rcases s with ⟨⟨l,r⟩,b⟩
    cases b <;> rfl

theorem start_core (c : MiddleCore) :
    (middleRepairStart c).core = middleNormalized c :=
  normalize_core ⟨c, false⟩

theorem start_invariant (c : MiddleCore) :
    middleRepairFrameInvariant (middleRepairStart c) :=
  normalize_invariant ⟨c, false⟩

theorem start_physical (c : MiddleCore) :
    middleRepairPhysical (middleRepairStart c) = c := by
  exact normalize_physical ⟨c, false⟩

theorem extend_core (s : MiddleRepairFrame) (u v : List ℕ+) :
    (middleRepairExtend s u v).core = middleRepairChild s.core u v := by
  simp only [middleRepairExtend, normalize_core, middleRepairChild, middleRepairRawChild]

theorem extend_invariant (s : MiddleRepairFrame) (u v : List ℕ+) :
    middleRepairFrameInvariant (middleRepairExtend s u v) := by
  exact normalize_invariant _

theorem append_proper (s : MiddleRepairFrame) (u v : List ℕ+)
    (hu : middleDigits123 u) (hv : middleDigits123 v) (hlen : 0 < u.length+v.length) :
    middleProper (middleRepairPhysical s)
      (middleRepairPhysical ⟨⟨s.core.left++u,s.core.right++v⟩,s.reflected⟩) := by
  rcases s with ⟨⟨l,r⟩,b⟩
  cases b
  · exact ⟨u,v,hu,hv,rfl,rfl,hlen⟩
  · exact ⟨v,u,hv,hu,rfl,rfl,by omega⟩

theorem extend_proper (s : MiddleRepairFrame) (u v : List ℕ+)
    (hu : middleDigits123 u) (hv : middleDigits123 v) (hlen : 0 < u.length+v.length) :
    middleProper (middleRepairPhysical s) (middleRepairPhysical (middleRepairExtend s u v)) := by
  unfold middleRepairExtend
  rw [normalize_physical, ← normalize_physical s]
  exact append_proper _ u v hu hv hlen

theorem raw_child_proper (c : MiddleCore) (u v : List ℕ+)
    (hu : middleDigits123 u) (hv : middleDigits123 v) (hlen : 0 < u.length+v.length) :
    middleProper (middleNormalized c) (middleRepairRawChild c u v) := by
  exact ⟨u,v,hu,hv,rfl,rfl,hlen⟩

theorem reflect_compatible (c : MiddleCore) (a : ℤ → ℕ+) (h : middleCompatible c a) :
    middleCompatible (middleRepairSwap c) (middleRepairReflectDigits a) := by
  rcases h with ⟨h0,hl,hr,hlb,hrb⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [middleRepairReflectDigits] using h0
  · intro n hn
    simpa [middleRepairReflectDigits, middleRepairSwap, add_comm] using hr n hn
  · intro n hn
    simpa [middleRepairReflectDigits, middleRepairSwap, neg_add_rev, sub_eq_add_neg,
      add_comm] using hl n hn
  · intro n hn
    simpa [middleRepairReflectDigits, middleRepairSwap, add_comm] using hrb n hn
  · intro n hn
    simpa [middleRepairReflectDigits, middleRepairSwap, neg_add_rev, sub_eq_add_neg,
      add_comm] using hlb n hn

theorem reflect_localValue (a : ℤ → ℕ+) :
    localValue (middleRepairReflectDigits a) 0 = localValue a 0 := by
  simp only [localValue, middleRepairReflectDigits, neg_zero, zero_sub, neg_sub, neg_neg,
    zero_add]
  have hfun : (fun n : ℕ => a (-((n : ℤ)+1))) = (fun n : ℕ => a (-(n : ℤ)-1)) := by
    funext n
    congr 1
    omega
  rw [hfun]
  ring

theorem reflect_act_localValue (b : Bool) (a : ℤ → ℕ+) :
    localValue (middleRepairActDigits b a) 0 = localValue a 0 := by
  cases b
  · rfl
  · exact reflect_localValue a

theorem reflect_realized (b : Bool) (c : MiddleCore) (t : ℝ)
    (h : middleRealized (middleRepairAct b c) t) : middleRealized c t := by
  cases b
  · exact h
  · rcases h with ⟨a,ha,ht⟩
    refine ⟨middleRepairReflectDigits a, ?_, (reflect_localValue a).trans ht⟩
    simpa only [middleRepairSwap, middleRepairAct, Bool.true_eq, if_true] using
      reflect_compatible (middleRepairSwap c) a ha

theorem realized_normalized (c : MiddleCore) (t : ℝ)
    (h : middleRealized (middleNormalized c) t) : middleRealized c t := by
  unfold middleNormalized at h
  split_ifs at h with hc
  · exact h
  · exact reflect_realized true c t h

theorem compatible_core (s : MiddleRepairFrame) (a : ℤ → ℕ+)
    (h : middleCompatible (middleRepairPhysical s) a) :
    middleCompatible s.core (middleRepairActDigits s.reflected a) := by
  rcases s with ⟨c,b⟩
  cases b
  · exact h
  · simpa only [middleRepairSwap, middleRepairAct, middleRepairActDigits,
      Bool.true_eq, if_true] using reflect_compatible (middleRepairSwap c) a h

theorem path_labels (c : MiddleCore) (t : ℝ) (p : ℕ → MiddleCore)
    (h : middleRepairPath c t p) :
    ∃ u v : ℕ → List ℕ+, ∀ n : ℕ, middleDigits123 (u n) ∧ middleDigits123 (v n) ∧
      0 < (u n).length+(v n).length ∧ p (n+1)=middleRepairChild (p n) (u n) (v n) := by
  have hstep := fun n => (h.2 n).2.2.2
  choose u v hu hv hlen heq using hstep
  exact ⟨u,v,fun n => ⟨hu n,hv n,hlen n,heq n⟩⟩

theorem prefix_compatible
    (hmon : ∀ (c d : MiddleCore) (a : ℤ → ℕ+), middleProper c d →
      middleCompatible d a → middleCompatible c a)
    (p : ℕ → MiddleCore) (hp : ∀ n : ℕ, middleProper (p n) (p (n+1)))
    (n m : ℕ) (hnm : n≤m) (a : ℤ → ℕ+) (ha : middleCompatible (p m) a) :
    middleCompatible (p n) a := by
  induction hnm with
  | refl => exact ha
  | @step m hnm ih => exact ih (hmon (p m) (p (m+1)) a (hp m) ha)

theorem path_build
    (hstart : ∀ c : MiddleCore, (middleRepairStart c).core=middleNormalized c)
    (hinv : ∀ c : MiddleCore, middleRepairFrameInvariant (middleRepairStart c))
    (hext : ∀ (s : MiddleRepairFrame) (u v : List ℕ+),
      (middleRepairExtend s u v).core=middleRepairChild s.core u v)
    (heinv : ∀ (s : MiddleRepairFrame) (u v : List ℕ+),
      middleRepairFrameInvariant (middleRepairExtend s u v))
    (c : MiddleCore) (t : ℝ) (p : ℕ → MiddleCore) (u v : ℕ → List ℕ+)
    (hp : middleRepairPath c t p)
    (huv : ∀ n : ℕ, middleDigits123 (u n) ∧ middleDigits123 (v n) ∧
      0 < (u n).length+(v n).length ∧ p (n+1)=middleRepairChild (p n) (u n) (v n)) :
    ∃ s : ℕ → MiddleRepairFrame, middleRepairLift c t p s := by
  let s : ℕ → MiddleRepairFrame :=
    fun n => Nat.rec (middleRepairStart c) (fun n s => middleRepairExtend s (u n) (v n)) n
  have hs0 : s 0 = middleRepairStart c := rfl
  have hss (n : ℕ) : s (n+1) = middleRepairExtend (s n) (u n) (v n) := rfl
  have hcore (n : ℕ) : (s n).core = p n := by
    induction n with
    | zero => exact (hstart c).trans hp.1.symm
    | succ n ih => rw [hss,hext,ih,← (huv n).2.2.2]
  refine ⟨s, ⟨hs0, ?_⟩, hcore⟩
  intro n
  refine ⟨?_,?_,?_,?_,u n,v n,(huv n).1,(huv n).2.1,(huv n).2.2.1,hss n⟩
  · cases n with
    | zero => exact hinv c
    | succ n => exact heinv _ _ _
  · rw [hcore]; exact (hp.2 n).1
  · rw [hcore]; exact (hp.2 n).2.1
  · rw [hcore]; exact (hp.2 n).2.2.1

theorem path_choice_normalized
    (hstep : ∀ (c : MiddleCore) (t : ℝ), middleRegular c → middleRepairGood c →
      t∈middleCover c → middleRealized c t ∨ ∃ d : MiddleCore,
        middleRegular d ∧ middleRepairGood d ∧ middleRepairProper c d ∧ t∈middleCover d)
    (hmon : ∀ (c d : MiddleCore) (t : ℝ), middleRepairProper c d →
      middleRealized d t → middleRealized c t)
    (c : MiddleCore) (t : ℝ) (hnorm : middleNormalized c=c)
    (hc : middleRegular c) (hgood : middleRepairGood c) (ht : t∈middleCover c) :
    middleRealized c t ∨ ∃ p : ℕ → MiddleCore, middleRepairPath c t p := by
  classical
  by_cases hreal : middleRealized c t
  · exact Or.inl hreal
  right
  let S := {d : MiddleCore // middleRegular d ∧ middleRepairGood d ∧
    t∈middleCover d ∧ ¬middleRealized d t}
  have hnext (d : S) : ∃ e : S, middleRepairProper d.val e.val := by
    rcases hstep d.val t d.property.1 d.property.2.1 d.property.2.2.1 with h | ⟨e,he,hg,hp,ht⟩
    · exact (d.property.2.2.2 h).elim
    · exact ⟨⟨e,he,hg,ht,fun h => d.property.2.2.2 (hmon d.val e t hp h)⟩,hp⟩
  let start : S := ⟨c,hc,hgood,ht,hreal⟩
  let next (d : S) : S := (hnext d).choose
  let s : ℕ → S := fun n => Nat.rec start (fun _ d => next d) n
  refine ⟨fun n => (s n).val, ?_, ?_⟩
  · exact hnorm.symm
  · intro n
    exact ⟨(s n).property.1,(s n).property.2.1,(s n).property.2.2.1,
      (hnext (s n)).choose_spec⟩

theorem normalized_length (c : MiddleCore) :
    (middleNormalized c).left.length+(middleNormalized c).right.length =
      c.left.length+c.right.length := by
  unfold middleNormalized
  split_ifs <;> simp [Nat.add_comm]

theorem child_length (c : MiddleCore) (u v : List ℕ+) :
    (middleRepairChild c u v).left.length+(middleRepairChild c u v).right.length =
      c.left.length+c.right.length+u.length+v.length := by
  unfold middleRepairChild
  rw [normalized_length]
  dsimp [middleRepairRawChild]
  simp only [List.length_append]
  have h := normalized_length c
  omega

theorem path_length (c : MiddleCore) (t : ℝ) (p : ℕ → MiddleCore)
    (hp : middleRepairPath c t p) (n : ℕ) :
    n+c.left.length+c.right.length ≤ (p n).left.length+(p n).right.length := by
  induction n with
  | zero => rw [hp.1, normalized_length]; omega
  | succ n ih =>
    rcases (hp.2 n).2.2.2 with ⟨u,v,_,_,hpos,heq⟩
    rw [heq,child_length]
    omega

theorem completion_closed (c : MiddleCore) (A : ℕ → ℤ → ℕ+) (a : ℤ → ℕ+)
    (hconv : ∀ i : ℤ, ∀ᶠ n in Filter.atTop, A n i=a i)
    (hc : ∀ᶠ n in Filter.atTop, middleCompatible c (A n)) : middleCompatible c a := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · obtain ⟨k,hka,hkc⟩ := ((hconv 0).and hc).exists
    exact hka.symm.trans hkc.1
  · intro n hn
    obtain ⟨k,hka,hkc⟩ := ((hconv (-(n:ℤ)-1)).and hc).exists
    exact hka.symm.trans (hkc.2.1 n hn)
  · intro n hn
    obtain ⟨k,hka,hkc⟩ := ((hconv ((n:ℤ)+1)).and hc).exists
    exact hka.symm.trans (hkc.2.2.1 n hn)
  · intro n hn
    obtain ⟨k,hka,hkc⟩ := ((hconv (-(n:ℤ)-1)).and hc).exists
    rw [← hka]
    exact hkc.2.2.2.1 n hn
  · intro n hn
    obtain ⟨k,hka,hkc⟩ := ((hconv ((n:ℤ)+1)).and hc).exists
    rw [← hka]
    exact hkc.2.2.2.2 n hn

theorem compatible_nonempty (c : MiddleCore) : ∃ a : ℤ → ℕ+, middleCompatible c a := by
  let a : ℤ → ℕ+ := fun i => if i=0 then 4 else if i<0
    then c.left.getD ((-i-1).toNat) 1 else c.right.getD ((i-1).toNat) 1
  have hl (n : ℕ) : a (-(n:ℤ)-1) = c.left.getD n 1 := by
    dsimp [a]
    rw [if_neg (by omega), if_pos (by omega)]
    congr 1
    omega
  have hr (n : ℕ) : a ((n:ℤ)+1) = c.right.getD n 1 := by
    dsimp [a]
    rw [if_neg (by omega), if_neg (by omega)]
    congr 1
    omega
  refine ⟨a, ?_, ?_, ?_, ?_, ?_⟩
  · simp [a]
  · exact fun n _ => hl n
  · exact fun n _ => hr n
  · intro n hn
    rw [hl n, List.getD_eq_default _ _ hn]
    decide
  · intro n hn
    rw [hr n, List.getD_eq_default _ _ hn]
    decide

theorem list_digit_bound (w : List ℕ+) : ∃ M : ℕ, ∀ n : ℕ, (w.getD n 1 : ℕ) ≤ M := by
  induction w with
  | nil => exact ⟨1,fun n => by simp⟩
  | cons a w ih =>
    obtain ⟨M,hM⟩ := ih
    refine ⟨max (a:ℕ) M, ?_⟩
    intro n
    cases n with
    | zero => exact le_max_left _ _
    | succ n => exact (hM n).trans (le_max_right _ _)

theorem alphabet_bound (c : MiddleCore) :
    ∃ M : ℕ, ∀ a : ℤ → ℕ+, middleCompatible c a → ∀ i : ℤ, (a i : ℕ) ≤ M := by
  obtain ⟨L,hL⟩ := list_digit_bound c.left
  obtain ⟨R,hR⟩ := list_digit_bound c.right
  refine ⟨max 4 (max L R),?_⟩
  intro a ha i
  by_cases h0 : i=0
  · rw [h0,ha.1]
    exact le_max_left _ _
  by_cases hi : i<0
  · let n := (-i-1).toNat
    have heq : i = -(n:ℤ)-1 := by dsimp [n]; omega
    rw [heq]
    by_cases hn : n<c.left.length
    · rw [ha.2.1 n hn]
      exact (hL n).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (ha.2.2.2.1 n (by omega)).trans (by omega)
  · let n := (i-1).toNat
    have heq : i = (n:ℤ)+1 := by dsimp [n]; omega
    rw [heq]
    by_cases hn : n<c.right.length
    · rw [ha.2.2.1 n hn]
      exact (hR n).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (ha.2.2.2.2 n (by omega)).trans (by omega)

end M8_Freiman_middleRepair_frame_alphabet_bound


theorem solution :
  ∀ c : MiddleCore, ∃ M : ℕ, ∀ a : ℤ → ℕ+, middleCompatible c a → ∀ i : ℤ, (a i : ℕ) ≤ M := by
  exact M8_Freiman_middleRepair_frame_alphabet_bound.alphabet_bound

#print axioms solution
