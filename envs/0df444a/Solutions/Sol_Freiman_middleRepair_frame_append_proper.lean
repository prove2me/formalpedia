-- Prove2me | solution 1 for Freiman.middleRepair_frame_append_proper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:41:00.513234+00:00
-- url     : https://prove2.me/submissions/cbc0bc99-dbe3-48ea-97b7-c47fe6a151ea

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Choose
import Mathlib.Tactic.SplitIfs

open Freiman

namespace M8_Freiman_middleRepair_frame_append_proper

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

end M8_Freiman_middleRepair_frame_append_proper


theorem solution :
  ∀ (s : MiddleRepairFrame) (u v : List ℕ+), middleDigits123 u → middleDigits123 v →
  0 < u.length+v.length → middleProper (middleRepairPhysical s)
    (middleRepairPhysical ⟨⟨s.core.left++u,s.core.right++v⟩,s.reflected⟩) := by
  exact M8_Freiman_middleRepair_frame_append_proper.append_proper

#print axioms solution
