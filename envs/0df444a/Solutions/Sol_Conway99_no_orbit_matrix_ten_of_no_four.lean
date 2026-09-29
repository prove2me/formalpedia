-- Prove2me | solution 1 for Conway99.no_orbit_matrix_ten_of_no_four
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-08T01:20:00.308533+00:00
-- url     : https://prove2.me/submissions/7a30e263-1c50-4459-a8ad-579774733a4d

import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.BitVec
import Mathlib.Data.FinEnum
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic


namespace ConwayLocalKernel

abbrev W := Fin 6

def pairIndex (i j : W) : Nat :=
  let a := min i.val j.val
  let b := max i.val j.val
  a * (11 - a) / 2 + (b - a - 1)

def edge (h : BitVec 15) (i j : W) : Bool :=
  if i = j then false else h.getLsbD (pairIndex i j)

def xmem (x : BitVec 6) (i : W) : Bool :=
  x.getLsbD i

def bnat (b : Bool) : Nat :=
  if b then 1 else 0

def degree (h : BitVec 15) (i : W) : Nat :=
  bnat (edge h i 0) + bnat (edge h i 1) + bnat (edge h i 2) +
  bnat (edge h i 3) + bnat (edge h i 4) + bnat (edge h i 5)

def commonParity (h : BitVec 15) (i j : W) : Bool :=
  (edge h i 0 && edge h 0 j) ^^
  (edge h i 1 && edge h 1 j) ^^
  (edge h i 2 && edge h 2 j) ^^
  (edge h i 3 && edge h 3 j) ^^
  (edge h i 4 && edge h 4 j) ^^
  (edge h i 5 && edge h 5 j)

def neighborsInXParity (h : BitVec 15) (x : BitVec 6) (i : W) : Bool :=
  (edge h i 0 && xmem x 0) ^^
  (edge h i 1 && xmem x 1) ^^
  (edge h i 2 && xmem x 2) ^^
  (edge h i 3 && xmem x 3) ^^
  (edge h i 4 && xmem x 4) ^^
  (edge h i 5 && xmem x 5)

def xcard (x : BitVec 6) : Nat :=
  bnat (xmem x 0) + bnat (xmem x 1) + bnat (xmem x 2) +
  bnat (xmem x 3) + bnat (xmem x 4) + bnat (xmem x 5)

def fullDegree (h : BitVec 15) (x : BitVec 6) (i : W) : Nat :=
  degree h i + 2 * bnat (xmem x i)

def degreeFourCount (h : BitVec 15) (x : BitVec 6) : Nat :=
  2 * bnat (xcard x = 2) +
  bnat (fullDegree h x 0 = 4) + bnat (fullDegree h x 1 = 4) +
  bnat (fullDegree h x 2 = 4) + bnat (fullDegree h x 3 = 4) +
  bnat (fullDegree h x 4 = 4) + bnat (fullDegree h x 5 = 4)

abbrev HConstraints (h : BitVec 15) : Prop :=
  ∀ i j, commonParity h i j = edge h i j

abbrev ExtensionConstraints (h : BitVec 15) (x : BitVec 6) : Prop :=
  (∀ i, neighborsInXParity h x i = false) ∧
  (xcard x = 0 ∨ xcard x = 2 ∨ xcard x = 4) ∧
  (∀ i, fullDegree h x i = 2 ∨ fullDegree h x i = 4 ∨
    fullDegree h x i = 6) ∧
  degreeFourCount h x = 5

def highBits (h : BitVec 15) : BitVec 10 :=
  h.extractLsb' 5 10

def lowBits (h : BitVec 15) : BitVec 5 :=
  h.extractLsb' 0 5

def joinBits (high : BitVec 10) (low : BitVec 5) : BitVec 15 :=
  high.append low

theorem join_highBits_lowBits (h : BitVec 15) :
    joinBits (highBits h) (lowBits h) = h := by
  rw [joinBits, highBits, lowBits, BitVec.append_eq]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb']
  · exact BitVec.extractLsb'_eq_self
  · simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_0 :
    ∀ high, HConstraints (joinBits high 0) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 0) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_1 :
    ∀ high, HConstraints (joinBits high 1) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 1) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_2 :
    ∀ high, HConstraints (joinBits high 2) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 2) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_3 :
    ∀ high, HConstraints (joinBits high 3) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 3) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_4 :
    ∀ high, HConstraints (joinBits high 4) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 4) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_5 :
    ∀ high, HConstraints (joinBits high 5) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 5) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_6 :
    ∀ high, HConstraints (joinBits high 6) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 6) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_7 :
    ∀ high, HConstraints (joinBits high 7) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 7) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_8 :
    ∀ high, HConstraints (joinBits high 8) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 8) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_9 :
    ∀ high, HConstraints (joinBits high 9) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 9) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_10 :
    ∀ high, HConstraints (joinBits high 10) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 10) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_11 :
    ∀ high, HConstraints (joinBits high 11) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 11) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_12 :
    ∀ high, HConstraints (joinBits high 12) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 12) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_13 :
    ∀ high, HConstraints (joinBits high 13) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 13) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_14 :
    ∀ high, HConstraints (joinBits high 14) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 14) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_15 :
    ∀ high, HConstraints (joinBits high 15) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 15) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_16 :
    ∀ high, HConstraints (joinBits high 16) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 16) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_17 :
    ∀ high, HConstraints (joinBits high 17) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 17) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_18 :
    ∀ high, HConstraints (joinBits high 18) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 18) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_19 :
    ∀ high, HConstraints (joinBits high 19) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 19) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_20 :
    ∀ high, HConstraints (joinBits high 20) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 20) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_21 :
    ∀ high, HConstraints (joinBits high 21) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 21) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_22 :
    ∀ high, HConstraints (joinBits high 22) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 22) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_23 :
    ∀ high, HConstraints (joinBits high 23) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 23) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_24 :
    ∀ high, HConstraints (joinBits high 24) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 24) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_25 :
    ∀ high, HConstraints (joinBits high 25) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 25) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_26 :
    ∀ high, HConstraints (joinBits high 26) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 26) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_27 :
    ∀ high, HConstraints (joinBits high 27) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 27) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_28 :
    ∀ high, HConstraints (joinBits high 28) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 28) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_29 :
    ∀ high, HConstraints (joinBits high 29) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 29) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_30 :
    ∀ high, HConstraints (joinBits high 30) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 30) x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_local_low_31 :
    ∀ high, HConstraints (joinBits high 31) →
      ∀ x, ¬ ExtensionConstraints (joinBits high 31) x := by
  decide +kernel

end ConwayLocalKernel

namespace ConwayLocalKernel

theorem no_local (h : BitVec 15) (hh : HConstraints h)
    (x : BitVec 6) (hx : ExtensionConstraints h x) : False := by
  rw [← join_highBits_lowBits h] at hh hx
  generalize hlow : lowBits h = low at hh hx
  fin_cases low <;> norm_num at hh hx
  case «0» =>
    have heq :
        (FinEnum.equiv (α := BitVec 5)).symm 0 = (0 : BitVec 5) := by
      decide +kernel
    rw [heq] at hh hx
    exact no_local_low_0 (highBits h) hh x hx
  case «1» =>
    have heq :
        (FinEnum.equiv (α := BitVec 5)).symm 1 = (1 : BitVec 5) := by
      decide +kernel
    rw [heq] at hh hx
    exact no_local_low_1 (highBits h) hh x hx
  case «2» =>
    apply no_local_low_2 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «3» =>
    apply no_local_low_3 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «4» =>
    apply no_local_low_4 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «5» =>
    apply no_local_low_5 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «6» =>
    apply no_local_low_6 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «7» =>
    apply no_local_low_7 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «8» =>
    apply no_local_low_8 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «9» =>
    apply no_local_low_9 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «10» =>
    apply no_local_low_10 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «11» =>
    apply no_local_low_11 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «12» =>
    apply no_local_low_12 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «13» =>
    apply no_local_low_13 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «14» =>
    apply no_local_low_14 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «15» =>
    apply no_local_low_15 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «16» =>
    apply no_local_low_16 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «17» =>
    apply no_local_low_17 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «18» =>
    apply no_local_low_18 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «19» =>
    apply no_local_low_19 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «20» =>
    apply no_local_low_20 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «21» =>
    apply no_local_low_21 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «22» =>
    apply no_local_low_22 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «23» =>
    apply no_local_low_23 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «24» =>
    apply no_local_low_24 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «25» =>
    apply no_local_low_25 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «26» =>
    apply no_local_low_26 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «27» =>
    apply no_local_low_27 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «28» =>
    apply no_local_low_28 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «29» =>
    apply no_local_low_29 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «30» =>
    apply no_local_low_30 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1
  case «31» =>
    apply no_local_low_31 (highBits h) ?_ x ?_
    · convert hh using 1 <;> congr 1
    · convert hx using 1 <;> congr 1

end ConwayLocalKernel

namespace ConwayAbstract

abbrev V := Fin 9
abbrev W := Fin 6
abbrev Adj := Matrix V V Bool
abbrev LocalAdj := Matrix W W Bool

def natDegree (A : Adj) (i : V) : Nat :=
  ∑ j, (A i j).toNat

def degreeFourCount (A : Adj) : Nat :=
  ∑ i, if natDegree A i = 4 then 1 else 0

def allOnes : Adj :=
  fun _ _ => true

def complement (A : Adj) : Adj :=
  A + allOnes + 1

def Conditions (A : Adj) : Prop :=
  A.IsSymm ∧
  (∀ i, A i i = false) ∧
  A * A = A ∧
  (∀ i, natDegree A i = 2 ∨ natDegree A i = 4 ∨ natDegree A i = 6) ∧
  degreeFourCount A = 5

def neighbors (A : Adj) (v : V) : Finset V :=
  Finset.univ.filter fun j => A v j = true

def rest (v a b : V) : Finset V :=
  ((Finset.univ.erase v).erase a).erase b

def encodeH (H : LocalAdj) : BitVec 15 :=
  BitVec.ofBoolListLE [
    H 0 1, H 0 2, H 0 3, H 0 4, H 0 5,
    H 1 2, H 1 3, H 1 4, H 1 5,
    H 2 3, H 2 4, H 2 5,
    H 3 4, H 3 5,
    H 4 5
  ]

def encodeX (f : W → Bool) : BitVec 6 :=
  BitVec.ofBoolListLE [f 0, f 1, f 2, f 3, f 4, f 5]

private theorem bnat_eq_toNat (b : Bool) :
    ConwayLocalKernel.bnat b = b.toNat := by
  cases b <;> rfl

private theorem xor_eq_add (a b : Bool) :
    (a ^^ b) = a + b := by
  cases a <;> cases b <;> rfl

private theorem and_eq_mul (a b : Bool) :
    (a && b) = a * b := by
  cases a <;> cases b <;> rfl

private theorem bool_add_true (b : Bool) :
    b + true = !b := by
  cases b <;> rfl

private theorem bool_mul_true (b : Bool) :
    b * true = b := by
  cases b <;> rfl

private theorem bool_one_eq_true :
    (1 : Bool) = true := by
  rfl

private theorem bool_zero_eq_false :
    (0 : Bool) = false := by
  rfl

private theorem symm_apply {H : LocalAdj} (hsymm : H.IsSymm) (i j : W) :
    H i j = H j i := by
  exact congrArg (fun M : LocalAdj => M j i) hsymm

theorem adj_symm_apply {A : Adj} (hsymm : A.IsSymm) (i j : V) :
    A i j = A j i := by
  exact congrArg (fun M : Adj => M j i) hsymm

private theorem bool_sum_false_of_count
    (a b c d e f g h i : Bool)
    (hc : a.toNat + b.toNat + c.toNat + d.toNat + e.toNat +
      f.toNat + g.toNat + h.toNat + i.toNat = 2 ∨
      a.toNat + b.toNat + c.toNat + d.toNat + e.toNat +
      f.toNat + g.toNat + h.toNat + i.toNat = 4 ∨
      a.toNat + b.toNat + c.toNat + d.toNat + e.toNat +
      f.toNat + g.toNat + h.toNat + i.toNat = 6) :
    a + b + c + d + e + f + g + h + i = false := by
  revert hc
  decide +kernel +revert

private theorem not_count_eight
    (a b c d e f g h : Bool) :
    (!a).toNat + (!b).toNat + (!c).toNat + (!d).toNat +
      (!e).toNat + (!f).toNat + (!g).toNat + (!h).toNat =
      8 - (a.toNat + b.toNat + c.toNat + d.toNat +
        e.toNat + f.toNat + g.toNat + h.toNat) := by
  decide +kernel +revert

theorem neighbors_card (A : Adj) (v : V) :
    (neighbors A v).card = natDegree A v := by
  rw [natDegree]
  change (Finset.univ.filter fun j => A v j = true).card =
    Finset.univ.sum fun j => (A v j).toNat
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  cases A v j <;> rfl

theorem mul_sum_eq_neighbors_sum
    (A : Adj) (v : V) (f : V → Bool) :
    (∑ k, A v k * f k) = (neighbors A v).sum f := by
  change Finset.univ.sum (fun k => A v k * f k) =
    (Finset.univ.filter fun k => A v k = true).sum f
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  cases A v k <;> cases f k <;> rfl

theorem rest_card
    (v a b : V) (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b) :
    (rest v a b).card = 6 := by
  simp [rest, Ne.symm hva, Ne.symm hvb, Ne.symm hab]

theorem sum_eq_three_add_rest
    {M : Type} [AddCommMonoid M]
    (v a b : V) (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (e : W ≃ ↥(rest v a b)) (f : V → M) :
    (∑ k, f k) = f v + f a + f b + ∑ w, f (e w).1 := by
  rw [← Finset.sum_erase_add (Finset.univ : Finset V) f
    (Finset.mem_univ v)]
  have ha : a ∈ (Finset.univ : Finset V).erase v := by
    simp [Ne.symm hva]
  rw [← Finset.sum_erase_add ((Finset.univ : Finset V).erase v) f ha]
  have hb : b ∈ ((Finset.univ : Finset V).erase v).erase a := by
    simp [Ne.symm hvb, Ne.symm hab]
  rw [← Finset.sum_erase_add
    (((Finset.univ : Finset V).erase v).erase a) f hb]
  change (rest v a b).sum f + f b + f a + f v = _
  have hsub : (∑ z : ↥(rest v a b), f z.1) =
      (rest v a b).sum f :=
    Finset.sum_coe_sort (rest v a b) f
  rw [← hsub]
  rw [← e.sum_comp (fun z : ↥(rest v a b) => f z.1)]
  ac_rfl

private theorem allOnes_sq :
    allOnes * allOnes = allOnes := by
  ext i j
  simp only [allOnes, Matrix.mul_apply]
  change (∑ _ : Fin 9, true) = true
  decide

private theorem row_sum_eq_false
    (A : Adj)
    (hdeg : ∀ i, natDegree A i = 2 ∨
      natDegree A i = 4 ∨ natDegree A i = 6) (i : V) :
    (∑ k, A i k) = false := by
  have hc :
      (A i 0).toNat + (A i 1).toNat + (A i 2).toNat +
        (A i 3).toNat + (A i 4).toNat + (A i 5).toNat +
        (A i 6).toNat + (A i 7).toNat + (A i 8).toNat = 2 ∨
      (A i 0).toNat + (A i 1).toNat + (A i 2).toNat +
        (A i 3).toNat + (A i 4).toNat + (A i 5).toNat +
        (A i 6).toNat + (A i 7).toNat + (A i 8).toNat = 4 ∨
      (A i 0).toNat + (A i 1).toNat + (A i 2).toNat +
        (A i 3).toNat + (A i 4).toNat + (A i 5).toNat +
        (A i 6).toNat + (A i 7).toNat + (A i 8).toNat = 6 := by
    simpa [natDegree, Fin.sum_univ_succ, add_assoc] using hdeg i
  simpa [Fin.sum_univ_succ, add_assoc] using
    bool_sum_false_of_count
      (A i 0) (A i 1) (A i 2) (A i 3) (A i 4)
      (A i 5) (A i 6) (A i 7) (A i 8) hc

private theorem mul_allOnes_eq_zero
    (A : Adj)
    (hdeg : ∀ i, natDegree A i = 2 ∨
      natDegree A i = 4 ∨ natDegree A i = 6) :
    A * allOnes = 0 := by
  ext i j
  simpa [Matrix.mul_apply, allOnes, bool_mul_true, bool_zero_eq_false] using
    row_sum_eq_false A hdeg i

private theorem allOnes_mul_eq_zero
    (A : Adj) (hsymm : A.IsSymm)
    (hdeg : ∀ i, natDegree A i = 2 ∨
      natDegree A i = 4 ∨ natDegree A i = 6) :
    allOnes * A = 0 := by
  ext i j
  change (∑ k, A k j) = false
  have hsum : (∑ k, A k j) = ∑ k, A j k := by
    apply Finset.sum_congr rfl
    intro k _
    exact adj_symm_apply hsymm k j
  simpa [Matrix.mul_apply, allOnes] using
    hsum.trans (row_sum_eq_false A hdeg j)

theorem complement_symm
    (A : Adj) (hsymm : A.IsSymm) :
    (complement A).IsSymm := by
  ext i j
  simp only [complement, Matrix.transpose_apply, Matrix.add_apply]
  rw [adj_symm_apply hsymm j i]
  simp [allOnes, Matrix.one_apply, eq_comm]

theorem complement_loopless
    (A : Adj) (hloop : ∀ i, A i i = false) :
    ∀ i, complement A i i = false := by
  intro i
  simp [complement, allOnes, Matrix.one_apply, hloop,
    bool_one_eq_true, bool_add_true]

theorem natDegree_complement
    (A : Adj) (hloop : ∀ i, A i i = false) (i : V) :
    natDegree (complement A) i = 8 - natDegree A i := by
  fin_cases i
  · simpa [natDegree, Fin.sum_univ_succ, complement, allOnes,
      Matrix.one_apply, hloop, bool_one_eq_true, bool_add_true,
      add_assoc] using
      not_count_eight
        (A 0 1) (A 0 2) (A 0 3) (A 0 4)
        (A 0 5) (A 0 6) (A 0 7) (A 0 8)
  · simpa [natDegree, Fin.sum_univ_succ, complement, allOnes,
      Matrix.one_apply, hloop, bool_one_eq_true, bool_add_true,
      add_assoc] using
      not_count_eight
        (A 1 0) (A 1 2) (A 1 3) (A 1 4)
        (A 1 5) (A 1 6) (A 1 7) (A 1 8)
  · simpa [natDegree, Fin.sum_univ_succ, complement, allOnes,
      Matrix.one_apply, hloop, bool_one_eq_true, bool_add_true,
      add_assoc] using
      not_count_eight
        (A 2 0) (A 2 1) (A 2 3) (A 2 4)
        (A 2 5) (A 2 6) (A 2 7) (A 2 8)
  · simpa [natDegree, Fin.sum_univ_succ, complement, allOnes,
      Matrix.one_apply, hloop, bool_one_eq_true, bool_add_true,
      add_assoc] using
      not_count_eight
        (A 3 0) (A 3 1) (A 3 2) (A 3 4)
        (A 3 5) (A 3 6) (A 3 7) (A 3 8)
  · simpa [natDegree, Fin.sum_univ_succ, complement, allOnes,
      Matrix.one_apply, hloop, bool_one_eq_true, bool_add_true,
      add_assoc] using
      not_count_eight
        (A 4 0) (A 4 1) (A 4 2) (A 4 3)
        (A 4 5) (A 4 6) (A 4 7) (A 4 8)
  · simpa [natDegree, Fin.sum_univ_succ, complement, allOnes,
      Matrix.one_apply, hloop, bool_one_eq_true, bool_add_true,
      add_assoc] using
      not_count_eight
        (A 5 0) (A 5 1) (A 5 2) (A 5 3)
        (A 5 4) (A 5 6) (A 5 7) (A 5 8)
  · simpa [natDegree, Fin.sum_univ_succ, complement, allOnes,
      Matrix.one_apply, hloop, bool_one_eq_true, bool_add_true,
      add_assoc] using
      not_count_eight
        (A 6 0) (A 6 1) (A 6 2) (A 6 3)
        (A 6 4) (A 6 5) (A 6 7) (A 6 8)
  · simpa [natDegree, Fin.sum_univ_succ, complement, allOnes,
      Matrix.one_apply, hloop, bool_one_eq_true, bool_add_true,
      add_assoc] using
      not_count_eight
        (A 7 0) (A 7 1) (A 7 2) (A 7 3)
        (A 7 4) (A 7 5) (A 7 6) (A 7 8)
  · simpa [natDegree, Fin.sum_univ_succ, complement, allOnes,
      Matrix.one_apply, hloop, bool_one_eq_true, bool_add_true,
      add_assoc] using
      not_count_eight
        (A 8 0) (A 8 1) (A 8 2) (A 8 3)
        (A 8 4) (A 8 5) (A 8 6) (A 8 7)

theorem complement_degree
    (A : Adj) (hloop : ∀ i, A i i = false)
    (hdeg : ∀ i, natDegree A i = 2 ∨
      natDegree A i = 4 ∨ natDegree A i = 6) :
    ∀ i, natDegree (complement A) i = 2 ∨
      natDegree (complement A) i = 4 ∨
      natDegree (complement A) i = 6 := by
  intro i
  rw [natDegree_complement A hloop i]
  rcases hdeg i with htwo | hfour | hsix <;> omega

theorem complement_degree_four_iff
    (A : Adj) (hloop : ∀ i, A i i = false)
    (hdeg : ∀ i, natDegree A i = 2 ∨
      natDegree A i = 4 ∨ natDegree A i = 6) (i : V) :
    natDegree (complement A) i = 4 ↔ natDegree A i = 4 := by
  rw [natDegree_complement A hloop i]
  rcases hdeg i with htwo | hfour | hsix <;> omega

theorem complement_degree_four_count
    (A : Adj) (hloop : ∀ i, A i i = false)
    (hdeg : ∀ i, natDegree A i = 2 ∨
      natDegree A i = 4 ∨ natDegree A i = 6) :
    degreeFourCount (complement A) = degreeFourCount A := by
  unfold degreeFourCount
  apply Finset.sum_congr rfl
  intro i _
  simp [complement_degree_four_iff A hloop hdeg i]

theorem complement_idempotent
    (A : Adj) (hsymm : A.IsSymm)
    (hidem : A * A = A)
    (hdeg : ∀ i, natDegree A i = 2 ∨
      natDegree A i = 4 ∨ natDegree A i = 6) :
    complement A * complement A = complement A := by
  simp only [complement]
  calc
    (A + allOnes + 1) * (A + allOnes + 1) =
        A * A + A * allOnes + A +
          (allOnes * A + allOnes * allOnes + allOnes) +
          (A + allOnes + 1) := by
      noncomm_ring
    _ = A + 0 + A + (0 + allOnes + allOnes) +
          (A + allOnes + 1) := by
      rw [hidem, mul_allOnes_eq_zero A hdeg,
        allOnes_mul_eq_zero A hsymm hdeg, allOnes_sq]
    _ = A + allOnes + 1 := by
      ext i j
      simp [Matrix.add_apply, allOnes, Matrix.one_apply]
      cases A i j <;> rfl

theorem complement_conditions
    (A : Adj) (hA : Conditions A) :
    Conditions (complement A) := by
  rcases hA with ⟨hsymm, hloop, hidem, hdeg, hcount⟩
  exact ⟨complement_symm A hsymm, complement_loopless A hloop,
    complement_idempotent A hsymm hidem hdeg,
    complement_degree A hloop hdeg,
    (complement_degree_four_count A hloop hdeg).trans hcount⟩

theorem edge_encodeH
    (H : LocalAdj) (hsymm : H.IsSymm) (hloop : ∀ i, H i i = false)
    (i j : W) :
    ConwayLocalKernel.edge (encodeH H) i j = H i j := by
  fin_cases i <;> fin_cases j <;>
    simp only [ConwayLocalKernel.edge, ConwayLocalKernel.pairIndex, encodeH,
      BitVec.getLsbD_ofBoolListLE] <;>
    norm_num [Nat.min_def, Nat.max_def, hloop] <;>
    first
    | simpa using symm_apply hsymm _ _
    | rfl

theorem xmem_encodeX (f : W → Bool) (i : W) :
    ConwayLocalKernel.xmem (encodeX f) i = f i := by
  fin_cases i <;>
    simp only [ConwayLocalKernel.xmem, encodeX, BitVec.getLsbD_ofBoolListLE] <;>
    norm_num <;>
    congr 1

theorem commonParity_encodeH
    (H : LocalAdj) (hsymm : H.IsSymm) (hloop : ∀ i, H i i = false)
    (i j : W) :
    ConwayLocalKernel.commonParity (encodeH H) i j = (H * H) i j := by
  simp [ConwayLocalKernel.commonParity, edge_encodeH H hsymm hloop,
    Matrix.mul_apply, Fin.sum_univ_succ, xor_eq_add, and_eq_mul, add_assoc]

theorem degree_encodeH
    (H : LocalAdj) (hsymm : H.IsSymm) (hloop : ∀ i, H i i = false)
    (i : W) :
    ConwayLocalKernel.degree (encodeH H) i =
      ∑ j, (H i j).toNat := by
  simp [ConwayLocalKernel.degree, edge_encodeH H hsymm hloop,
    bnat_eq_toNat, Fin.sum_univ_succ, add_assoc]

theorem xcard_encodeX (f : W → Bool) :
    ConwayLocalKernel.xcard (encodeX f) = ∑ i, (f i).toNat := by
  simp [ConwayLocalKernel.xcard, xmem_encodeX, bnat_eq_toNat,
    Fin.sum_univ_succ, add_assoc]

theorem neighborsInXParity_encode
    (H : LocalAdj) (f : W → Bool)
    (hsymm : H.IsSymm) (hloop : ∀ i, H i i = false) (i : W) :
    ConwayLocalKernel.neighborsInXParity (encodeH H) (encodeX f) i =
      ∑ j, H i j * f j := by
  simp [ConwayLocalKernel.neighborsInXParity,
    edge_encodeH H hsymm hloop, xmem_encodeX, Fin.sum_univ_succ,
    xor_eq_add, and_eq_mul, add_assoc]

end ConwayAbstract

namespace ConwayAbstract

set_option maxHeartbeats 5000000

private theorem bool_eq_of_add_eq_false (a b : Bool)
    (h : a + b = false) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem bool_add_cancel_self (a b : Bool)
    (h : a + b = a) : b = false := by
  cases a <;> cases b <;> simp_all

private theorem bool_false_mul (b : Bool) :
    false * b = false := by
  cases b <;> rfl

private theorem bool_false_add (b : Bool) :
    false + b = b := by
  cases b <;> rfl

private theorem degreeTwo_bool_mul_true (b : Bool) :
    b * true = b := by
  cases b <;> rfl

private theorem bool_mul_false (b : Bool) :
    b * false = false := by
  cases b <;> rfl

private theorem degreeTwo_bnat_eq_toNat (b : Bool) :
    ConwayLocalKernel.bnat b = b.toNat := by
  cases b <;> rfl

theorem no_conditions_of_degree_two
    (A : Adj) (hA : Conditions A) (v : V)
    (hvDegree : natDegree A v = 2) : False := by
  rcases hA with ⟨hsymm, hloop, hidem, hdeg, hcount⟩
  have hncard : (neighbors A v).card = 2 := by
    rw [neighbors_card, hvDegree]
  obtain ⟨a, b, hab, hn⟩ := Finset.card_eq_two.mp hncard
  have hvaEdge : A v a = true := by
    have : a ∈ neighbors A v := by simp [hn]
    simpa [neighbors] using this
  have hvbEdge : A v b = true := by
    have : b ∈ neighbors A v := by simp [hn]
    simpa [neighbors] using this
  have hva : v ≠ a := by
    intro hva
    subst a
    simpa [hloop v] using hvaEdge
  have hvb : v ≠ b := by
    intro hvb
    subst b
    simpa [hloop v] using hvbEdge
  have hvOutside (x : V) (hxa : x ≠ a) (hxb : x ≠ b) :
      A v x = false := by
    by_contra hx
    have hxtrue : A v x = true := by
      cases h : A v x
      · exact (hx h).elim
      · rfl
    have hxmem : x ∈ neighbors A v := by
      simpa [neighbors, hxtrue]
    rw [hn] at hxmem
    simp [hxa, hxb] at hxmem
  have habEdge : A a b = true := by
    have hentry := congrArg (fun M : Adj => M v a) hidem
    have hsum :
        (∑ k, A v k * A k a) = A a a + A b a := by
      rw [mul_sum_eq_neighbors_sum A v (fun k => A k a), hn]
      simp [hab]
    rw [Matrix.mul_apply, hsum, hloop a,
      adj_symm_apply hsymm b a, hvaEdge] at hentry
    cases h : A a b
    · have hne : false + false ≠ true := by decide
      exact (hne (by simpa [h] using hentry)).elim
    · rfl
  have hsameOutside (x : V) (hxa : x ≠ a) (hxb : x ≠ b) :
      A a x = A b x := by
    have hentry := congrArg (fun M : Adj => M v x) hidem
    have hsum :
        (∑ k, A v k * A k x) = A a x + A b x := by
      rw [mul_sum_eq_neighbors_sum A v (fun k => A k x), hn]
      simp [hab]
    rw [Matrix.mul_apply, hsum, hvOutside x hxa hxb] at hentry
    exact bool_eq_of_add_eq_false _ _ hentry
  let e : W ≃ ↥(rest v a b) :=
    (Finset.equivFinOfCardEq (rest_card v a b hva hvb hab)).symm
  let r : W → V := fun i => (e i).1
  have hrMem (i : W) : r i ∈ rest v a b := (e i).2
  have hrv (i : W) : r i ≠ v := by
    have := hrMem i
    simp [rest] at this
    exact this.2.2
  have hra (i : W) : r i ≠ a := by
    have := hrMem i
    simp [rest] at this
    exact this.2.1
  have hrb (i : W) : r i ≠ b := by
    have := hrMem i
    simp [rest] at this
    exact this.1
  let H : LocalAdj := fun i j => A (r i) (r j)
  let f : W → Bool := fun i => A a (r i)
  have hHsymm : H.IsSymm := by
    ext i j
    exact adj_symm_apply hsymm (r j) (r i)
  have hHloop : ∀ i, H i i = false := by
    intro i
    exact hloop (r i)
  have hrvEdge (i : W) : A (r i) v = false := by
    rw [adj_symm_apply hsymm (r i) v]
    exact hvOutside (r i) (hra i) (hrb i)
  have hraEq (i : W) : A (r i) a = f i := by
    exact adj_symm_apply hsymm (r i) a
  have hrbEq (i : W) : A (r i) b = f i := by
    rw [adj_symm_apply hsymm (r i) b]
    exact hsameOutside (r i) (hra i) (hrb i) |>.symm
  have hbrEq (i : W) : A b (r i) = f i := by
    rw [adj_symm_apply hsymm b (r i)]
    exact hrbEq i
  have hHidem : H * H = H := by
    ext i j
    have hentry := congrArg (fun M : Adj => M (r i) (r j)) hidem
    rw [Matrix.mul_apply] at hentry
    have hdecomp := sum_eq_three_add_rest v a b hva hvb hab e
      (fun k => A (r i) k * A k (r j))
    rw [hdecomp] at hentry
    change
      A (r i) v * A v (r j) +
        A (r i) a * A a (r j) +
        A (r i) b * A b (r j) +
        (∑ w, A (r i) (r w) * A (r w) (r j)) =
      A (r i) (r j) at hentry
    rw [hrvEdge i, hraEq i, hrbEq i,
      ← hsameOutside (r j) (hra j) (hrb j)] at hentry
    simp only [bool_false_mul, bool_false_add] at hentry
    change f i * f j + f i * f j + (H * H) i j = H i j at hentry
    have hcancel : f i * f j + f i * f j = false := by
      cases f i <;> cases f j <;> rfl
    rw [hcancel] at hentry
    simpa [bool_false_add] using hentry
  have hXorth : ∀ i, (∑ j, H i j * f j) = false := by
    intro i
    have hentry := congrArg (fun M : Adj => M (r i) a) hidem
    rw [Matrix.mul_apply] at hentry
    have hdecomp := sum_eq_three_add_rest v a b hva hvb hab e
      (fun k => A (r i) k * A k a)
    rw [hdecomp] at hentry
    change
      A (r i) v * A v a +
        A (r i) a * A a a +
        A (r i) b * A b a +
        (∑ w, A (r i) (r w) * A (r w) a) =
      A (r i) a at hentry
    rw [hrvEdge i, hraEq i, hrbEq i, hloop a,
      adj_symm_apply hsymm b a, habEdge] at hentry
    simp only [bool_false_mul, bool_false_add, degreeTwo_bool_mul_true,
      bool_mul_false] at hentry
    simp_rw [hraEq] at hentry
    change f i + (∑ j, H i j * f j) = f i at hentry
    exact bool_add_cancel_self _ _ hentry
  let t : Nat := ∑ i, (f i).toNat
  have hdegA : natDegree A a = 2 + t := by
    rw [natDegree, sum_eq_three_add_rest v a b hva hvb hab e]
    rw [adj_symm_apply hsymm a v, hvaEdge, hloop a, habEdge]
    change 1 + 0 + 1 + (∑ i, (f i).toNat) = 2 + t
    omega
  have hdegB : natDegree A b = 2 + t := by
    rw [natDegree, sum_eq_three_add_rest v a b hva hvb hab e]
    rw [adj_symm_apply hsymm b v, hvbEdge,
      adj_symm_apply hsymm b a, habEdge, hloop b]
    change 1 + 1 + 0 + (∑ i, (A b (r i)).toNat) = 2 + t
    simp_rw [hbrEq]
    omega
  have ht : t = 0 ∨ t = 2 ∨ t = 4 := by
    have haCases := hdeg a
    rw [hdegA] at haCases
    rcases haCases with htwo | hfour | hsix <;> omega
  let localDeg : W → Nat :=
    fun i => (∑ j, (H i j).toNat) + 2 * (f i).toNat
  have hdegR (i : W) : natDegree A (r i) = localDeg i := by
    rw [natDegree, sum_eq_three_add_rest v a b hva hvb hab e]
    rw [hrvEdge i, hraEq i, hrbEq i]
    change 0 + (f i).toNat + (f i).toNat +
        (∑ j, (H i j).toNat) = localDeg i
    cases hfi : f i <;> simp [localDeg, hfi] <;> omega
  have hlocalDeg (i : W) :
      localDeg i = 2 ∨ localDeg i = 4 ∨ localDeg i = 6 := by
    rw [← hdegR i]
    exact hdeg (r i)
  have hlocalCount :
      2 * (if t = 2 then 1 else 0) +
        (∑ i, if localDeg i = 4 then 1 else 0) = 5 := by
    have hc := hcount
    rw [degreeFourCount,
      sum_eq_three_add_rest v a b hva hvb hab e] at hc
    change
      (if natDegree A v = 4 then 1 else 0) +
        (if natDegree A a = 4 then 1 else 0) +
        (if natDegree A b = 4 then 1 else 0) +
        (∑ i, if natDegree A (r i) = 4 then 1 else 0) = 5 at hc
    rw [hvDegree, hdegA, hdegB] at hc
    simp_rw [hdegR] at hc
    rcases ht with ht | ht | ht
    · rw [ht] at hc ⊢
      norm_num at hc ⊢
      exact hc
    · rw [ht] at hc ⊢
      norm_num at hc ⊢
      exact hc
    · rw [ht] at hc ⊢
      norm_num at hc ⊢
      exact hc
  let hb : BitVec 15 := encodeH H
  let xb : BitVec 6 := encodeX f
  have hh : ConwayLocalKernel.HConstraints hb := by
    intro i j
    dsimp only [hb]
    rw [commonParity_encodeH H hHsymm hHloop,
      edge_encodeH H hHsymm hHloop, hHidem]
  have hxOrth :
      ∀ i, ConwayLocalKernel.neighborsInXParity hb xb i = false := by
    intro i
    dsimp only [hb, xb]
    rw [neighborsInXParity_encode H f hHsymm hHloop]
    exact hXorth i
  have hxCard : ConwayLocalKernel.xcard xb = t := by
    dsimp only [xb, t]
    exact xcard_encodeX f
  have hxCardCases :
      ConwayLocalKernel.xcard xb = 0 ∨
        ConwayLocalKernel.xcard xb = 2 ∨
        ConwayLocalKernel.xcard xb = 4 := by
    rw [hxCard]
    exact ht
  have hfullDegree (i : W) :
      ConwayLocalKernel.fullDegree hb xb i = localDeg i := by
    dsimp only [hb, xb]
    rw [ConwayLocalKernel.fullDegree,
      degree_encodeH H hHsymm hHloop, xmem_encodeX f i,
      degreeTwo_bnat_eq_toNat]
  have hxDegrees :
      ∀ i, ConwayLocalKernel.fullDegree hb xb i = 2 ∨
        ConwayLocalKernel.fullDegree hb xb i = 4 ∨
        ConwayLocalKernel.fullDegree hb xb i = 6 := by
    intro i
    rw [hfullDegree i]
    exact hlocalDeg i
  have hxCount :
      ConwayLocalKernel.degreeFourCount hb xb = 5 := by
    rw [ConwayLocalKernel.degreeFourCount, hxCard,
      hfullDegree 0, hfullDegree 1, hfullDegree 2,
      hfullDegree 3, hfullDegree 4, hfullDegree 5]
    have hc := hlocalCount
    simp only [Fin.sum_univ_succ] at hc
    simpa [ConwayLocalKernel.bnat, add_assoc] using hc
  exact ConwayLocalKernel.no_local hb hh xb
    ⟨hxOrth, hxCardCases, hxDegrees, hxCount⟩

theorem no_conditions (A : Adj) (hA : Conditions A) : False := by
  have hdata := hA
  rcases hdata with ⟨_, hloop, _, hdeg, hcount⟩
  by_cases htwo : ∃ v, natDegree A v = 2
  · obtain ⟨v, hv⟩ := htwo
    exact no_conditions_of_degree_two A hA v hv
  · have hsix : ∃ v, natDegree A v = 6 := by
      by_contra hsix
      push_neg at hsix
      have hfour : ∀ v, natDegree A v = 4 := by
        intro v
        rcases hdeg v with hv | hv | hv
        · exact (htwo ⟨v, hv⟩).elim
        · exact hv
        · exact (hsix v hv).elim
      have hnine : degreeFourCount A = 9 := by
        simp [degreeFourCount, hfour]
      omega
    obtain ⟨v, hv⟩ := hsix
    have hvComplement : natDegree (complement A) v = 2 := by
      rw [natDegree_complement A hloop v, hv]
    exact no_conditions_of_degree_two (complement A)
      (complement_conditions A hA) v hvComplement

end ConwayAbstract

namespace ConwayArithmetic

set_option maxHeartbeats 50000

private theorem sq_mod_four_eq_mod_two (n : ℕ) :
    n * n % 4 = n % 2 := by
  rw [Nat.mul_mod]
  have hlt : n % 4 < 4 := Nat.mod_lt _ (by decide)
  have hmod : n % 4 % 2 = n % 2 := Nat.mod_mod_of_dvd n (by norm_num)
  interval_cases h : n % 4 <;> norm_num [h] at hmod ⊢ <;> omega

private theorem sq_modEq_mod_two_four (n : ℕ) :
    n * n ≡ n % 2 [MOD 4] := by
  change n * n % 4 = n % 2 % 4
  rw [sq_mod_four_eq_mod_two]
  omega

private theorem even_sq_modEq_twice_eight (n : ℕ) (h : n % 2 = 0) :
    n * n ≡ 2 * n [MOD 8] := by
  change n * n % 8 = (2 * n) % 8
  rw [Nat.mul_mod, Nat.mul_mod]
  have hlt : n % 8 < 8 := Nat.mod_lt _ (by decide)
  have hmod : n % 8 % 2 = n % 2 :=
    Nat.mod_mod_of_dvd n (by norm_num)
  rw [h] at hmod
  interval_cases hn : n % 8 <;> norm_num [hn] at hmod
  all_goals norm_num [Nat.mul_mod, hn]

private theorem odd_sq_modEq_one_eight (n : ℕ) (h : n % 2 = 1) :
    n * n ≡ 1 [MOD 8] := by
  change n * n % 8 = 1 % 8
  rw [Nat.mul_mod]
  have hlt : n % 8 < 8 := Nat.mod_lt _ (by decide)
  have hmod : n % 8 % 2 = n % 2 :=
    Nat.mod_mod_of_dvd n (by norm_num)
  rw [h] at hmod
  interval_cases hn : n % 8 <;> norm_num [hn] at hmod
  all_goals norm_num [Nat.mul_mod, hn]

private theorem mod_two_le_one (n : ℕ) : n % 2 ≤ 1 := by
  exact Nat.le_of_lt_succ (Nat.mod_lt n (by decide))

private theorem eight_parities_mod_four_cases
    (a b c d e f g h : ℕ)
    (hmod :
      (a % 2 + b % 2 + c % 2 + d % 2 +
        e % 2 + f % 2 + g % 2 + h % 2) % 4 = 0) :
    a % 2 + b % 2 + c % 2 + d % 2 +
        e % 2 + f % 2 + g % 2 + h % 2 = 0 ∨
    a % 2 + b % 2 + c % 2 + d % 2 +
        e % 2 + f % 2 + g % 2 + h % 2 = 4 ∨
    a % 2 + b % 2 + c % 2 + d % 2 +
        e % 2 + f % 2 + g % 2 + h % 2 = 8 := by
  have ha := mod_two_le_one a
  have hb := mod_two_le_one b
  have hc := mod_two_le_one c
  have hd := mod_two_le_one d
  have he := mod_two_le_one e
  have hf := mod_two_le_one f
  have hg := mod_two_le_one g
  have hh := mod_two_le_one h
  omega

private theorem all_even_of_parity_sum_zero
    (a b c d e f g h : ℕ)
    (hsum :
      a % 2 + b % 2 + c % 2 + d % 2 +
        e % 2 + f % 2 + g % 2 + h % 2 = 0) :
    a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 ∧ d % 2 = 0 ∧
      e % 2 = 0 ∧ f % 2 = 0 ∧ g % 2 = 0 ∧ h % 2 = 0 := by
  omega

private theorem all_odd_of_parity_sum_eight
    (a b c d e f g h : ℕ)
    (hsum :
      a % 2 + b % 2 + c % 2 + d % 2 +
        e % 2 + f % 2 + g % 2 + h % 2 = 8) :
    a % 2 = 1 ∧ b % 2 = 1 ∧ c % 2 = 1 ∧ d % 2 = 1 ∧
      e % 2 = 1 ∧ f % 2 = 1 ∧ g % 2 = 1 ∧ h % 2 = 1 := by
  have ha := mod_two_le_one a
  have hb := mod_two_le_one b
  have hc := mod_two_le_one c
  have hd := mod_two_le_one d
  have he := mod_two_le_one e
  have hf := mod_two_le_one f
  have hg := mod_two_le_one g
  have hh := mod_two_le_one h
  omega

theorem parity_count_zero
    (a b c d e f g h : ℕ)
    (hsq : a * a + b * b + c * c + d * d +
      e * e + f * f + g * g + h * h = 34) :
    a % 2 + b % 2 + c % 2 + d % 2 +
      e % 2 + f % 2 + g % 2 + h % 2 = 2 ∨
    a % 2 + b % 2 + c % 2 + d % 2 +
      e % 2 + f % 2 + g % 2 + h % 2 = 6 := by
  have hcongr :=
    (((((((sq_modEq_mod_two_four a).add (sq_modEq_mod_two_four b)).add
      (sq_modEq_mod_two_four c)).add (sq_modEq_mod_two_four d)).add
      (sq_modEq_mod_two_four e)).add (sq_modEq_mod_two_four f)).add
      (sq_modEq_mod_two_four g)).add (sq_modEq_mod_two_four h)
  rw [hsq] at hcongr
  change 34 % 4 =
    (a % 2 + b % 2 + c % 2 + d % 2 +
      e % 2 + f % 2 + g % 2 + h % 2) % 4 at hcongr
  norm_num at hcongr
  omega

theorem parity_count_two
    (a b c d e f g h : ℕ)
    (hsum : a + b + c + d + e + f + g + h = 12)
    (hsq : a * a + b * b + c * c + d * d +
      e * e + f * f + g * g + h * h = 28) :
    a % 2 + b % 2 + c % 2 + d % 2 +
      e % 2 + f % 2 + g % 2 + h % 2 = 4 := by
  have hcongr :=
    (((((((sq_modEq_mod_two_four a).add (sq_modEq_mod_two_four b)).add
      (sq_modEq_mod_two_four c)).add (sq_modEq_mod_two_four d)).add
      (sq_modEq_mod_two_four e)).add (sq_modEq_mod_two_four f)).add
      (sq_modEq_mod_two_four g)).add (sq_modEq_mod_two_four h)
  rw [hsq] at hcongr
  change 28 % 4 =
    (a % 2 + b % 2 + c % 2 + d % 2 +
      e % 2 + f % 2 + g % 2 + h % 2) % 4 at hcongr
  norm_num at hcongr
  have hcases :=
    eight_parities_mod_four_cases a b c d e f g h hcongr.symm
  rcases hcases with hzero | hfour | height
  · obtain ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ :=
      all_even_of_parity_sum_zero a b c d e f g h hzero
    have hcongrEight :=
      (((((((even_sq_modEq_twice_eight a ha).add
        (even_sq_modEq_twice_eight b hb)).add
        (even_sq_modEq_twice_eight c hc)).add
        (even_sq_modEq_twice_eight d hd)).add
        (even_sq_modEq_twice_eight e he)).add
        (even_sq_modEq_twice_eight f hf)).add
        (even_sq_modEq_twice_eight g hg)).add
        (even_sq_modEq_twice_eight h hh)
    have hright :
        2 * a + 2 * b + 2 * c + 2 * d +
            2 * e + 2 * f + 2 * g + 2 * h =
          2 * (a + b + c + d + e + f + g + h) := by
      ring
    rw [hsq, hright, hsum] at hcongrEight
    norm_num at hcongrEight
  · exact hfour
  · obtain ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ :=
      all_odd_of_parity_sum_eight a b c d e f g h height
    have hcongrEight :=
      (((((((odd_sq_modEq_one_eight a ha).add
        (odd_sq_modEq_one_eight b hb)).add
        (odd_sq_modEq_one_eight c hc)).add
        (odd_sq_modEq_one_eight d hd)).add
        (odd_sq_modEq_one_eight e he)).add
        (odd_sq_modEq_one_eight f hf)).add
        (odd_sq_modEq_one_eight g hg)).add
        (odd_sq_modEq_one_eight h hh)
    rw [hsq] at hcongrEight
    norm_num at hcongrEight

theorem parity_count_nine_zero
    (a b c d e f g h i : ℕ)
    (hzero :
      a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0 ∨ e = 0 ∨
        f = 0 ∨ g = 0 ∨ h = 0 ∨ i = 0)
    (hsq :
      a * a + b * b + c * c + d * d + e * e +
        f * f + g * g + h * h + i * i = 34) :
    a % 2 + b % 2 + c % 2 + d % 2 + e % 2 +
        f % 2 + g % 2 + h % 2 + i % 2 = 2 ∨
    a % 2 + b % 2 + c % 2 + d % 2 + e % 2 +
        f % 2 + g % 2 + h % 2 + i % 2 = 6 := by
  rcases hzero with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num at hsq ⊢
  · exact parity_count_zero b c d e f g h i hsq
  · exact parity_count_zero a c d e f g h i hsq
  · exact parity_count_zero a b d e f g h i hsq
  · exact parity_count_zero a b c e f g h i hsq
  · exact parity_count_zero a b c d f g h i hsq
  · exact parity_count_zero a b c d e g h i hsq
  · exact parity_count_zero a b c d e f h i hsq
  · exact parity_count_zero a b c d e f g i hsq
  · exact parity_count_zero a b c d e f g h hsq

theorem parity_count_nine_two
    (a b c d e f g h i : ℕ)
    (htwo :
      a = 2 ∨ b = 2 ∨ c = 2 ∨ d = 2 ∨ e = 2 ∨
        f = 2 ∨ g = 2 ∨ h = 2 ∨ i = 2)
    (hsum : a + b + c + d + e + f + g + h + i = 14)
    (hsq :
      a * a + b * b + c * c + d * d + e * e +
        f * f + g * g + h * h + i * i = 32) :
    a % 2 + b % 2 + c % 2 + d % 2 + e % 2 +
      f % 2 + g % 2 + h % 2 + i % 2 = 4 := by
  rcases htwo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num at hsum hsq ⊢
  · have hs : b + c + d + e + f + g + h + i = 12 := by omega
    have hq : b * b + c * c + d * d + e * e +
        f * f + g * g + h * h + i * i = 28 := by omega
    exact parity_count_two b c d e f g h i hs hq
  · have hs : a + c + d + e + f + g + h + i = 12 := by omega
    have hq : a * a + c * c + d * d + e * e +
        f * f + g * g + h * h + i * i = 28 := by omega
    exact parity_count_two a c d e f g h i hs hq
  · have hs : a + b + d + e + f + g + h + i = 12 := by omega
    have hq : a * a + b * b + d * d + e * e +
        f * f + g * g + h * h + i * i = 28 := by omega
    exact parity_count_two a b d e f g h i hs hq
  · have hs : a + b + c + e + f + g + h + i = 12 := by omega
    have hq : a * a + b * b + c * c + e * e +
        f * f + g * g + h * h + i * i = 28 := by omega
    exact parity_count_two a b c e f g h i hs hq
  · have hs : a + b + c + d + f + g + h + i = 12 := by omega
    have hq : a * a + b * b + c * c + d * d +
        f * f + g * g + h * h + i * i = 28 := by omega
    exact parity_count_two a b c d f g h i hs hq
  · have hs : a + b + c + d + e + g + h + i = 12 := by omega
    have hq : a * a + b * b + c * c + d * d +
        e * e + g * g + h * h + i * i = 28 := by omega
    exact parity_count_two a b c d e g h i hs hq
  · have hs : a + b + c + d + e + f + h + i = 12 := by omega
    have hq : a * a + b * b + c * c + d * d +
        e * e + f * f + h * h + i * i = 28 := by omega
    exact parity_count_two a b c d e f h i hs hq
  · have hs : a + b + c + d + e + f + g + i = 12 := by omega
    have hq : a * a + b * b + c * c + d * d +
        e * e + f * f + g * g + i * i = 28 := by omega
    exact parity_count_two a b c d e f g i hs hq
  · have hs : a + b + c + d + e + f + g + h = 12 := by omega
    have hq : a * a + b * b + c * c + d * d +
        e * e + f * f + g * g + h * h = 28 := by omega
    exact parity_count_two a b c d e f g h hs hq

end ConwayArithmetic

namespace ConwayParity36

set_option maxHeartbeats 5000000

abbrev V := Fin 9

def pairIndex (i j : V) : Nat :=
  let a := min i.val j.val
  let b := max i.val j.val
  a * (17 - a) / 2 + (b - a - 1)

def edge (x : BitVec 36) (i j : V) : Bool :=
  if i = j then false else x.getLsbD (pairIndex i j)

def bit4 (b : Bool) : BitVec 4 :=
  (BitVec.ofBool b).setWidth 4

def degree (x : BitVec 36) (i : V) : BitVec 4 :=
  bit4 (edge x i 0) + bit4 (edge x i 1) + bit4 (edge x i 2) +
  bit4 (edge x i 3) + bit4 (edge x i 4) + bit4 (edge x i 5) +
  bit4 (edge x i 6) + bit4 (edge x i 7) + bit4 (edge x i 8)

def commonParity (x : BitVec 36) (i j : V) : Bool :=
  (edge x i 0 && edge x 0 j) ^^
  (edge x i 1 && edge x 1 j) ^^
  (edge x i 2 && edge x 2 j) ^^
  (edge x i 3 && edge x 3 j) ^^
  (edge x i 4 && edge x 4 j) ^^
  (edge x i 5 && edge x 5 j) ^^
  (edge x i 6 && edge x 6 j) ^^
  (edge x i 7 && edge x 7 j) ^^
  (edge x i 8 && edge x 8 j)

def degreeFourCount (x : BitVec 36) : BitVec 4 :=
  bit4 (degree x 0 == 4) + bit4 (degree x 1 == 4) +
  bit4 (degree x 2 == 4) + bit4 (degree x 3 == 4) +
  bit4 (degree x 4 == 4) + bit4 (degree x 5 == 4) +
  bit4 (degree x 6 == 4) + bit4 (degree x 7 == 4) +
  bit4 (degree x 8 == 4)

def Constraints (x : BitVec 36) : Prop :=
  (∀ i j, commonParity x i j = edge x i j) ∧
  degreeFourCount x = 5 ∧
  ∀ i, degree x i = 2 ∨ degree x i = 4 ∨ degree x i = 6

end ConwayParity36

namespace ConwaySolution

private def oddBit (n : ℕ) : Bool :=
  decide (n % 2 = 1)

private theorem oddBit_toNat (n : ℕ) :
    (oddBit n).toNat = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
    simp [oddBit, h]

private theorem oddBit_diag_false
    (C : Matrix (Fin 9) (Fin 9) ℕ)
    (hdiagEven : ∀ i, C i i % 2 = 0)
    (i : Fin 9) :
    oddBit (C i i) = false := by
  simp [oddBit, hdiagEven]

private def encode (C : Matrix (Fin 9) (Fin 9) ℕ) : BitVec 36 :=
  BitVec.ofBoolListLE [
    oddBit (C 0 1), oddBit (C 0 2), oddBit (C 0 3), oddBit (C 0 4),
    oddBit (C 0 5), oddBit (C 0 6), oddBit (C 0 7), oddBit (C 0 8),
    oddBit (C 1 2), oddBit (C 1 3), oddBit (C 1 4), oddBit (C 1 5),
    oddBit (C 1 6), oddBit (C 1 7), oddBit (C 1 8),
    oddBit (C 2 3), oddBit (C 2 4), oddBit (C 2 5), oddBit (C 2 6),
    oddBit (C 2 7), oddBit (C 2 8),
    oddBit (C 3 4), oddBit (C 3 5), oddBit (C 3 6), oddBit (C 3 7),
    oddBit (C 3 8),
    oddBit (C 4 5), oddBit (C 4 6), oddBit (C 4 7), oddBit (C 4 8),
    oddBit (C 5 6), oddBit (C 5 7), oddBit (C 5 8),
    oddBit (C 6 7), oddBit (C 6 8),
    oddBit (C 7 8)
  ]

private theorem edge_encode
    (C : Matrix (Fin 9) (Fin 9) ℕ)
    (hsymm : ∀ i j, C i j = C j i)
    (hdiagEven : ∀ i, C i i % 2 = 0)
    (i j : Fin 9) :
    ConwayParity36.edge (encode C) i j = oddBit (C i j) := by
  fin_cases i <;> fin_cases j <;>
    simp only [ConwayParity36.edge, ConwayParity36.pairIndex, encode,
      BitVec.getLsbD_ofBoolListLE] <;>
    norm_num [oddBit_diag_false C hdiagEven, Nat.min_def, Nat.max_def] <;>
    apply congrArg oddBit <;>
    first
    | exact hsymm _ _
    | congr 2

private def rowParity (C : Matrix (Fin 9) (Fin 9) ℕ) (i : Fin 9) : ℕ :=
  C i 0 % 2 + C i 1 % 2 + C i 2 % 2 + C i 3 % 2 + C i 4 % 2 +
    C i 5 % 2 + C i 6 % 2 + C i 7 % 2 + C i 8 % 2

private theorem square_sum_plus_diag_eq_34
    (C : Matrix (Fin 9) (Fin 9) ℕ)
    (hsymm : ∀ i j, C i j = C j i)
    (hsq : ∀ i j,
      (∑ k, C i k * C k j) + C i j =
        (if i = j then 12 else 0) + 22)
    (i : Fin 9) :
    (∑ k, C i k * C i k) + C i i = 34 := by
  have h := hsq i i
  have hsum :
      (∑ k, C i k * C k i) = ∑ k, C i k * C i k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hsymm k i]
  rw [hsum] at h
  simpa using h

private theorem rowParity_of_diag_zero
    (C : Matrix (Fin 9) (Fin 9) ℕ)
    (hsymm : ∀ i j, C i j = C j i)
    (hsq : ∀ i j,
      (∑ k, C i k * C k j) + C i j =
        (if i = j then 12 else 0) + 22)
    (i : Fin 9) (hzero : C i i = 0) :
    rowParity C i = 2 ∨ rowParity C i = 6 := by
  have hs := square_sum_plus_diag_eq_34 C hsymm hsq i
  have hs' :
      C i 0 * C i 0 + C i 1 * C i 1 + C i 2 * C i 2 +
        C i 3 * C i 3 + C i 4 * C i 4 + C i 5 * C i 5 +
        C i 6 * C i 6 + C i 7 * C i 7 + C i 8 * C i 8 = 34 := by
    simpa [Fin.sum_univ_succ, hzero, add_assoc] using hs
  have hz :
      C i 0 = 0 ∨ C i 1 = 0 ∨ C i 2 = 0 ∨ C i 3 = 0 ∨
        C i 4 = 0 ∨ C i 5 = 0 ∨ C i 6 = 0 ∨ C i 7 = 0 ∨
        C i 8 = 0 := by
    fin_cases i <;> simp_all
  simpa [rowParity] using
    ConwayArithmetic.parity_count_nine_zero
      (C i 0) (C i 1) (C i 2) (C i 3) (C i 4)
      (C i 5) (C i 6) (C i 7) (C i 8) hz hs'

private theorem rowParity_of_diag_two
    (C : Matrix (Fin 9) (Fin 9) ℕ)
    (hsymm : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, C i j = 14)
    (hsq : ∀ i j,
      (∑ k, C i k * C k j) + C i j =
        (if i = j then 12 else 0) + 22)
    (i : Fin 9) (htwo : C i i = 2) :
    rowParity C i = 4 := by
  have hr := hrow i
  have hr' :
      C i 0 + C i 1 + C i 2 + C i 3 + C i 4 +
        C i 5 + C i 6 + C i 7 + C i 8 = 14 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hr
  have hs := square_sum_plus_diag_eq_34 C hsymm hsq i
  have hsExpanded :
      (C i 0 * C i 0 + C i 1 * C i 1 + C i 2 * C i 2 +
        C i 3 * C i 3 + C i 4 * C i 4 + C i 5 * C i 5 +
        C i 6 * C i 6 + C i 7 * C i 7 + C i 8 * C i 8) + 2 = 34 := by
    simpa [Fin.sum_univ_succ, htwo, add_assoc] using hs
  have hs' :
      C i 0 * C i 0 + C i 1 * C i 1 + C i 2 * C i 2 +
        C i 3 * C i 3 + C i 4 * C i 4 + C i 5 * C i 5 +
        C i 6 * C i 6 + C i 7 * C i 7 + C i 8 * C i 8 = 32 := by
    omega
  have hd :
      C i 0 = 2 ∨ C i 1 = 2 ∨ C i 2 = 2 ∨ C i 3 = 2 ∨
        C i 4 = 2 ∨ C i 5 = 2 ∨ C i 6 = 2 ∨ C i 7 = 2 ∨
        C i 8 = 2 := by
    fin_cases i <;> simp_all
  simpa [rowParity] using
    ConwayArithmetic.parity_count_nine_two
      (C i 0) (C i 1) (C i 2) (C i 3) (C i 4)
      (C i 5) (C i 6) (C i 7) (C i 8) hd hr' hs'

private theorem bit4_oddBit (n : ℕ) :
    ConwayParity36.bit4 (oddBit n) = BitVec.ofNat 4 (n % 2) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
    simp [ConwayParity36.bit4, oddBit, h]

private theorem degree_encode
    (C : Matrix (Fin 9) (Fin 9) ℕ)
    (hsymm : ∀ i j, C i j = C j i)
    (hdiagEven : ∀ i, C i i % 2 = 0)
    (i : Fin 9) :
    ConwayParity36.degree (encode C) i =
      BitVec.ofNat 4 (rowParity C i) := by
  simp [ConwayParity36.degree, edge_encode C hsymm hdiagEven,
    bit4_oddBit, rowParity, BitVec.ofNat_add_ofNat]

private theorem degree_of_diag_zero
    (C : Matrix (Fin 9) (Fin 9) ℕ)
    (hsymm : ∀ i j, C i j = C j i)
    (hsq : ∀ i j,
      (∑ k, C i k * C k j) + C i j =
        (if i = j then 12 else 0) + 22)
    (hdiagEven : ∀ i, C i i % 2 = 0)
    (i : Fin 9) (hzero : C i i = 0) :
    ConwayParity36.degree (encode C) i = 2 ∨
      ConwayParity36.degree (encode C) i = 6 := by
  rw [degree_encode C hsymm hdiagEven i]
  rcases rowParity_of_diag_zero C hsymm hsq i hzero with hp | hp
  · left
    simp [hp]
  · right
    simp [hp]

private theorem degree_of_diag_two
    (C : Matrix (Fin 9) (Fin 9) ℕ)
    (hsymm : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, C i j = 14)
    (hsq : ∀ i j,
      (∑ k, C i k * C k j) + C i j =
        (if i = j then 12 else 0) + 22)
    (hdiagEven : ∀ i, C i i % 2 = 0)
    (i : Fin 9) (htwo : C i i = 2) :
    ConwayParity36.degree (encode C) i = 4 := by
  rw [degree_encode C hsymm hdiagEven i]
  simp [rowParity_of_diag_two C hsymm hrow hsq i htwo]

private theorem oddBit_add (a b : ℕ) :
    (oddBit a ^^ oddBit b) = oddBit (a + b) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    simp [oddBit, Nat.add_mod, ha, hb]

private theorem oddBit_eq_false
    (n : ℕ) (h : n % 2 = 0) :
    oddBit n = false := by
  simp [oddBit, h]

private theorem oddBit_eq_true
    (n : ℕ) (h : n % 2 = 1) :
    oddBit n = true := by
  simp [oddBit, h]

private theorem oddBit_mul (a b : ℕ) :
    (oddBit a && oddBit b) = oddBit (a * b) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha
  · rcases Nat.mod_two_eq_zero_or_one b with hb | hb
    · have hab : (a * b) % 2 = 0 := by
        rw [Nat.mul_mod, ha, hb]
      rw [oddBit_eq_false a ha, oddBit_eq_false (a * b) hab]
      rfl
    · have hab : (a * b) % 2 = 0 := by
        rw [Nat.mul_mod, ha, hb]
      rw [oddBit_eq_false a ha, oddBit_eq_false (a * b) hab]
      rfl
  · rcases Nat.mod_two_eq_zero_or_one b with hb | hb
    · have hab : (a * b) % 2 = 0 := by
        rw [Nat.mul_mod, ha, hb]
      rw [oddBit_eq_true a ha, oddBit_eq_false b hb,
        oddBit_eq_false (a * b) hab]
      simp
    · have hab : (a * b) % 2 = 1 := by
        rw [Nat.mul_mod, ha, hb]
      rw [oddBit_eq_true a ha, oddBit_eq_true b hb,
        oddBit_eq_true (a * b) hab]
      simp

private def commonNat
    (C : Matrix (Fin 9) (Fin 9) ℕ) (i j : Fin 9) : ℕ :=
  C i 0 * C 0 j + C i 1 * C 1 j + C i 2 * C 2 j +
    C i 3 * C 3 j + C i 4 * C 4 j + C i 5 * C 5 j +
    C i 6 * C 6 j + C i 7 * C 7 j + C i 8 * C 8 j

private theorem commonParity_encode
    (C : Matrix (Fin 9) (Fin 9) ℕ)
    (hsymm : ∀ i j, C i j = C j i)
    (hdiagEven : ∀ i, C i i % 2 = 0)
    (i j : Fin 9) :
    ConwayParity36.commonParity (encode C) i j =
      oddBit (commonNat C i j) := by
  simp [ConwayParity36.commonParity, edge_encode C hsymm hdiagEven,
    oddBit_mul, oddBit_add, commonNat]

private theorem mod_two_eq_of_add_eq_twice
    (a b n : ℕ) (h : a + b = 2 * n) :
    a % 2 = b % 2 := by
  omega

private theorem commonNat_parity
    (C : Matrix (Fin 9) (Fin 9) ℕ)
    (hsq : ∀ i j,
      (∑ k, C i k * C k j) + C i j =
        (if i = j then 12 else 0) + 22)
    (i j : Fin 9) :
    commonNat C i j % 2 = C i j % 2 := by
  have h := hsq i j
  have hsum :
      (∑ k, C i k * C k j) = commonNat C i j := by
    simp [commonNat, Fin.sum_univ_succ, add_assoc]
  rw [hsum] at h
  by_cases hij : i = j
  · rw [if_pos hij] at h
    norm_num at h
    exact mod_two_eq_of_add_eq_twice _ _ 17 (by norm_num; exact h)
  · rw [if_neg hij] at h
    norm_num at h
    exact mod_two_eq_of_add_eq_twice _ _ 11 (by norm_num; exact h)

private theorem commonParity_eq_edge
    (C : Matrix (Fin 9) (Fin 9) ℕ)
    (hsymm : ∀ i j, C i j = C j i)
    (hsq : ∀ i j,
      (∑ k, C i k * C k j) + C i j =
        (if i = j then 12 else 0) + 22)
    (hdiagEven : ∀ i, C i i % 2 = 0)
    (i j : Fin 9) :
    ConwayParity36.commonParity (encode C) i j =
      ConwayParity36.edge (encode C) i j := by
  rw [commonParity_encode C hsymm hdiagEven i j,
    edge_encode C hsymm hdiagEven i j]
  simp [oddBit, commonNat_parity C hsq i j]

private def diagTwoNat
    (C : Matrix (Fin 9) (Fin 9) ℕ) (i : Fin 9) : ℕ :=
  if C i i = 2 then 1 else 0

private theorem bit4_degreeFour_eq_diagTwo
    (C : Matrix (Fin 9) (Fin 9) ℕ)
    (x : BitVec 36) (i : Fin 9)
    (hiff : ConwayParity36.degree x i = 4 ↔ C i i = 2) :
    ConwayParity36.bit4 (ConwayParity36.degree x i == 4) =
      BitVec.ofNat 4 (diagTwoNat C i) := by
  by_cases htwo : C i i = 2
  · have hdegree : ConwayParity36.degree x i = 4 := hiff.mpr htwo
    simp [ConwayParity36.bit4, diagTwoNat, htwo, hdegree]
  · have hdegree : ConwayParity36.degree x i ≠ 4 := by
      intro hfour
      exact htwo (hiff.mp hfour)
    have hbeq : (ConwayParity36.degree x i == (4 : BitVec 4)) = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact hdegree (beq_iff_eq.mp htrue)
    rw [hbeq]
    simp [ConwayParity36.bit4, diagTwoNat, htwo]

theorem main
    (C : Matrix (Fin 9) (Fin 9) ℕ) (hsymm : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, C i j = 14)
    (hsq : ∀ i j, (∑ k, C i k * C k j) + C i j =
      (if i = j then 12 else 0) + 22)
    (hdiag : ∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4)
    (htr : (∑ i, C i i) = 10)
    (hfour : ∀ i, C i i ≠ 4) : False := by
  have hdiag02 (i : Fin 9) : C i i = 0 ∨ C i i = 2 := by
    rcases hdiag i with hzero | htwo | hfour'
    · exact Or.inl hzero
    · exact Or.inr htwo
    · exact (hfour i hfour').elim
  have hdiagEven (i : Fin 9) : C i i % 2 = 0 := by
    rcases hdiag02 i with hzero | htwo
    · simp [hzero]
    · simp [htwo]
  have hdegree (i : Fin 9) :
      ConwayParity36.degree (encode C) i = 2 ∨
        ConwayParity36.degree (encode C) i = 4 ∨
        ConwayParity36.degree (encode C) i = 6 := by
    rcases hdiag02 i with hzero | htwo
    · rcases degree_of_diag_zero C hsymm hsq hdiagEven i hzero with htwo' | hsix
      · exact Or.inl htwo'
      · exact Or.inr (Or.inr hsix)
    · exact Or.inr
        (Or.inl (degree_of_diag_two C hsymm hrow hsq hdiagEven i htwo))
  have hdegreeFour (i : Fin 9) :
      ConwayParity36.degree (encode C) i = 4 ↔ C i i = 2 := by
    constructor
    · intro hdegree4
      rcases hdiag02 i with hzero | htwo
      · rcases degree_of_diag_zero C hsymm hsq hdiagEven i hzero with
          hdegree2 | hdegree6
        · rw [hdegree2] at hdegree4
          exact ((by decide : (2 : BitVec 4) ≠ 4) hdegree4).elim
        · rw [hdegree6] at hdegree4
          exact ((by decide : (6 : BitVec 4) ≠ 4) hdegree4).elim
      · exact htwo
    · intro htwo
      exact degree_of_diag_two C hsymm hrow hsq hdiagEven i htwo
  have hdiagAsDouble (i : Fin 9) :
      C i i = 2 * diagTwoNat C i := by
    rcases hdiag02 i with hzero | htwo
    · simp [diagTwoNat, hzero]
    · simp [diagTwoNat, htwo]
  have htwiceCount : 2 * (∑ i, diagTwoNat C i) = 10 := by
    calc
      2 * (∑ i, diagTwoNat C i) =
          ∑ i, 2 * diagTwoNat C i := by
            rw [Finset.mul_sum]
      _ = ∑ i, C i i := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hdiagAsDouble i).symm
      _ = 10 := htr
  have hdiagTwoCount : (∑ i, diagTwoNat C i) = 5 := by
    omega
  let A : ConwayAbstract.Adj := fun i j => oddBit (C i j)
  have hA_symm : A.IsSymm := by
    ext i j
    change oddBit (C j i) = oddBit (C i j)
    rw [hsymm j i]
  have hA_loop : ∀ i, A i i = false := by
    intro i
    exact oddBit_diag_false C hdiagEven i
  have hA_idem : A * A = A := by
    ext i j
    have hp := commonParity_eq_edge C hsymm hsq hdiagEven i j
    rw [Matrix.mul_apply]
    change (∑ k, oddBit (C i k) * oddBit (C k j)) = oddBit (C i j)
    simpa [ConwayParity36.commonParity,
      edge_encode C hsymm hdiagEven, Fin.sum_univ_succ,
      Bool.add_eq_xor, Bool.mul_eq_and] using hp
  have hA_degree_eq (i : Fin 9) :
      ConwayAbstract.natDegree A i = rowParity C i := by
    simp [ConwayAbstract.natDegree, A, rowParity, Fin.sum_univ_succ,
      oddBit_toNat, add_assoc]
  have hA_degree (i : Fin 9) :
      ConwayAbstract.natDegree A i = 2 ∨
        ConwayAbstract.natDegree A i = 4 ∨
        ConwayAbstract.natDegree A i = 6 := by
    rw [hA_degree_eq]
    rcases hdiag02 i with hzero | htwo
    · rcases rowParity_of_diag_zero C hsymm hsq i hzero with hp | hp
      · exact Or.inl hp
      · exact Or.inr (Or.inr hp)
    · exact Or.inr
        (Or.inl (rowParity_of_diag_two C hsymm hrow hsq i htwo))
  have hA_degreeFour (i : Fin 9) :
      ConwayAbstract.natDegree A i = 4 ↔ C i i = 2 := by
    rw [hA_degree_eq]
    constructor
    · intro hdegree4
      rcases hdiag02 i with hzero | htwo
      · rcases rowParity_of_diag_zero C hsymm hsq i hzero with hp | hp <;>
          omega
      · exact htwo
    · intro htwo
      exact rowParity_of_diag_two C hsymm hrow hsq i htwo
  have hA_count : ConwayAbstract.degreeFourCount A = 5 := by
    rw [ConwayAbstract.degreeFourCount]
    calc
      (∑ i, if ConwayAbstract.natDegree A i = 4 then 1 else 0) =
          ∑ i, diagTwoNat C i := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases htwo : C i i = 2
        · simp [diagTwoNat, htwo, (hA_degreeFour i).mpr htwo]
        · have hdegree4 : ConwayAbstract.natDegree A i ≠ 4 := by
            intro h
            exact htwo ((hA_degreeFour i).mp h)
          simp [diagTwoNat, htwo, hdegree4]
      _ = 5 := hdiagTwoCount
  exact ConwayAbstract.no_conditions A
    ⟨hA_symm, hA_loop, hA_idem, hA_degree, hA_count⟩

end ConwaySolution

theorem solution
    (C : Matrix (Fin 9) (Fin 9) ℕ) (hsymm : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, C i j = 14)
    (hsq : ∀ i j, (∑ k, C i k * C k j) + C i j =
      (if i = j then 12 else 0) + 22)
    (hdiag : ∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4)
    (htr : (∑ i, C i i) = 10)
    (hfour : ∀ i, C i i ≠ 4) : False :=
  ConwaySolution.main C hsymm hrow hsq hdiag htr hfour
