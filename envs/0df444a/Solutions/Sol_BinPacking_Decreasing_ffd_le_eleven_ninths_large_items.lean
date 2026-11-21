-- Prove2me | solution 1 for BinPacking.Decreasing.ffd_le_eleven_ninths_large_items
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T19:34:03.243147+00:00
-- url     : https://prove2.me/submissions/41924e1e-c9ec-4ecc-b0a5-6c4b9dd90709

import Definitions.Def_BinPacking_Decreasing_Model
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Relation
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

set_option autoImplicit false

/- Definitions/Def_BinPacking_Decreasing_Weight.lean -/
section

namespace BinPacking.Decreasing

/-- The piece number of `x` (p. 316): `x` is a `k`-piece when `x ∈ (1/(k+1), 1/k]`, i.e.
`k = ⌊1/x⌋`. Meaningful for `0 < x ≤ 1` (then `k ≥ 1`). -/
noncomputable def pieceNum (x : ℝ) : ℤ := ⌊1 / x⌋

/-- `w₁(x) = ⌊1/x⌋⁻¹` (p. 316); for a `k`-piece, `w₁(x) = 1/k`. -/
noncomputable def w1 (x : ℝ) : ℝ := ((pieceNum x : ℝ))⁻¹

/-- `(x, y)` obeys relation `k` (p. 317): `x` is a `k`-piece and `k x + y ≤ 1`. Since the piece
number of `x` is unique, this is `⌊1/x⌋ · x + y ≤ 1`. -/
abbrev ObeysRelation (x y : ℝ) : Prop := (pieceNum x : ℝ) * x + y ≤ 1

/-- `w₂(x, y)` (p. 317): `w₁(x) + ((k − 1)/k) w₁(y)` if `(x, y)` obeys relation `k`,
and `w₁(x) + w₁(y)` otherwise. -/
noncomputable def w2 (x y : ℝ) : ℝ :=
  if ObeysRelation x y then w1 x + ((pieceNum x : ℝ) - 1) / (pieceNum x : ℝ) * w1 y
  else w1 x + w1 y

/-- The partitions of the positions `{0, …, n − 1}` into one- and two-element sets, encoded as
involutions `m` of `Fin n`: `i` is a singleton when `m i = i`, and `{i, m i}` is a pair
otherwise. The identity (all singletons) is always one of them. -/
def partitions (n : ℕ) : Finset (Fin n → Fin n) :=
  Finset.univ.filter (fun m => ∀ i, m (m i) = i)

/-- `w₁₂(π)` (p. 316) for the partition `m` of the positions of the list `S`: the sum of `w₁(x)`
over singletons `{x}` plus the sum of `w₂(x, y)` over pairs `{x, y}` with `index(x) < index(y)`
(each pair is counted once, from its smaller position). -/
noncomputable def w12 (S : List ℝ) (m : Fin S.length → Fin S.length) : ℝ :=
  ∑ i : Fin S.length,
    if m i = i then w1 (S.get i)
    else if i < m i then w2 (S.get i) (S.get (m i)) else 0

/-- The weight `W(X)` (pp. 315–316): `X` is arranged into nonincreasing order (`sortDesc`), so
that `index` is the position in that order and every pair `(x, y)` with `index(x) < index(y)`
has `x ≥ y`; then `W(X) = min_π w₁₂(π)` over all partitions `π` of the positions into one- and
two-element sets (a finite nonempty family). -/
noncomputable def W (X : List ℝ) : ℝ :=
  (partitions (sortDesc X).length).inf' ⟨id, by simp [partitions]⟩ (w12 (sortDesc X))

end BinPacking.Decreasing

end

/- assembly/DiscountConfigurations.lean -/
section

namespace BinPacking.Decreasing

private theorem pieceNum_of_mul_bounds (x : ℝ) (k : ℤ) (hx : 0 < x)
    (hlo : 1 < ((k : ℝ) + 1) * x) (hhi : (k : ℝ) * x ≤ 1) :
    pieceNum x = k := by
  exact Int.floor_eq_iff.mpr ⟨(le_div_iff₀ hx).2 hhi, (div_lt_iff₀ hx).2 hlo⟩

/-- The B interval has reciprocal floor two. -/
theorem pieceNum_B {x : ℝ} (hlo : 1 / 3 < x) (hhi : x ≤ 1 / 2) : pieceNum x = 2 := by
  refine pieceNum_of_mul_bounds x 2 (by linarith) ?_ ?_
  all_goals (norm_num; linarith)

/-- The C interval has reciprocal floor three. -/
theorem pieceNum_C {x : ℝ} (hlo : 1 / 4 < x) (hhi : x ≤ 1 / 3) : pieceNum x = 3 := by
  refine pieceNum_of_mul_bounds x 3 (by linarith) ?_ ?_
  all_goals (norm_num; linarith)

/-- The D interval has reciprocal floor four. -/
theorem pieceNum_D {x : ℝ} (hlo : 1 / 5 < x) (hhi : x ≤ 1 / 4) : pieceNum x = 4 := by
  refine pieceNum_of_mul_bounds x 4 (by linarith) ?_ ?_
  all_goals (norm_num; linarith)

private theorem relation_of_scaled_sum (x y : ℝ) (k : ℤ)
    (hnum : pieceNum x = k) (hfit : (k : ℝ) * x + y ≤ 1) : ObeysRelation x y := by
  simpa only [ObeysRelation, hnum] using hfit

/-- A feasible three-item bin with two B-pieces allows the smaller B-piece
to be paired with the remaining piece. -/
theorem relation_of_two_B (b₁ b₂ y : ℝ)
    (hb₂ : 1 / 3 < b₂ ∧ b₂ ≤ 1 / 2) (horder : b₂ ≤ b₁)
    (hfit : b₁ + b₂ + y ≤ 1) : ObeysRelation b₂ y := by
  apply relation_of_scaled_sum b₂ y 2 (pieceNum_B hb₂.1 hb₂.2)
  norm_num
  linarith

/-- The smallest C-piece of a feasible bin with three C-pieces can be paired
with the remaining piece, covering the CCCD and CCCE configurations. -/
theorem relation_of_three_C (c₁ c₂ c₃ y : ℝ)
    (hc₃ : 1 / 4 < c₃ ∧ c₃ ≤ 1 / 3) (horder₁ : c₃ ≤ c₁) (horder₂ : c₃ ≤ c₂)
    (hfit : c₁ + c₂ + c₃ + y ≤ 1) : ObeysRelation c₃ y := by
  exact relation_of_scaled_sum c₃ y 3 (pieceNum_C hc₃.1 hc₃.2) (by norm_num; linarith)

/-- In BCDD, BCDE, and BCEE, the B-piece can be paired with either item
after the C-piece. -/
theorem relation_B_of_other_C (b x c y : ℝ)
    (hb : 1 / 3 < b ∧ b ≤ 1 / 2) (hc : 1 / 4 < c)
    (hx : 2 / 11 < x) (hy : 2 / 11 < y)
    (hfit : b + x + c + y ≤ 1) : ObeysRelation b x := by
  exact relation_of_scaled_sum b x 2 (pieceNum_B hb.1 hb.2) (by norm_num; linarith)

/-- In BCDD, the C-piece can use the D-piece unused by the relation-2 pair. -/
theorem relation_C_of_other_B_and_D (c d b d' : ℝ)
    (hc : 1 / 4 < c ∧ c ≤ 1 / 3) (hb : 1 / 3 < b)
    (hd : 1 / 5 < d) (hd' : 1 / 5 < d')
    (hfit : c + d + b + d' ≤ 1) : ObeysRelation c d := by
  exact relation_of_scaled_sum c d 3 (pieceNum_C hc.1 hc.2) (by norm_num; linarith)

/-- In BDDD, the B-piece can be paired with any D-piece. -/
theorem relation_B_of_three_D (b d₁ d₂ d₃ : ℝ)
    (hb : 1 / 3 < b ∧ b ≤ 1 / 2) (hd₁ : 1 / 5 < d₁)
    (hd₂ : 1 / 5 < d₂) (hd₃ : 1 / 5 < d₃)
    (hfit : b + d₁ + d₂ + d₃ ≤ 1) : ObeysRelation b d₁ := by
  exact relation_of_scaled_sum b d₁ 2 (pieceNum_B hb.1 hb.2) (by norm_num; linarith)

/-- In DDDDE, the E-piece can be paired with the smallest D-piece. -/
theorem relation_of_four_D (d₁ d₂ d₃ d₄ y : ℝ)
    (hd₄ : 1 / 5 < d₄ ∧ d₄ ≤ 1 / 4) (horder₁ : d₄ ≤ d₁) (horder₂ : d₄ ≤ d₂)
    (horder₃ : d₄ ≤ d₃) (hfit : d₁ + d₂ + d₃ + d₄ + y ≤ 1) :
    ObeysRelation d₄ y := by
  exact relation_of_scaled_sum d₄ y 4 (pieceNum_D hd₄.1 hd₄.2) (by norm_num; linarith)

/-- In BDDE, a B-piece larger than two fifths forces each D–E pair
to have total size at most two fifths. -/
theorem pair_size_le_of_large_B_and_other_D (b d d' e : ℝ)
    (hb : 2 / 5 < b) (hd' : 1 / 5 < d') (hfit : b + d + d' + e ≤ 1) :
    d + e ≤ 2 / 5 := by
  linarith

/-- In DDDDE, each choice of a D-piece and the E-piece has total size at most
two fifths. -/
theorem pair_size_le_of_three_other_D (d d₁ d₂ d₃ e : ℝ)
    (hd₁ : 1 / 5 < d₁) (hd₂ : 1 / 5 < d₂) (hd₃ : 1 / 5 < d₃)
    (hfit : d + d₁ + d₂ + d₃ + e ≤ 1) : d + e ≤ 2 / 5 := by
  linarith

/-- In DDDEE, at least one of two disjoint D–E pairs has total size at most
two fifths. -/
theorem pair_size_le_of_three_D_two_E (d₁ d₂ d₃ e₄ e₅ : ℝ)
    (hd₃ : 1 / 5 < d₃) (hfit : d₁ + d₂ + d₃ + e₄ + e₅ ≤ 1) :
    d₁ + e₄ ≤ 2 / 5 ∨ d₂ + e₅ ≤ 2 / 5 := by
  by_cases h : d₁ + e₄ ≤ 2 / 5
  · exact Or.inl h
  · exact Or.inr (by linarith [lt_of_not_ge h])

end BinPacking.Decreasing

end

/- assembly/ResponsibilityCosts.lean -/
section

namespace BinPacking.Decreasing

/-- The four piece classes below one half in the range `(2/11, 1]`. -/
inductive SmallPieceClass
  | B | C | D | E
  deriving DecidableEq

/-- The singleton allowance in Table 5.1. Case I is `hasC = true`. -/
noncomputable def singletonAllowance (hasC : Bool) : SmallPieceClass → ℝ
  | .B => 1 / 2
  | .C => if hasC then 13 / 36 else 5 / 18
  | .D => if hasC then 1 / 4 else 5 / 18
  | .E => 1 / 5

/-- Claims 5.9.14 and 5.9.15 bound the count of indirect responsibilities. -/
def indirectCountLimit (hasC : Bool) : SmallPieceClass → ℕ
  | .B => if hasC then 2 else 3
  | .C => 1
  | .D => if hasC then 0 else 1
  | .E => 0

/-- An upper bound on the weight of the direct responsibility. Claim 5.9.18
forces a B-piece with indirect responsibilities to have a smaller direct piece. -/
noncomputable def directWeightLimit (hasC : Bool) (count : ℕ) : SmallPieceClass → ℝ
  | .B => if count = 0 then 1 / 2 else if hasC then 1 / 3 else 1 / 4
  | .C => if hasC then 1 / 3 else 1 / 4
  | .D | .E => 1 / 4

/-- An indirect piece costs a quarter in singleton weight and pays two ninths
in credit. This leaves at most one thirty-sixth per indirect responsibility. -/
theorem responsibility_cost_le (factor direct indirect extra directCap extraMin : ℝ)
    (count countCap : ℕ)
    (hfactor : 0 ≤ factor)
    (hdirect : direct ≤ directCap)
    (hindirect : indirect ≤ (count : ℝ) / 4)
    (hcount : count ≤ countCap)
    (hextra : extraMin ≤ extra) :
    factor * direct + indirect - 2 / 9 * ((count : ℝ) + extra) ≤
      factor * directCap + (countCap : ℝ) / 36 - 2 / 9 * extraMin := by
  have hdirect' := mul_le_mul_of_nonneg_left hdirect hfactor
  have hcount' : (count : ℝ) ≤ countCap := by exact_mod_cast hcount
  linarith

/-- Claim 5.9.23 follows from the weight and count limits and the charge for
promoting the direct piece of an E-piece. -/
theorem singleton_cost_le_allowance (hasC : Bool) (kind : SmallPieceClass)
    (direct indirect extra : ℝ) (count : ℕ)
    (hdirect : direct ≤ directWeightLimit hasC count kind)
    (hindirect : indirect ≤ (count : ℝ) / 4)
    (hcount : count ≤ indirectCountLimit hasC kind)
    (hextra : 0 ≤ extra)
    (hpromotion : kind = .E → direct ≤ 1 / 5 ∨ 2 / 3 ≤ extra) :
    direct + indirect - 2 / 9 * ((count : ℝ) + extra) ≤ singletonAllowance hasC kind := by
  have hcount' : (count : ℝ) ≤ indirectCountLimit hasC kind := by exact_mod_cast hcount
  cases kind <;> cases hasC <;>
    simp only [singletonAllowance, directWeightLimit, indirectCountLimit,
      Bool.false_eq_true, if_false, if_true] at hdirect hcount' ⊢
  all_goals simp only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at hcount'
  case B.false | B.true =>
    split at hdirect
    · rename_i hzero
      subst count
      norm_num at *
      linarith
    · linarith
  case E.false | E.true =>
    rcases hpromotion rfl with h | h <;> linarith
  all_goals linarith

/-- A piece whose direct responsibility is no larger than itself has this weight cap. -/
noncomputable def unpromotedWeightLimit (hasC : Bool) : SmallPieceClass → ℝ
  | .E => 1 / 5
  | kind => directWeightLimit hasC 0 kind

/-- The smaller weight cap when the first member of a pair is demoted. -/
noncomputable def demotedWeightLimit (hasC : Bool) : SmallPieceClass → ℝ
  | .B => if hasC then 1 / 3 else 1 / 4
  | .C => 1 / 4
  | .D => 1 / 5
  | .E => 0

/-- A class-B piece retaining a class-B responsibility has no indirect responsibilities. -/
def matchingCountLimit (hasC : Bool) : SmallPieceClass → ℕ
  | .B => 0
  | kind => indirectCountLimit hasC kind

/-- The remaining fraction of the second item's weight when the discount applies. -/
noncomputable def pairFactor : SmallPieceClass → ℝ
  | .B => 1 / 2
  | .C => 2 / 3
  | .D => 3 / 4
  | .E => 4 / 5

/-- Table 5.2 lists the pair configurations used in Johnson's case analysis. -/
noncomputable def pairAllowance : Bool → SmallPieceClass → SmallPieceClass → Option ℝ
  | true, .B, .C => some (3 / 4)
  | true, .B, .D => some (23 / 36)
  | _, .B, .E => some (65 / 108)
  | true, .C, .D => some (19 / 36)
  | true, .C, .E => some (89 / 180)
  | true, .D, .E => some (2 / 5)
  | false, .B, .C | false, .B, .D => some (47 / 72)
  | false, .D, .E => some (77 / 180)
  | _, _, _ => none

private noncomputable def costCap (factor directCap : ℝ) (countCap : ℕ) (extraMin : ℝ) : ℝ :=
  factor * directCap + (countCap : ℝ) / 36 - 2 / 9 * extraMin

private theorem pair_allowance_caps (hasC : Bool) (left right : SmallPieceClass) (allowance : ℝ)
    (hrow : pairAllowance hasC left right = some allowance) :
    costCap 1 (unpromotedWeightLimit hasC left) (matchingCountLimit hasC left) 0 +
        costCap (pairFactor left) (unpromotedWeightLimit hasC right)
          (indirectCountLimit hasC right) 0 ≤ allowance ∧
      costCap 1 (demotedWeightLimit hasC left) (indirectCountLimit hasC left) 0 +
        singletonAllowance hasC right ≤ allowance ∧
      (left = .D ∨ left = .E →
        costCap 1 (1 / 4) (indirectCountLimit hasC left) (2 / 3) +
          singletonAllowance hasC right ≤ allowance) ∧
      (right = .D ∨ right = .E →
        singletonAllowance hasC left +
          costCap 1 (1 / 4) (indirectCountLimit hasC right) (2 / 3) ≤ allowance) := by
  cases left <;> cases right <;> cases hasC <;> simp [pairAllowance] at hrow
  all_goals subst allowance
  all_goals
    norm_num [costCap, unpromotedWeightLimit, matchingCountLimit, pairFactor,
      indirectCountLimit, demotedWeightLimit, singletonAllowance, directWeightLimit]

/-- The weight of `f₁`, the singleton weight of `f₂`, and their credits. -/
structure ResponsibilityWeights where
  direct : ℝ
  indirect : ℝ
  extra : ℝ
  count : ℕ

namespace ResponsibilityWeights

/-- In a non-A-bin the base credit is the count of indirect pieces. -/
noncomputable def credit (r : ResponsibilityWeights) : ℝ := r.count + r.extra

noncomputable def weightedCost (r : ResponsibilityWeights) (factor : ℝ) : ℝ :=
  factor * r.direct + r.indirect - 2 / 9 * r.credit

/-- The bounds on `f₁`, `f₂`, and `g₂` used for the singleton allowance. -/
structure Admissible (r : ResponsibilityWeights) (hasC : Bool) (kind : SmallPieceClass) : Prop where
  direct_le : r.direct ≤ directWeightLimit hasC r.count kind
  indirect_le : r.indirect ≤ (r.count : ℝ) / 4
  count_le : r.count ≤ indirectCountLimit hasC kind
  extra_nonneg : 0 ≤ r.extra
  promotion_charge : kind = .E → r.direct ≤ 1 / 5 ∨ 2 / 3 ≤ r.extra

theorem Admissible.cost_le_allowance {r : ResponsibilityWeights} {hasC : Bool}
    {kind : SmallPieceClass} (h : r.Admissible hasC kind) :
    r.weightedCost 1 ≤ singletonAllowance hasC kind := by
  simpa only [weightedCost, credit, one_mul] using
    singleton_cost_le_allowance hasC kind r.direct r.indirect r.extra r.count
      h.direct_le h.indirect_le h.count_le h.extra_nonneg h.promotion_charge

private theorem Admissible.cost_le_cap {r : ResponsibilityWeights} {hasC : Bool}
    {kind : SmallPieceClass} (h : r.Admissible hasC kind)
    {factor directCap extraMin : ℝ} {countCap : ℕ}
    (hfactor : 0 ≤ factor) (hdirect : r.direct ≤ directCap)
    (hcount : r.count ≤ countCap) (hextra : extraMin ≤ r.extra) :
    r.weightedCost factor ≤ costCap factor directCap countCap extraMin :=
  responsibility_cost_le factor r.direct r.indirect r.extra directCap extraMin
    r.count countCap hfactor hdirect h.indirect_le hcount hextra

end ResponsibilityWeights

/-- Claim 5.9.26 from the four possible outcomes for the discount. The value
`joint` is the weight of the two direct responsibilities. -/
theorem pair_cost_le_allowance (hasC : Bool) (left right : SmallPieceClass)
    (x y : ResponsibilityWeights) (joint allowance : ℝ)
    (hrow : pairAllowance hasC left right = some allowance)
    (hx : x.Admissible hasC left) (hy : y.Admissible hasC right)
    (hplain : joint ≤ x.direct + y.direct)
    (halternatives :
      (joint ≤ x.direct + pairFactor left * y.direct ∧
        x.direct ≤ unpromotedWeightLimit hasC left ∧
        y.direct ≤ unpromotedWeightLimit hasC right ∧
        x.count ≤ matchingCountLimit hasC left) ∨
      x.direct ≤ demotedWeightLimit hasC left ∨
      ((left = .D ∨ left = .E) ∧ 2 / 3 ≤ x.extra) ∨
      ((right = .D ∨ right = .E) ∧ 2 / 3 ≤ y.extra)) :
    joint + x.indirect + y.indirect - 2 / 9 * (x.credit + y.credit) ≤ allowance := by
  obtain ⟨hmatch, hdemote, hpromoteLeft, hpromoteRight⟩ :=
    pair_allowance_caps hasC left right allowance hrow
  have finish {p q capX capY : ℝ} (hjoint : joint ≤ p * x.direct + q * y.direct)
      (hcostX : x.weightedCost p ≤ capX) (hcostY : y.weightedCost q ≤ capY)
      (hcaps : capX + capY ≤ allowance) :
      joint + x.indirect + y.indirect - 2 / 9 * (x.credit + y.credit) ≤ allowance := by
    unfold ResponsibilityWeights.weightedCost at hcostX hcostY
    linarith
  rcases halternatives with
    ⟨hjoint, hleft, hright, hcount⟩ | hleft | ⟨hkind, hextra⟩ | ⟨hkind, hextra⟩
  · refine finish (p := 1) (q := pairFactor left) ?_ ?_ ?_ hmatch
    · simpa only [one_mul] using hjoint
    · exact hx.cost_le_cap zero_le_one hleft hcount hx.extra_nonneg
    · exact hy.cost_le_cap (by cases left <;> norm_num [pairFactor]) hright hy.count_le
        hy.extra_nonneg
  · exact finish (p := 1) (q := 1) (by simpa only [one_mul] using hplain)
      (hx.cost_le_cap zero_le_one hleft hx.count_le hx.extra_nonneg) hy.cost_le_allowance hdemote
  · have hdirect : x.direct ≤ 1 / 4 := by
      rcases hkind with rfl | rfl <;> exact hx.direct_le
    exact finish (p := 1) (q := 1) (by simpa only [one_mul] using hplain)
      (hx.cost_le_cap zero_le_one hdirect hx.count_le hextra) hy.cost_le_allowance
      (hpromoteLeft hkind)
  · have hdirect : y.direct ≤ 1 / 4 := by
      rcases hkind with rfl | rfl <;> exact hy.direct_le
    exact finish (p := 1) (q := 1) (by simpa only [one_mul] using hplain)
      hx.cost_le_allowance (hy.cost_le_cap zero_le_one hdirect hy.count_le hextra)
      (hpromoteRight hkind)

end BinPacking.Decreasing

end

/- assembly/SingletonBudget.lean -/
section

namespace BinPacking.Decreasing

private theorem of_bounded_counts (P : ℕ → ℕ → ℕ → ℕ → Prop)
    (hfinite : ∀ (b : Fin 3) (c : Fin 4) (d : Fin 5) (e : Fin 6),
      220 * b.val + 165 * c.val + 132 * d.val + 120 * e.val < 660 →
      P b.val c.val d.val e.val)
    (b c d e : ℕ) (hfit : 220 * b + 165 * c + 132 * d + 120 * e < 660) : P b c d e := by
  exact hfinite ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, by omega⟩ ⟨e, by omega⟩ hfit

/-- The necessary capacity condition uses the strict lower limits for classes
`B`, `C`, `D`, and `E`, multiplied by 660. In case I, the singleton allowances
from Table 5.1 suffice outside these configurations. The allowances and budget
are multiplied by 180. -/
theorem singletonBudgetCaseI (b c d e : ℕ)
    (hfit : 220 * b + 165 * c + 132 * d + 120 * e < 660) :
    90 * b + 65 * c + 45 * d + 36 * e ≤ 220 ∨
      (b, c, d, e) ∈
        ([(0, 3, 0, 1), (0, 3, 1, 0), (1, 0, 3, 0), (1, 1, 0, 2),
          (1, 1, 1, 1), (1, 1, 2, 0), (2, 0, 1, 0), (2, 1, 0, 0)] :
          List (ℕ × ℕ × ℕ × ℕ)) := by
  revert b c d e
  apply of_bounded_counts
  decide

/-- In case II the singleton allowances and budget are multiplied by 90. -/
theorem singletonBudgetCaseII (b c d e : ℕ)
    (hfit : 220 * b + 165 * c + 132 * d + 120 * e < 660) :
    45 * b + 25 * c + 25 * d + 18 * e ≤ 110 ∨
      (b, c, d, e) ∈
        ([(0, 0, 3, 2), (0, 0, 4, 1), (1, 0, 2, 1), (1, 0, 3, 0),
          (1, 1, 1, 1), (1, 1, 2, 0), (2, 0, 1, 0), (2, 1, 0, 0)] :
          List (ℕ × ℕ × ℕ × ℕ)) := by
  revert b c d e
  apply of_bounded_counts
  decide

end BinPacking.Decreasing

end

/- assembly/BinConfigurations.lean -/
section

namespace BinPacking.Decreasing

open SmallPieceClass

noncomputable def smallPieceClass (x : ℝ) : SmallPieceClass :=
  if 1 / 3 < x then .B else if 1 / 4 < x then .C else if 1 / 5 < x then .D else .E

def SmallPieceClass.lowerUnits : SmallPieceClass → ℕ
  | .B => 220
  | .C => 165
  | .D => 132
  | .E => 120

def SmallPieceClass.singletonUnits (hasC : Bool) : SmallPieceClass → ℕ
  | .B => 90
  | .C => if hasC then 65 else 50
  | .D => if hasC then 45 else 50
  | .E => 36

theorem smallPieceClass_bounds {x : ℝ} (threshold : 2 / 11 < x) (small : x ≤ 1 / 2) :
    match smallPieceClass x with
    | .B => 1 / 3 < x ∧ x ≤ 1 / 2
    | .C => 1 / 4 < x ∧ x ≤ 1 / 3
    | .D => 1 / 5 < x ∧ x ≤ 1 / 4
    | .E => 2 / 11 < x ∧ x ≤ 1 / 5 := by
  by_cases hB : 1 / 3 < x
  · rw [smallPieceClass, if_pos hB]
    exact ⟨hB, small⟩
  by_cases hC : 1 / 4 < x
  · rw [smallPieceClass, if_neg hB, if_pos hC]
    exact ⟨hC, le_of_not_gt hB⟩
  by_cases hD : 1 / 5 < x
  · rw [smallPieceClass, if_neg hB, if_neg hC, if_pos hD]
    exact ⟨hD, le_of_not_gt hC⟩
  · rw [smallPieceClass, if_neg hB, if_neg hC, if_neg hD]
    exact ⟨threshold, le_of_not_gt hD⟩

private theorem lowerUnits_le_of_size_le {a b : ℝ} (h : a ≤ b) :
    (smallPieceClass a).lowerUnits ≤ (smallPieceClass b).lowerUnits := by
  unfold smallPieceClass
  repeat' split
  all_goals norm_num [SmallPieceClass.lowerUnits] <;> linarith

private theorem lowerUnits_lt_size_mul {x : ℝ} (threshold : 2 / 11 < x) (small : x ≤ 1 / 2) :
    ((smallPieceClass x).lowerUnits : ℝ) < 660 * x := by
  have bounds := smallPieceClass_bounds threshold small
  cases h : smallPieceClass x <;> rw [h] at bounds <;>
    norm_num [SmallPieceClass.lowerUnits] <;> linarith [bounds.1]

private theorem units_sum_eq {f : SmallPieceClass → ℕ} (classes : List SmallPieceClass) :
    (classes.map f).sum = f .B * classes.count .B + f .C * classes.count .C +
      f .D * classes.count .D + f .E * classes.count .E := by
  induction classes with
  | nil => simp
  | cons kind tail ih =>
      cases kind <;> simp [ih, Nat.mul_add] <;> omega

private theorem scaled_singleton_allowance (hasC : Bool) (kind : SmallPieceClass) :
    (kind.singletonUnits hasC : ℝ) = 180 * singletonAllowance hasC kind := by
  cases hasC <;> cases kind <;> norm_num [SmallPieceClass.singletonUnits, singletonAllowance]

private def canonicalClasses (b c d e : ℕ) : List SmallPieceClass :=
  List.replicate b .B ++ List.replicate c .C ++ List.replicate d .D ++ List.replicate e .E

private theorem classes_eq_canonical (classes : List SmallPieceClass)
    (sorted : classes.Pairwise (fun a b => b.lowerUnits ≤ a.lowerUnits)) :
    classes = canonicalClasses (classes.count .B) (classes.count .C)
      (classes.count .D) (classes.count .E) := by
  apply List.Perm.eq_of_pairwise (le := fun a b : SmallPieceClass => b.lowerUnits ≤ a.lowerUnits)
  · intro a b _ _ hab hba
    cases a <;> cases b <;> simp_all [SmallPieceClass.lowerUnits]
  · exact sorted
  · simp [canonicalClasses, List.pairwise_append, List.pairwise_replicate,
      List.mem_replicate, SmallPieceClass.lowerUnits]
    constructor <;> intro _ kind present <;> cases kind <;> simp_all
  · apply List.perm_iff_count.mpr
    intro kind
    cases kind <;> simp [canonicalClasses, List.count_append, List.count_replicate]

/-- The feasible ordered configurations whose Table 5.1 sum can exceed `11/9`. -/
def configurationsBeyondSingletons : Bool → List (List SmallPieceClass)
  | true => [[C, C, C, E], [C, C, C, D], [B, D, D, D], [B, C, E, E],
      [B, C, D, E], [B, C, D, D], [B, B, D], [B, B, C]]
  | false => [[D, D, D, E, E], [D, D, D, D, E], [B, D, D, E], [B, D, D, D],
      [B, C, D, E], [B, C, D, D], [B, B, D], [B, B, C]]

private theorem list_lowerUnits_lt {Piece : Type*} (size : Piece → ℝ) (items : List Piece)
    (nonempty : items ≠ []) (small : ∀ a ∈ items, 2 / 11 < size a ∧ size a ≤ 1 / 2) :
    (((items.map fun a => (smallPieceClass (size a)).lowerUnits).sum : ℕ) : ℝ) <
      660 * (items.map size).sum := by
  induction items with
  | nil => contradiction
  | cons a tail ih =>
      have tailBound : (((tail.map fun b => (smallPieceClass (size b)).lowerUnits).sum : ℕ) : ℝ) ≤
          660 * (tail.map size).sum := by
        by_cases empty : tail = []
        · simp [empty]
        · exact (ih empty (fun b hb => small b (List.mem_cons_of_mem _ hb))).le
      have aSmall := small a List.mem_cons_self
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      linarith [lowerUnits_lt_size_mul aSmall.1 aSmall.2]

private theorem list_scaled_singleton_allowance (hasC : Bool) (classes : List SmallPieceClass) :
    ((classes.map (SmallPieceClass.singletonUnits hasC)).sum : ℝ) =
      180 * (classes.map (singletonAllowance hasC)).sum := by
  induction classes with
  | nil => simp
  | cons a tail ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, scaled_singleton_allowance, ih, mul_add]

/-- Exhaustive classification of actual feasible non-A-bin lists. -/
theorem singleton_allowance_or_configuration {Piece : Type*} (hasC : Bool)
    (size : Piece → ℝ) (items : List Piece)
    (sorted : items.Pairwise (fun a b => size b ≤ size a))
    (small : ∀ a ∈ items, 2 / 11 < size a ∧ size a ≤ 1 / 2) (fits : (items.map size).sum ≤ 1) :
    (((items.map (smallPieceClass ∘ size)).map (singletonAllowance hasC)).sum ≤ 11 / 9) ∨
      (items.map (smallPieceClass ∘ size)) ∈ configurationsBeyondSingletons hasC := by
  by_cases empty : items = []
  · left
    norm_num [empty]
  let classes := items.map (smallPieceClass ∘ size)
  let b := classes.count .B
  let c := classes.count .C
  let d := classes.count .D
  let e := classes.count .E
  have lower : (classes.map SmallPieceClass.lowerUnits).sum < 660 := by
    exact_mod_cast (show ((classes.map SmallPieceClass.lowerUnits).sum : ℝ) < 660 by
      rw [List.map_map]
      exact (list_lowerUnits_lt size items empty small).trans_le (by linarith))
  have hfit : 220 * b + 165 * c + 132 * d + 120 * e < 660 := by
    rw [units_sum_eq] at lower
    exact lower
  have order : classes.Pairwise (fun a b => b.lowerUnits ≤ a.lowerUnits) :=
    List.pairwise_map.mpr (sorted.imp (fun h => lowerUnits_le_of_size_le h))
  have canonical : classes = canonicalClasses b c d e := classes_eq_canonical classes order
  cases hasC
  · rcases singletonBudgetCaseII b c d e hfit with sufficient | exceptional
    · left
      have scaled := list_scaled_singleton_allowance false classes
      rw [units_sum_eq] at scaled
      change (((90 * b + 50 * c + 50 * d + 36 * e : ℕ) : ℝ)) =
        180 * (classes.map (singletonAllowance false)).sum at scaled
      have budget : ((90 * b + 50 * c + 50 * d + 36 * e : ℕ) : ℝ) ≤ 220 := by
        exact_mod_cast (show 90 * b + 50 * c + 50 * d + 36 * e ≤ 220 by omega)
      change (classes.map (singletonAllowance false)).sum ≤ 11 / 9
      linarith
    · right
      change classes ∈ _
      rw [canonical]
      simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at exceptional
      rcases exceptional with h | h | h | h | h | h | h | h <;>
        simp_all [canonicalClasses, configurationsBeyondSingletons]
  · rcases singletonBudgetCaseI b c d e hfit with sufficient | exceptional
    · left
      have scaled := list_scaled_singleton_allowance true classes
      rw [units_sum_eq] at scaled
      change (((90 * b + 65 * c + 45 * d + 36 * e : ℕ) : ℝ)) =
        180 * (classes.map (singletonAllowance true)).sum at scaled
      have budget : ((90 * b + 65 * c + 45 * d + 36 * e : ℕ) : ℝ) ≤ 220 := by
        exact_mod_cast sufficient
      change (classes.map (singletonAllowance true)).sum ≤ 11 / 9
      linarith
    · right
      change classes ∈ _
      rw [canonical]
      simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at exceptional
      rcases exceptional with h | h | h | h | h | h | h | h <;>
        simp_all [canonicalClasses, configurationsBeyondSingletons]

/-- The five configurations that need the refined per-bin arguments. -/
def exceptionalConfigurations : Bool → List (List SmallPieceClass)
  | true => [[B, B, C], [C, C, C, D]]
  | false => [[B, D, D, E], [D, D, D, E, E], [D, D, D, D, E]]

/-- A partition into singletons and eligible pairs, with its total
allowance from Tables 5.1 and 5.2. -/
inductive DiscountPlan {Piece : Type*} (hasC : Bool) (size : Piece → ℝ) : List Piece → ℝ → Prop
  | singletons (items : List Piece) :
      DiscountPlan hasC size items
        (items.map (singletonAllowance hasC ∘ smallPieceClass ∘ size)).sum
  | pair (left right : Piece) {rest : List Piece} {allowance budget : ℝ}
      (row : pairAllowance hasC (smallPieceClass (size left)) (smallPieceClass (size right)) =
        some allowance) (relation : ObeysRelation (size left) (size right))
      (tail : DiscountPlan hasC size rest budget) :
      DiscountPlan hasC size (left :: right :: rest) (allowance + budget)
  | perm {items other : List Piece} {budget : ℝ} (perm : items.Perm other)
      (plan : DiscountPlan hasC size items budget) : DiscountPlan hasC size other budget

private theorem plan_of_three_with_two_B {Piece : Type*} (hasC : Bool) (size : Piece → ℝ)
    (b₁ b₂ x : Piece) (b₁Class : smallPieceClass (size b₁) = .B)
    (b₂Class : smallPieceClass (size b₂) = .B)
    (thirdClass : smallPieceClass (size x) = .D ∨ hasC = false ∧ smallPieceClass (size x) = .C)
    (b₂Bounds : 1 / 3 < size b₂ ∧ size b₂ ≤ 1 / 2) (horder : size b₂ ≤ size b₁)
    (fits : size b₁ + size b₂ + size x ≤ 1) :
    ∃ budget ≤ 11 / 9, DiscountPlan hasC size [b₁, b₂, x] budget := by
  have relation := relation_of_two_B (size b₁) (size b₂) (size x) b₂Bounds horder fits
  have reorder : [b₂, x, b₁].Perm [b₁, b₂, x] := List.perm_middle (l₁ := [b₂, x]) (l₂ := [])
  rcases thirdClass with hD | ⟨rfl, hC⟩
  · cases hasC
    · refine ⟨_, ?_, .perm reorder (.pair b₂ x (allowance := 47 / 72) ?_ relation (.singletons [b₁]))⟩
      · norm_num [Function.comp_apply, singletonAllowance, b₁Class]
      · simp [b₂Class, hD, pairAllowance]
    · refine ⟨_, ?_, .perm reorder (.pair b₂ x (allowance := 23 / 36) ?_ relation (.singletons [b₁]))⟩
      · norm_num [Function.comp_apply, singletonAllowance, b₁Class]
      · simp [b₂Class, hD, pairAllowance]
  · refine ⟨_, ?_, .perm reorder (.pair b₂ x (allowance := 47 / 72) ?_ relation (.singletons [b₁]))⟩
    · norm_num [Function.comp_apply, singletonAllowance, b₁Class]
    · simp [b₂Class, hC, pairAllowance]

private theorem plan_of_BCDD {Piece : Type*} (hasC : Bool) (size : Piece → ℝ)
    (b c d₁ d₂ : Piece) (bClass : smallPieceClass (size b) = .B)
    (cClass : smallPieceClass (size c) = .C)
    (d₁Class : smallPieceClass (size d₁) = .D) (d₂Class : smallPieceClass (size d₂) = .D)
    (bBounds : 1 / 3 < size b ∧ size b ≤ 1 / 2) (cBounds : 1 / 4 < size c ∧ size c ≤ 1 / 3)
    (d₁Lower : 1 / 5 < size d₁) (d₂Lower : 1 / 5 < size d₂)
    (fit : size b + size c + size d₁ + size d₂ ≤ 1) :
    ∃ budget ≤ 11 / 9, DiscountPlan hasC size [b, c, d₁, d₂] budget := by
  have hBD := relation_B_of_other_C (size b) (size d₂) (size c) (size d₁)
    bBounds cBounds.1 (by linarith) (by linarith) (by linarith)
  have reorder : [b, d₂, c, d₁].Perm [b, c, d₁, d₂] :=
    .cons b (List.perm_middle (l₁ := [c, d₁]) (l₂ := [])).symm
  cases hasC
  · refine ⟨_, ?_, .perm reorder (.pair b d₂ (allowance := 47 / 72) ?_ hBD (.singletons [c, d₁]))⟩
    · norm_num [Function.comp_apply, singletonAllowance, cClass, d₁Class]
    · simp [pairAllowance, bClass, d₂Class]
  · have hCD := relation_C_of_other_B_and_D (size c) (size d₁) (size b) (size d₂)
      cBounds bBounds.1 d₁Lower d₂Lower (by linarith)
    refine ⟨_, ?_, .perm reorder (.pair b d₂ (allowance := 23 / 36) ?_ hBD
      (.pair c d₁ (allowance := 19 / 36) ?_ hCD (.singletons [])))⟩
    · norm_num
    · simp [pairAllowance, bClass, d₂Class]
    · simp [pairAllowance, cClass, d₁Class]

private theorem plan_of_BCXE {Piece : Type*} (hasC : Bool) (size : Piece → ℝ)
    (b c x e : Piece) (bClass : smallPieceClass (size b) = .B)
    (cClass : smallPieceClass (size c) = .C)
    (xClass : smallPieceClass (size x) = .D ∨ smallPieceClass (size x) = .E)
    (eClass : smallPieceClass (size e) = .E)
    (bBounds : 1 / 3 < size b ∧ size b ≤ 1 / 2) (cLower : 1 / 4 < size c)
    (xLower : 2 / 11 < size x) (eLower : 2 / 11 < size e)
    (fit : size b + size c + size x + size e ≤ 1) :
    ∃ budget ≤ 11 / 9, DiscountPlan hasC size [b, c, x, e] budget := by
  have relation := relation_B_of_other_C (size b) (size e) (size c) (size x)
    bBounds cLower eLower xLower (by linarith)
  have reorder : [b, e, c, x].Perm [b, c, x, e] :=
    .cons b (List.perm_middle (l₁ := [c, x]) (l₂ := [])).symm
  refine ⟨_, ?_, .perm reorder (.pair b e (allowance := 65 / 108) ?_ relation (.singletons [c, x]))⟩
  · rcases xClass with hD | hE <;> cases hasC <;>
      norm_num [Function.comp_apply, singletonAllowance, cClass, *]
  · cases hasC <;> simp [pairAllowance, bClass, eClass]

private theorem plan_of_BDDD {Piece : Type*} (hasC : Bool) (size : Piece → ℝ)
    (b d₁ d₂ d₃ : Piece) (bClass : smallPieceClass (size b) = .B)
    (d₁Class : smallPieceClass (size d₁) = .D) (d₂Class : smallPieceClass (size d₂) = .D)
    (d₃Class : smallPieceClass (size d₃) = .D)
    (bBounds : 1 / 3 < size b ∧ size b ≤ 1 / 2)
    (d₁Lower : 1 / 5 < size d₁) (d₂Lower : 1 / 5 < size d₂) (d₃Lower : 1 / 5 < size d₃)
    (fit : size b + size d₁ + size d₂ + size d₃ ≤ 1) :
    ∃ budget ≤ 11 / 9, DiscountPlan hasC size [b, d₁, d₂, d₃] budget := by
  have relation := relation_B_of_three_D (size b) (size d₁) (size d₂) (size d₃)
    bBounds d₁Lower d₂Lower d₃Lower fit
  cases hasC
  · refine ⟨_, ?_, .pair b d₁ (allowance := 47 / 72) ?_ relation (.singletons [d₂, d₃])⟩
    · norm_num [Function.comp_apply, singletonAllowance, d₂Class, d₃Class]
    · simp [pairAllowance, bClass, d₁Class]
  · refine ⟨_, ?_, .pair b d₁ (allowance := 23 / 36) ?_ relation (.singletons [d₂, d₃])⟩
    · norm_num [Function.comp_apply, singletonAllowance, d₂Class, d₃Class]
    · simp [pairAllowance, bClass, d₁Class]

private theorem plan_of_CCCE {Piece : Type*} (size : Piece → ℝ)
    (c₁ c₂ c₃ e : Piece) (c₁Class : smallPieceClass (size c₁) = .C)
    (c₂Class : smallPieceClass (size c₂) = .C) (c₃Class : smallPieceClass (size c₃) = .C)
    (eClass : smallPieceClass (size e) = .E)
    (c₃Bounds : 1 / 4 < size c₃ ∧ size c₃ ≤ 1 / 3)
    (order₁ : size c₃ ≤ size c₁) (order₂ : size c₃ ≤ size c₂)
    (fit : size c₁ + size c₂ + size c₃ + size e ≤ 1) :
    ∃ budget ≤ 11 / 9, DiscountPlan true size [c₁, c₂, c₃, e] budget := by
  have relation := relation_of_three_C (size c₁) (size c₂) (size c₃) (size e) c₃Bounds
    order₁ order₂ fit
  have reorder : [c₃, e, c₁, c₂].Perm [c₁, c₂, c₃, e] :=
    List.perm_append_comm (l₁ := [c₃, e]) (l₂ := [c₁, c₂])
  refine ⟨_, ?_, .perm reorder (.pair c₃ e (allowance := 89 / 180) ?_ relation (.singletons [c₁, c₂]))⟩
  · norm_num [Function.comp_apply, singletonAllowance, c₁Class, c₂Class]
  · simp [pairAllowance, c₃Class, eClass]

/-- Every feasible bin either has a budgeted singleton/pair partition or
matches one of the five refined cases. -/
theorem nonLarge_bin_configuration {Piece : Type*} (hasC : Bool)
    (size : Piece → ℝ) (items : List Piece)
    (sorted : items.Pairwise (fun a b => size b ≤ size a))
    (small : ∀ a ∈ items, 2 / 11 < size a ∧ size a ≤ 1 / 2) (fits : (items.map size).sum ≤ 1) :
    (∃ budget ≤ 11 / 9, DiscountPlan hasC size items budget) ∨
      (items.map (smallPieceClass ∘ size)) ∈ exceptionalConfigurations hasC := by
  rcases singleton_allowance_or_configuration hasC size items sorted small fits with singleton | shape
  · exact Or.inl ⟨_, by simpa only [List.map_map] using singleton, .singletons items⟩
  let classes := items.map (smallPieceClass ∘ size)
  have shapes :
      (classes = [B, B, D] ∨ hasC = false ∧ classes = [B, B, C]) ∨
      (classes = [B, C, D, E] ∨ classes = [B, C, E, E]) ∨
      classes = [B, C, D, D] ∨ classes = [B, D, D, D] ∨
      (hasC = true ∧ classes = [C, C, C, E]) ∨ classes ∈ exceptionalConfigurations hasC := by
    cases hasC <;>
      simp [classes, configurationsBeyondSingletons, exceptionalConfigurations] at shape ⊢ <;> tauto
  have bounds (a) (ha : a ∈ items) := smallPieceClass_bounds (small a ha).1 (small a ha).2
  rcases shapes with (shape | ⟨hcase, shape⟩) | (shape | shape) | shape | shape | ⟨caseI, ccce⟩ | hard
  · left
    simp only [classes, List.map_eq_cons_iff, List.map_eq_nil_iff, Function.comp_apply] at shape
    obtain ⟨b₁, _, rfl, hB₁, b₂, _, rfl, hB₂, d, _, rfl, hD, rfl⟩ := shape
    have b₂Bounds := bounds b₂ (by simp)
    rw [hB₂] at b₂Bounds
    exact plan_of_three_with_two_B hasC size b₁ b₂ d hB₁ hB₂ (.inl hD) b₂Bounds
      (List.rel_of_pairwise_cons sorted (by simp)) (by simpa [add_assoc] using fits)
  · left
    simp only [classes, List.map_eq_cons_iff, List.map_eq_nil_iff, Function.comp_apply] at shape
    obtain ⟨b₁, _, rfl, hB₁, b₂, _, rfl, hB₂, c, _, rfl, hC, rfl⟩ := shape
    have b₂Bounds := bounds b₂ (by simp)
    rw [hB₂] at b₂Bounds
    exact plan_of_three_with_two_B hasC size b₁ b₂ c hB₁ hB₂ (.inr ⟨hcase, hC⟩) b₂Bounds
      (List.rel_of_pairwise_cons sorted (by simp)) (by simpa [add_assoc] using fits)
  · left
    simp only [classes, List.map_eq_cons_iff, List.map_eq_nil_iff, Function.comp_apply] at shape
    obtain ⟨b, _, rfl, hB, c, _, rfl, hC, d, _, rfl, hD, e, _, rfl, hE, rfl⟩ := shape
    have bBounds := bounds b (by simp)
    have cBounds := bounds c (by simp)
    rw [hB] at bBounds
    rw [hC] at cBounds
    exact plan_of_BCXE hasC size b c d e hB hC (.inl hD) hE bBounds cBounds.1
      (small d (by simp)).1 (small e (by simp)).1 (by simpa [add_assoc] using fits)
  · left
    simp only [classes, List.map_eq_cons_iff, List.map_eq_nil_iff, Function.comp_apply] at shape
    obtain ⟨b, _, rfl, hB, c, _, rfl, hC, e₁, _, rfl, hE₁, e₂, _, rfl, hE₂, rfl⟩ := shape
    have bBounds := bounds b (by simp)
    have cBounds := bounds c (by simp)
    rw [hB] at bBounds
    rw [hC] at cBounds
    exact plan_of_BCXE hasC size b c e₁ e₂ hB hC (.inr hE₁) hE₂ bBounds cBounds.1
      (small e₁ (by simp)).1 (small e₂ (by simp)).1 (by simpa [add_assoc] using fits)
  · left
    simp only [classes, List.map_eq_cons_iff, List.map_eq_nil_iff, Function.comp_apply] at shape
    obtain ⟨b, _, rfl, hB, c, _, rfl, hC, d₁, _, rfl, hD₁, d₂, _, rfl, hD₂, rfl⟩ := shape
    have bBounds := bounds b (by simp)
    have cBounds := bounds c (by simp)
    have d₁Bounds := bounds d₁ (by simp)
    have d₂Bounds := bounds d₂ (by simp)
    rw [hB] at bBounds
    rw [hC] at cBounds
    rw [hD₁] at d₁Bounds
    rw [hD₂] at d₂Bounds
    exact plan_of_BCDD hasC size b c d₁ d₂ hB hC hD₁ hD₂ bBounds cBounds d₁Bounds.1
      d₂Bounds.1 (by simpa [add_assoc] using fits)
  · left
    simp only [classes, List.map_eq_cons_iff, List.map_eq_nil_iff, Function.comp_apply] at shape
    obtain ⟨b, _, rfl, hB, d₁, _, rfl, hD₁, d₂, _, rfl, hD₂, d₃, _, rfl, hD₃, rfl⟩ := shape
    have bBounds := bounds b (by simp)
    have d₁Bounds := bounds d₁ (by simp)
    have d₂Bounds := bounds d₂ (by simp)
    have d₃Bounds := bounds d₃ (by simp)
    rw [hB] at bBounds
    rw [hD₁] at d₁Bounds
    rw [hD₂] at d₂Bounds
    rw [hD₃] at d₃Bounds
    exact plan_of_BDDD hasC size b d₁ d₂ d₃ hB hD₁ hD₂ hD₃ bBounds d₁Bounds.1 d₂Bounds.1
      d₃Bounds.1 (by simpa [add_assoc] using fits)
  · left
    subst hasC
    change items.map (smallPieceClass ∘ size) = [C, C, C, E] at ccce
    simp only [List.map_eq_cons_iff, List.map_eq_nil_iff, Function.comp_apply] at ccce
    obtain ⟨c₁, _, rfl, hC₁, c₂, _, rfl, hC₂, c₃, _, rfl, hC₃, e, _, rfl, hE, rfl⟩ := ccce
    have c₃Bounds := bounds c₃ (by simp)
    rw [hC₃] at c₃Bounds
    exact plan_of_CCCE size c₁ c₂ c₃ e hC₁ hC₂ hC₃ hE c₃Bounds
      (List.rel_of_pairwise_cons sorted (by simp))
      (List.rel_of_pairwise_cons sorted.tail (by simp)) (by simpa [add_assoc] using fits)
  · exact Or.inr hard

end BinPacking.Decreasing

end

/- chains/PieceChains.lean -/
section

namespace BinPacking.Decreasing.PieceChains

universe u

variable {Piece : Type u} {points : Piece → Piece → Prop}

/-- An endpoint with no incoming arrow, as in Johnson's Claim 5.9.5. -/
def IsHead (points : Piece → Piece → Prop) (piece : Piece) : Prop :=
  ∀ previous, ¬ points previous piece

/-- An endpoint with no outgoing arrow. A piece can be both a head and a tail. -/
def IsTail (points : Piece → Piece → Prop) (piece : Piece) : Prop :=
  ∀ next, ¬ points piece next

/-- In a finite system with unique predecessors, following arrows from a head
must reach a tail. Reachability includes the isolated-piece case. -/
theorem exists_tail [Finite Piece]
    (uniquePrevious : ∀ ⦃a b c⦄, points a c → points b c → a = b)
    {head : Piece} (isHead : IsHead points head) :
    ∃ tail, IsTail points tail ∧ Relation.ReflTransGen points head tail := by
  by_contra neverTail
  have hasNext {piece : Piece} (reaches : Relation.ReflTransGen points head piece) :
      ∃ next, points piece next :=
    Classical.byContradiction fun noNext =>
      neverTail ⟨piece, fun next edge => noNext ⟨next, edge⟩, reaches⟩
  let states : ℕ → {piece : Piece // Relation.ReflTransGen points head piece} :=
    Nat.rec ⟨head, .refl⟩ fun _ state =>
      ⟨(hasNext state.property).choose, state.property.tail (hasNext state.property).choose_spec⟩
  have step (n : ℕ) : points (states n).val (states (n + 1)).val :=
    (hasNext (states n).property).choose_spec
  refine not_injective_infinite_finite (fun n => (states n).val) ?_
  intro m n same
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ n =>
          exact (isHead _ (Eq.mp (congrArg (points (states n).val) same.symm) (step n))).elim
  | succ m ih =>
      cases n with
      | zero =>
          exact (isHead _ (Eq.mp (congrArg (points (states m).val) same) (step m))).elim
      | succ n =>
          exact congrArg Nat.succ
            (ih (uniquePrevious (Eq.mp (congrArg (points (states m).val) same) (step m)) (step n)))

/-- A deterministic system has at most one reachable tail from any piece. -/
theorem tails_eq
    (uniqueNext : ∀ ⦃a b c⦄, points a b → points a c → b = c)
    {start a b : Piece} (tailA : IsTail points a) (tailB : IsTail points b)
    (pathA : Relation.ReflTransGen points start a) (pathB : Relation.ReflTransGen points start b) :
    a = b := by
  induction pathA using Relation.ReflTransGen.head_induction_on with
  | refl => exact ((Relation.reflTransGen_iff_eq tailA).mp pathB).symm
  | head arrow _ ih =>
      rcases pathB.cases_head with rfl | ⟨_, otherArrow, otherPath⟩
      · exact (tailB _ arrow).elim
      · exact ih ((uniqueNext otherArrow arrow) ▸ otherPath)

/-- Every head reaches exactly one tail. -/
theorem existsUnique_tail [Finite Piece]
    (uniqueNext : ∀ ⦃a b c⦄, points a b → points a c → b = c)
    (uniquePrevious : ∀ ⦃a b c⦄, points a c → points b c → a = b)
    {head : Piece} (isHead : IsHead points head) :
    ∃! tail, IsTail points tail ∧ Relation.ReflTransGen points head tail := by
  obtain ⟨tail, isTail, path⟩ := exists_tail uniquePrevious isHead
  exact ⟨tail, ⟨isTail, path⟩,
    fun _ other => tails_eq uniqueNext other.1 isTail other.2 path⟩

/-- A cycle of a deterministic relation cannot reach a tail. -/
theorem noCycle_of_reachesTail
    (uniqueNext : ∀ ⦃a b c⦄, points a b → points a c → b = c)
    {piece tail : Piece} (isTail : IsTail points tail)
    (path : Relation.ReflTransGen points piece tail) :
    ¬ Relation.TransGen points piece piece := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun loop =>
      (Relation.TransGen.head'_iff.mp loop).elim fun next nextStep => isTail next nextStep.1
  | head arrow _ ih =>
      rintro loop
      obtain ⟨_, first, remaining⟩ := Relation.TransGen.head'_iff.mp loop
      exact ih (Relation.TransGen.tail' ((uniqueNext first arrow) ▸ remaining) arrow)

/-- Every tail traces backwards to exactly one head. -/
theorem existsUnique_head [Finite Piece]
    (uniqueNext : ∀ ⦃a b c⦄, points a b → points a c → b = c)
    (uniquePrevious : ∀ ⦃a b c⦄, points a c → points b c → a = b)
    {tail : Piece} (isTail : IsTail points tail) :
    ∃! head, IsHead points head ∧ Relation.ReflTransGen points head tail := by
  obtain ⟨head, isHead, path⟩ := exists_tail (points := Function.swap points)
    (fun ⦃_ _ _⦄ arrow other => uniqueNext arrow other) isTail
  refine ⟨head, ⟨isHead, Relation.reflTransGen_swap.mp path⟩, ?_⟩
  exact fun _ other => tails_eq (points := Function.swap points)
    (fun ⦃_ _ _⦄ arrow another => uniquePrevious arrow another)
    other.1 isHead (Relation.reflTransGen_swap.mpr other.2) path

/-- Each deficit bin belongs to a unique owner outside the deficit bins, as in
Claim 5.9.10. Here `points` is the relation from owners and bins to deficit bins. -/
theorem existsUnique_owner (deficit : Piece → Prop)
    (uniquePrevious : ∀ ⦃a b c⦄, points a c → points b c → a = b)
    (pointsToDeficit : ∀ ⦃a b⦄, points a b → deficit b)
    (hasPrevious : ∀ b, deficit b → ∃ a, points a b)
    (noThreeDeficits : ∀ ⦃a b c⦄, deficit a → points a b → points b c → False)
    {target : Piece} (isDeficit : deficit target) :
    ∃! owner, ¬deficit owner ∧ Relation.ReflTransGen points owner target := by
  obtain ⟨previous, arrow⟩ := hasPrevious target isDeficit
  have existsOwner : ∃ owner, ¬deficit owner ∧ Relation.ReflTransGen points owner target := by
    by_cases previousDeficit : deficit previous
    · obtain ⟨initial, incoming⟩ := hasPrevious previous previousDeficit
      exact ⟨initial, fun initialDeficit => noThreeDeficits initialDeficit incoming arrow,
        (Relation.ReflTransGen.single incoming).tail arrow⟩
    · exact ⟨previous, previousDeficit, .single arrow⟩
  obtain ⟨owner, outside, path⟩ := existsOwner
  exact ⟨owner, ⟨outside, path⟩, fun _ other =>
    tails_eq (points := Function.swap points)
      (fun ⦃_ _ _⦄ edge another => uniquePrevious edge another)
      (fun _ edge => other.1 (pointsToDeficit edge))
      (fun _ edge => outside (pointsToDeficit edge))
      (Relation.reflTransGen_swap.mpr other.2) (Relation.reflTransGen_swap.mpr path)⟩

section Slots

variable {Bin : Type*}
variable (greedySlot optimalSlot : Piece → Bin × ℕ) (isABin : Bin → Prop)

/-- Match the greedy occupant of an A-bin's slot with its optimal occupant.
`Piece` contains the non-A piece occurrences. Slot indices start at zero. -/
def slotPoints (fromPiece toPiece : Piece) : Prop :=
  isABin (optimalSlot toPiece).1 ∧ greedySlot fromPiece = optimalSlot toPiece

theorem slotPoints_uniqueNext (optimalInjective : Function.Injective optimalSlot) :
    ∀ ⦃a b c⦄, slotPoints greedySlot optimalSlot isABin a b →
      slotPoints greedySlot optimalSlot isABin a c → b = c := by
  exact fun ⦃_ _ _⦄ first second => optimalInjective (first.2.symm.trans second.2)

theorem slotPoints_uniquePrevious (greedyInjective : Function.Injective greedySlot) :
    ∀ ⦃a b c⦄, slotPoints greedySlot optimalSlot isABin a c →
      slotPoints greedySlot optimalSlot isABin b c → a = b := by
  exact fun ⦃_ _ _⦄ first second => greedyInjective (first.2.trans second.2.symm)

/-- The optimal packing fills slot three of this A-bin, and the greedy packing leaves it empty. -/
def IsDeficit (bin : Bin) : Prop :=
  isABin bin ∧ (∃ piece, optimalSlot piece = (bin, 2)) ∧
    ∀ piece, greedySlot piece ≠ (bin, 2)

/-- Claim 5.9.5. Each head lies in a non-A bin of the optimal packing, or in
the third slot of an optimal A-bin whose third greedy slot is empty. -/
theorem slotPoints_head_iff {piece : Piece}
    (eligibleSlots : isABin (optimalSlot piece).1 →
      (optimalSlot piece).2 = 1 ∨ (optimalSlot piece).2 = 2)
    (secondCovered : isABin (optimalSlot piece).1 → (optimalSlot piece).2 = 1 →
      ∃ previous, greedySlot previous = optimalSlot piece) :
    IsHead (slotPoints greedySlot optimalSlot isABin) piece ↔
      ¬isABin (optimalSlot piece).1 ∨
        IsDeficit greedySlot optimalSlot isABin (optimalSlot piece).1 ∧
          (optimalSlot piece).2 = 2 := by
  constructor
  · intro head
    by_cases inside : isABin (optimalSlot piece).1
    · have unmatched : ∀ candidate, greedySlot candidate ≠ optimalSlot piece :=
        fun candidate same => head candidate ⟨inside, same⟩
      have third := (eligibleSlots inside).resolve_left fun second =>
        (secondCovered inside second).elim unmatched
      have position : optimalSlot piece = ((optimalSlot piece).1, 2) := Prod.ext rfl third
      exact Or.inr ⟨⟨inside, ⟨piece, position⟩,
        fun candidate same => unmatched candidate (same.trans position.symm)⟩, third⟩
    · exact Or.inl inside
  · rintro (outside | ⟨deficit, third⟩) previous ⟨inside, arrow⟩
    · exact outside inside
    · exact deficit.2.2 previous (arrow.trans (Prod.ext rfl third))

/-- A tail is outside the greedy A-bins or has no optimal counterpart at its greedy slot. -/
theorem slotPoints_tail_iff {piece : Piece} :
    IsTail (slotPoints greedySlot optimalSlot isABin) piece ↔
      ¬isABin (greedySlot piece).1 ∨ ∀ next, optimalSlot next ≠ greedySlot piece := by
  constructor
  · intro tail
    by_cases inside : isABin (greedySlot piece).1
    · exact Or.inr fun next same => tail next ⟨same.symm ▸ inside, same.symm⟩
    · exact Or.inl inside
  · rintro (outside | unmatched) next ⟨inside, same⟩
    · exact outside (same.symm ▸ inside)
    · exact unmatched next same.symm

/-- With every occupied greedy A-slot covered by the optimal packing,
the tails are exactly the pieces that first fit puts outside A-bins. -/
theorem slotPoints_tail_iff_nonA {piece : Piece}
    (cover : isABin (greedySlot piece).1 → ∃ next, optimalSlot next = greedySlot piece) :
    IsTail (slotPoints greedySlot optimalSlot isABin) piece ↔ ¬isABin (greedySlot piece).1 := by
  rw [slotPoints_tail_iff]
  exact ⟨fun tail inside => tail.elim (fun outside => outside inside)
    (fun unmatched => (cover inside).elim unmatched), Or.inl⟩

/-- Claim 5.9.6. Each piece in a greedy non-A bin terminates a unique chain. -/
theorem slotPoints_existsUnique_head_of_nonA [Finite Piece]
    (greedyInjective : Function.Injective greedySlot)
    (optimalInjective : Function.Injective optimalSlot)
    {piece : Piece} (outside : ¬isABin (greedySlot piece).1) :
    ∃! head, IsHead (slotPoints greedySlot optimalSlot isABin) head ∧
      Relation.ReflTransGen (slotPoints greedySlot optimalSlot isABin) head piece := by
  exact existsUnique_head
    (slotPoints_uniqueNext greedySlot optimalSlot isABin optimalInjective)
    (slotPoints_uniquePrevious greedySlot optimalSlot isABin greedyInjective)
    ((slotPoints_tail_iff greedySlot optimalSlot isABin).mpr (Or.inl outside))

end Slots

section SecondSlots

variable (greedySlot optimalSlot : Piece → ℕ × ℕ) (largeBins : ℕ)

/-- The arrows after the last third-slot optimal piece target only second slots. -/
def secondSlotPoints (fromPiece toPiece : Piece) : Prop :=
  slotPoints greedySlot optimalSlot (· < largeBins) fromPiece toPiece ∧
    (optimalSlot toPiece).2 = 1

local notation "secondArrow" => secondSlotPoints greedySlot optimalSlot largeBins

/-- A second-slot chain suffix ending outside the greedy A-bins has its greatest
rank at the end, as in Claim 5.9.7. The first-fit condition says that an earlier
piece whose optimal bin is at or before a given A-bin's second-slot occupant
must be placed strictly before that bin. -/
theorem rank_lt_of_secondSlotPath [Finite Piece] (rank : Piece → ℕ)
    (rankInjective : Function.Injective rank)
    (optimalInjective : Function.Injective optimalSlot)
    (firstFitBefore : ∀ ⦃blocker piece⦄,
      (greedySlot blocker).2 = 1 → (greedySlot blocker).1 < largeBins →
      (optimalSlot piece).1 ≤ (greedySlot blocker).1 → rank piece < rank blocker →
      (greedySlot piece).1 < (greedySlot blocker).1)
    {first terminal : Piece} (outside : largeBins ≤ (greedySlot terminal).1)
    (suffix : Relation.TransGen secondArrow first terminal) : rank first < rank terminal := by
  classical
  let : Fintype Piece := Fintype.ofFinite Piece
  let between := (Finset.univ : Finset Piece).filter fun piece =>
    Relation.ReflTransGen secondArrow first piece ∧
      Relation.ReflTransGen secondArrow piece terminal
  have memBetween (piece : Piece) : piece ∈ between ↔
      Relation.ReflTransGen secondArrow first piece ∧
        Relation.ReflTransGen secondArrow piece terminal := by simp [between]
  have firstMem : first ∈ between := (memBetween first).mpr ⟨.refl, suffix.to_reflTransGen⟩
  obtain ⟨blocker, inBetween, highest⟩ := Finset.exists_max_image between rank ⟨first, firstMem⟩
  have terminalTail : IsTail secondArrow terminal := fun _ arrow =>
    Nat.not_lt_of_ge outside (arrow.1.2.symm ▸ arrow.1.1)
  by_cases blockLast : blocker = terminal
  · exact lt_of_le_of_ne (blockLast ▸ highest first firstMem) fun sameRank =>
      (Relation.TransGen.head'_iff.mp suffix).elim fun next steps =>
        terminalTail next (rankInjective sameRank ▸ steps.1)
  · exfalso
    obtain ⟨next, arrow, toTerminal⟩ :=
      ((memBetween blocker).mp inBetween).2.cases_head.resolve_left blockLast
    have nextDeterministic : ∀ ⦃a b c⦄, secondArrow a b → secondArrow a c → b = c :=
      fun ⦃_ _ _⦄ firstArrow secondArrowProof =>
        slotPoints_uniqueNext greedySlot optimalSlot (· < largeBins) optimalInjective
          firstArrow.1 secondArrowProof.1
    have lower {piece : Piece} (fromNext : Relation.ReflTransGen secondArrow next piece)
        (finishes : Relation.ReflTransGen secondArrow piece terminal) : rank piece < rank blocker :=
      lt_of_le_of_ne (highest piece ((memBetween piece).mpr
        ⟨((memBetween blocker).mp inBetween).1.trans (fromNext.head arrow), finishes⟩))
        (fun equal => noCycle_of_reachesTail nextDeterministic terminalTail (toTerminal.head arrow)
          (Eq.mp (congrArg (Relation.TransGen secondArrow blocker) (rankInjective equal))
            (Relation.TransGen.head' arrow fromNext)))
    have forcedLeft {piece : Piece} (binAtMost : (optimalSlot piece).1 ≤ (greedySlot blocker).1)
        (earlier : rank piece < rank blocker) : (greedySlot piece).1 < (greedySlot blocker).1 :=
      firstFitBefore (arrow.1.2.symm ▸ arrow.2) (arrow.1.2.symm ▸ arrow.1.1) binAtMost earlier
    have remains {piece : Piece} (path : Relation.ReflTransGen secondArrow next piece)
        (finishes : Relation.ReflTransGen secondArrow piece terminal) :
        (optimalSlot piece).1 ≤ (greedySlot blocker).1 := by
      induction path with
      | refl => exact (congrArg Prod.fst arrow.1.2).ge
      | tail before step ih =>
          let previousFinishes := finishes.head step
          exact step.1.2 ▸ (forcedLeft (ih previousFinishes) (lower before previousFinishes)).le
    exact Nat.not_lt_of_ge outside (lt_trans
      (forcedLeft (remains toTerminal .refl) (lower toTerminal .refl))
      (arrow.1.2.symm ▸ arrow.1.1))

end SecondSlots

end BinPacking.Decreasing.PieceChains

end

/- chains/ChainCredit.lean -/
section

namespace BinPacking.Decreasing.PieceChains

variable {Piece Bin Owner : Type*}

/-- The baseline part of `g₁` on A-bins. -/
noncomputable def anchorCredit (isDeficit hasB : Bin → Prop) (bin : Bin) : ℝ := by
  classical
  exact if isDeficit bin then 0 else if hasB bin then 1 else 1 / 3

noncomputable def deficitChargeBins (aBins : Finset Bin) (isDeficit : Bin → Prop) : Finset Bin := by
  classical
  exact aBins.filter isDeficit

noncomputable def thirdChargeBins (aBins : Finset Bin) (isDeficit hasB : Bin → Prop) : Finset Bin := by
  classical
  exact aBins.filter fun bin => ¬isDeficit bin ∧ ¬hasB bin

/-- A deficit bin reserves one unit for its terminating head. A non-deficit bin with
a third slot reserves two thirds once its baseline is one third. -/
theorem anchor_credit_account (aBins : Finset Bin) (isDeficit hasB : Bin → Prop) :
    (∑ bin ∈ aBins, anchorCredit isDeficit hasB bin) + (deficitChargeBins aBins isDeficit).card +
      (2 / 3 : ℝ) * (thirdChargeBins aBins isDeficit hasB).card = aBins.card := by
  classical
  have onePerBin (bin : Bin) : anchorCredit isDeficit hasB bin +
      (if isDeficit bin then 1 else 0) +
      (if ¬isDeficit bin ∧ ¬hasB bin then 2 / 3 else 0) = 1 := by
    by_cases hd : isDeficit bin <;> by_cases hb : hasB bin <;>
      norm_num [anchorCredit, hd, hb]
  have account := Finset.sum_congr (s₁ := aBins) rfl (fun bin _ => onePerBin bin)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter,
    ← Finset.sum_filter] at account
  simpa [deficitChargeBins, thirdChargeBins, Finset.sum_const, nsmul_eq_mul, mul_comm] using account

noncomputable def routedCredit {Charge : Type*} [Fintype Charge]
    (route : Charge → Owner) (credit : Charge → ℝ) (owner : Owner) : ℝ := by
  classical
  exact ∑ charge ∈ Finset.univ with route charge = owner, credit charge

theorem sum_routedCredit {Charge : Type*} [Fintype Charge] [Fintype Owner]
    (route : Charge → Owner) (credit : Charge → ℝ) :
    ∑ owner, routedCredit route credit owner = ∑ charge, credit charge := by
  classical
  exact Finset.sum_fiberwise Finset.univ route credit

/-- Johnson's `g₁`, with one additional unit for each terminating deficit head. -/
noncomputable def firstCredit {aBins : Finset Bin} {indirect : Finset Piece}
    (isDeficit hasB : Bin → Prop) (anchorOwner : ↥aBins → Owner)
    (indirectOwner : ↥indirect → Owner) (owner : Owner) : ℝ :=
  routedCredit anchorOwner (fun bin => anchorCredit isDeficit hasB bin.val) owner +
    routedCredit indirectOwner (fun _ => 1) owner

/-- Johnson's `g₂`, charged once per terminating chain that touches a third slot away from its head. -/
noncomputable def secondCredit {chargedChains : Finset Piece}
    (chainOwner : ↥chargedChains → Owner) (owner : Owner) : ℝ :=
  routedCredit chainOwner (fun _ => 2 / 3) owner

section Slots

variable (greedySlot optimalSlot : Piece → Bin × ℕ) (aBins : Finset Bin)

local notation "points" => slotPoints greedySlot optimalSlot (· ∈ aBins)
local notation "deficit" => IsDeficit greedySlot optimalSlot (· ∈ aBins)

/-- Two terminating chains that touch the same optimal third slot end at the same item. -/
theorem tails_eq_of_same_optimal_third
    (optimalInjective : Function.Injective optimalSlot) {witness otherWitness terminal other : Piece}
    (sameBin : (optimalSlot witness).1 = (optimalSlot otherWitness).1)
    (third : (optimalSlot witness).2 = 2) (otherThird : (optimalSlot otherWitness).2 = 2)
    (path : Relation.ReflTransGen points witness terminal)
    (otherPath : Relation.ReflTransGen points otherWitness other)
    (isTail : IsTail points terminal) (otherTail : IsTail points other) : terminal = other := by
  have same : witness = otherWitness := optimalInjective (Prod.ext sameBin (third.trans otherThird.symm))
  exact tails_eq (slotPoints_uniqueNext greedySlot optimalSlot (· ∈ aBins) optimalInjective)
    isTail otherTail path (same.symm ▸ otherPath)

/-- A third optimal slot reached away from a chain's head also occurs in the greedy run. -/
theorem reached_optimal_third_nondeficit {head witness : Piece}
    (third : (optimalSlot witness).2 = 2) (reached : Relation.TransGen points head witness) :
    (optimalSlot witness).1 ∈ aBins ∧ ¬deficit (optimalSlot witness).1 := by
  obtain ⟨earlier, _, arrow⟩ := Relation.TransGen.tail'_iff.mp reached
  exact ⟨arrow.1, fun short => short.2.2 earlier (arrow.2.trans (Prod.ext rfl third))⟩

/-- Charge at most one terminating chain to each allowed third slot. -/
theorem card_le_optimal_third_bins (optimalInjective : Function.Injective optimalSlot)
    (terminals : Finset Piece) (bins : Finset Bin)
    (tails : ∀ item ∈ terminals, IsTail points item)
    (thirdWitness : ∀ item ∈ terminals, ∃ witness, (optimalSlot witness).1 ∈ bins ∧
      (optimalSlot witness).2 = 2 ∧ Relation.ReflTransGen points witness item) :
    terminals.card ≤ bins.card := by
  classical
  let witness (item : ↥terminals) := (thirdWitness item.val item.property).choose
  let chargeTo (item : ↥terminals) : ↥bins :=
    ⟨(optimalSlot (witness item)).1, (thirdWitness item.val item.property).choose_spec.1⟩
  apply Finset.card_le_card_of_injective (f := chargeTo)
  intro item other sameCharge
  exact Subtype.ext (tails_eq_of_same_optimal_third greedySlot optimalSlot aBins optimalInjective
    (witness := witness item) (otherWitness := witness other) (congrArg Subtype.val sameCharge)
    (thirdWitness item.val item.property).choose_spec.2.1
    (thirdWitness other.val other.property).choose_spec.2.1
    (thirdWitness item.val item.property).choose_spec.2.2
    (thirdWitness other.val other.property).choose_spec.2.2
    (tails item.val item.property) (tails other.val other.property))

/-- Claim 5.9.13 before the charges are grouped by owner. -/
theorem slot_credit_total_le (optimalInjective : Function.Injective optimalSlot)
    (hasB : Bin → Prop) (indirect chargedChains : Finset Piece)
    (tails : ∀ item, item ∈ indirect ∨ item ∈ chargedChains → IsTail points item)
    (indirectWitness : ∀ item ∈ indirect, ∃ head, deficit (optimalSlot head).1 ∧
      (optimalSlot head).2 = 2 ∧ Relation.ReflTransGen points head item)
    (chainWitness : ∀ item ∈ chargedChains, ∃ head witness, (optimalSlot witness).2 = 2 ∧
      Relation.TransGen points head witness ∧ Relation.ReflTransGen points witness item)
    (noBWithThird : ∀ witness, (optimalSlot witness).1 ∈ aBins → (optimalSlot witness).2 = 2 →
      ¬hasB (optimalSlot witness).1) :
    (∑ bin ∈ aBins, anchorCredit deficit hasB bin) + indirect.card +
      (2 / 3 : ℝ) * chargedChains.card ≤ aBins.card := by
  classical
  have indirectBound : indirect.card ≤ (deficitChargeBins aBins deficit).card := by
    apply card_le_optimal_third_bins greedySlot optimalSlot aBins optimalInjective
      indirect (deficitChargeBins aBins deficit) (fun item member => tails item (.inl member))
    exact fun item member => (indirectWitness item member).elim fun head witness =>
      ⟨head, by simpa [deficitChargeBins] using And.intro witness.1.1 witness.1,
        witness.2.1, witness.2.2⟩
  have thirdBound : chargedChains.card ≤ (thirdChargeBins aBins deficit hasB).card := by
    apply card_le_optimal_third_bins greedySlot optimalSlot aBins optimalInjective
      chargedChains (thirdChargeBins aBins deficit hasB) (fun item member => tails item (.inr member))
    exact fun item member => (chainWitness item member).elim fun _ witnesses =>
      witnesses.elim fun witness path =>
        let facts := reached_optimal_third_nondeficit greedySlot optimalSlot aBins path.1 path.2.1
        ⟨witness, (by simpa [thirdChargeBins] using
          (And.intro facts.1 (And.intro facts.2 (noBWithThird witness facts.1 path.1)))),
          path.1, path.2.2⟩
  linarith [anchor_credit_account aBins deficit hasB,
    show (indirect.card : ℝ) ≤ (deficitChargeBins aBins deficit).card by exact_mod_cast indirectBound,
    show (chargedChains.card : ℝ) ≤ (thirdChargeBins aBins deficit hasB).card by exact_mod_cast thirdBound]

/-- Total credit remains bounded after routing charges to owners or to the owners' optimal bins. -/
theorem grouped_slot_credit_le [Fintype Owner] (optimalInjective : Function.Injective optimalSlot)
    (hasB : Bin → Prop) (indirect chargedChains : Finset Piece)
    (anchorOwner : ↥aBins → Owner) (indirectOwner : ↥indirect → Owner)
    (chainOwner : ↥chargedChains → Owner)
    (tails : ∀ item, item ∈ indirect ∨ item ∈ chargedChains → IsTail points item)
    (indirectWitness : ∀ item ∈ indirect, ∃ head, deficit (optimalSlot head).1 ∧
      (optimalSlot head).2 = 2 ∧ Relation.ReflTransGen points head item)
    (chainWitness : ∀ item ∈ chargedChains, ∃ head witness, (optimalSlot witness).2 = 2 ∧
      Relation.TransGen points head witness ∧ Relation.ReflTransGen points witness item)
    (noBWithThird : ∀ witness, (optimalSlot witness).1 ∈ aBins → (optimalSlot witness).2 = 2 →
      ¬hasB (optimalSlot witness).1) :
    (∑ owner, (firstCredit deficit hasB anchorOwner indirectOwner owner +
      secondCredit chainOwner owner)) ≤ (aBins.card : ℝ) := by
  simpa only [firstCredit, secondCredit, Finset.sum_add_distrib, sum_routedCredit,
    Finset.sum_coe_sort, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    nsmul_eq_mul, mul_one, mul_comm] using
    slot_credit_total_le greedySlot optimalSlot aBins optimalInjective hasB indirect chargedChains
      tails indirectWitness chainWitness noBWithThird

end Slots

end BinPacking.Decreasing.PieceChains

end

/- chains/ChainOwnership.lean -/
section

namespace BinPacking.Decreasing.PieceChains

universe u v w

variable {Piece : Type u} {Owner : Type v} {Deficit : Type w}

/-- The source of the incoming arrow into each deficit bin is either an owner or another deficit bin. -/
def deficitPoints (previous : Deficit → Owner ⊕ Deficit) (source : Owner ⊕ Deficit) :
    Owner ⊕ Deficit → Prop
  | .inl _ => False
  | .inr bin => previous bin = source

def IsDeficitNode : Owner ⊕ Deficit → Prop
  | .inl _ => False
  | .inr _ => True

/-- Johnson's Claim 5.9.9 excludes two successive predecessor links between deficit bins. -/
def NoThreeDeficits (previous : Deficit → Owner ⊕ Deficit) : Prop :=
  ∀ ⦃a b c⦄, previous b = .inr a → previous c = .inr b → False

/-- The deficit bin lies in the responsibility set of an ordinary piece or a non-deficit A-bin. -/
def ResponsibleFor (previous : Deficit → Owner ⊕ Deficit) (owner : Owner) (bin : Deficit) :
    Prop :=
  Relation.ReflTransGen (deficitPoints previous) (.inl owner) (.inr bin)

/-- Claim 5.9.10 for the predecessor description of deficit bins. -/
theorem existsUnique_responsible (previous : Deficit → Owner ⊕ Deficit)
    (noThree : NoThreeDeficits previous) (bin : Deficit) :
    ∃! owner, ResponsibleFor previous owner bin := by
  have uniquePrevious : ∀ ⦃a b c⦄, deficitPoints previous a c → deficitPoints previous b c →
      a = b := fun ⦃a _ c⦄ => match c with
    | .inl _ => fun impossible _ => impossible.elim
    | .inr d => fun left right => (show previous d = a from left).symm.trans right
  have targetDeficit : ∀ ⦃a b⦄, deficitPoints previous a b → IsDeficitNode b :=
    fun ⦃_ b⦄ => match b with
    | .inl _ => id
    | .inr _ => fun _ => trivial
  have hasPrevious : ∀ b, IsDeficitNode b → ∃ a, deficitPoints previous a b
    | .inl _, impossible => impossible.elim
    | .inr d, _ => ⟨previous d, rfl⟩
  have noThreeNodes : ∀ ⦃a b c⦄, IsDeficitNode a → deficitPoints previous a b →
      deficitPoints previous b c → False := fun ⦃a b c⦄ => match a, b, c with
    | .inl _, _, _ => fun impossible _ _ => impossible
    | .inr _, .inl _, _ => fun _ impossible _ => impossible
    | .inr _, .inr _, .inl _ => fun _ _ impossible => impossible
    | .inr _, .inr _, .inr _ => fun _ first second => noThree first second
  obtain ⟨node, ⟨outside, reached⟩, unique⟩ := existsUnique_owner
    (points := deficitPoints previous) IsDeficitNode uniquePrevious targetDeficit hasPrevious
    noThreeNodes (target := .inr bin) trivial
  cases node with
  | inl owner => exact ⟨owner, reached, fun other owns =>
      Sum.inl.inj (unique (.inl other) ⟨not_false, owns⟩)⟩
  | inr _ => exact (outside trivial).elim

variable {points : Piece → Piece → Prop}

/-- A head contributes directly when it has an ordinary owner, or indirectly to the owner of
its deficit bin. -/
def ownsHead (previous : Deficit → Owner ⊕ Deficit) (headClass : Owner ⊕ Deficit) (owner : Owner) :
    Prop :=
  match headClass with
  | .inl direct => owner = direct
  | .inr bin => ResponsibleFor previous owner bin

/-- A residual occurrence belongs to the owner of the head of its piece chain. -/
def OwnsResidual (points : Piece → Piece → Prop)
    (classify : {head // IsHead points head} → Owner ⊕ Deficit)
    (previous : Deficit → Owner ⊕ Deficit) (owner : Owner) (item : Piece) : Prop :=
  ∃ head : {head // IsHead points head}, Relation.ReflTransGen points head.val item ∧
    ownsHead previous (classify head) owner

/-- The direct and indirect responsibilities of Claim 5.9.12 assign each terminating occurrence
to a unique owner. -/
theorem existsUnique_residual_owner [Finite Piece]
    (uniqueNext : ∀ ⦃a b c⦄, points a b → points a c → b = c)
    (uniquePrevious : ∀ ⦃a b c⦄, points a c → points b c → a = b)
    (classify : {head // IsHead points head} → Owner ⊕ Deficit)
    (previous : Deficit → Owner ⊕ Deficit) (noThree : NoThreeDeficits previous)
    {item : Piece} (tail : IsTail points item) :
    ∃! owner, OwnsResidual points classify previous owner item := by
  obtain ⟨head, ⟨headIsHead, path⟩, headUnique⟩ := existsUnique_head uniqueNext uniquePrevious tail
  let root : {head // IsHead points head} := ⟨head, headIsHead⟩
  have uniqueOwner : ∃! owner, ownsHead previous (classify root) owner := by
    cases classify root with
    | inl direct => exact ⟨direct, rfl, fun _ same => same⟩
    | inr bin => exact existsUnique_responsible previous noThree bin
  obtain ⟨owner, owns, unique⟩ := uniqueOwner
  refine ⟨owner, ⟨root, path, owns⟩, ?_⟩
  rintro other ⟨otherHead, otherPath, otherOwns⟩
  have same : otherHead = root := Subtype.ext
    (headUnique otherHead.val ⟨otherHead.property, otherPath⟩)
  exact unique other (same ▸ otherOwns)

/-- Select the unique owner, keeping the original index of each residual item. -/
noncomputable def residualOwner [Finite Piece]
    (uniqueNext : ∀ ⦃a b c⦄, points a b → points a c → b = c)
    (uniquePrevious : ∀ ⦃a b c⦄, points a c → points b c → a = b)
    (classify : {head // IsHead points head} → Owner ⊕ Deficit)
    (previous : Deficit → Owner ⊕ Deficit) (noThree : NoThreeDeficits previous)
    {residual : Piece → Prop} (residualTail : ∀ ⦃item⦄, residual item → IsTail points item)
    (item : {item // residual item}) : Owner :=
  (existsUnique_residual_owner uniqueNext uniquePrevious classify previous noThree
    (residualTail item.property)).choose

theorem residualOwner_eq_iff [Finite Piece]
    (uniqueNext : ∀ ⦃a b c⦄, points a b → points a c → b = c)
    (uniquePrevious : ∀ ⦃a b c⦄, points a c → points b c → a = b)
    (classify : {head // IsHead points head} → Owner ⊕ Deficit)
    (previous : Deficit → Owner ⊕ Deficit) (noThree : NoThreeDeficits previous)
    {residual : Piece → Prop} (residualTail : ∀ ⦃item⦄, residual item → IsTail points item)
    (item : {item // residual item}) (owner : Owner) :
    residualOwner uniqueNext uniquePrevious classify previous noThree residualTail item = owner ↔
      OwnsResidual points classify previous owner item.val :=
  (existsUnique_residual_owner uniqueNext uniquePrevious classify previous noThree
    (residualTail item.property)).choose_eq_iff

/-- Keep the list of occurrences assigned to one owner. -/
def ownerGroup [DecidableEq Owner] (assign : Piece → Owner) (items : List Piece) (owner : Owner) :
    List Piece :=
  items.filter fun item => decide (assign item = owner)

theorem mem_ownerGroup_iff [DecidableEq Owner] (assign : Piece → Owner) {items : List Piece}
    {owner : Owner} {item : Piece} :
    item ∈ ownerGroup assign items owner ↔ item ∈ items ∧ assign item = owner := by
  simp [ownerGroup]

/-- Different owners have disjoint groups of occurrence indices. -/
theorem ownerGroups_disjoint [DecidableEq Owner] (assign : Piece → Owner) {items : List Piece}
    {owner other : Owner} (distinct : owner ≠ other) {item : Piece}
    (belongs : item ∈ ownerGroup assign items owner)
    (belongsOther : item ∈ ownerGroup assign items other) : False :=
  distinct (((mem_ownerGroup_iff assign).mp belongs).2.symm.trans
    ((mem_ownerGroup_iff assign).mp belongsOther).2)

/-- Enumerating each owner once and concatenating their groups preserves all occurrences. -/
theorem flatten_ownerGroups_perm [DecidableEq Owner] (assign : Piece → Owner)
    (owners : List Owner) (items : List Piece) (noRepeatedOwners : owners.Nodup)
    (covered : ∀ item ∈ items, assign item ∈ owners) :
    (owners.map (ownerGroup assign items)).flatten.Perm items := by
  induction owners generalizing items with
  | nil =>
      have empty : items = [] := List.eq_nil_iff_forall_not_mem.mpr
        (fun item belongs => List.not_mem_nil (covered item belongs))
      simp [empty]
  | cons owner others ih =>
      let remaining := items.filter fun item => !decide (assign item = owner)
      have remainingCovered : ∀ item ∈ remaining, assign item ∈ others := by
        intro item belongs
        obtain ⟨member, unmatched⟩ := List.mem_filter.mp belongs
        exact (List.mem_cons.mp (covered item member)).resolve_left (by simpa using unmatched)
      have sameGroup : ∀ other ∈ others,
          ownerGroup assign remaining other = ownerGroup assign items other := by
        intro other inOthers
        simp only [ownerGroup, remaining, List.filter_filter]
        apply List.filter_congr
        intro item _
        by_cases assigned : assign item = other
        · simp [assigned, show other ≠ owner from fun equal =>
            (List.nodup_cons.mp noRepeatedOwners).1 (equal ▸ inOthers)]
        · simp [assigned]
      rw [List.map_cons, List.flatten_cons, ← List.map_congr_left sameGroup]
      exact (List.Perm.append_left (ownerGroup assign items owner)
        (ih remaining (List.nodup_cons.mp noRepeatedOwners).2 remainingCovered)).trans
        (List.filter_append_perm (fun item => decide (assign item = owner)) items)

/-- Projecting grouped indices to sizes preserves the multiplicities of equal-size items. -/
theorem map_ownerGroups_perm {Value : Type*} [DecidableEq Owner] (assign : Piece → Owner)
    (owners : List Owner) (items : List Piece) (value : Piece → Value)
    (noRepeatedOwners : owners.Nodup) (covered : ∀ item ∈ items, assign item ∈ owners) :
    (owners.map (fun owner => (ownerGroup assign items owner).map value)).flatten.Perm
      (items.map value) := by
  simpa only [List.map_flatten, List.map_map, Function.comp_def] using
    (flatten_ownerGroups_perm assign owners items noRepeatedOwners covered).map value

/-- Group residual occurrences by the optimal bin of their owner. -/
theorem grouped_occurrences_by_bin_perm {Value : Type*} {n : ℕ} (assign : Piece → Fin n)
    (items : List Piece) (value : Piece → Value) :
    (items.map value).Perm
      (List.ofFn (fun bin => (ownerGroup assign items bin).map value)).flatten := by
  rw [List.ofFn_eq_map]
  exact (map_ownerGroups_perm assign (List.finRange n) items value (List.nodup_finRange n)
    (fun item _ => List.mem_finRange (assign item))).symm

end BinPacking.Decreasing.PieceChains

end

/- chains/SlotOwnership.lean -/
section

namespace BinPacking.Decreasing.PieceChains

variable {Piece Bin Owner : Type*}
variable (greedySlot optimalSlot : Piece → Bin × ℕ) (isABin : Bin → Prop)

abbrev DeficitBin := {bin : Bin // IsDeficit greedySlot optimalSlot isABin bin}

variable (ordinaryOwner : ∀ item, ¬isABin (optimalSlot item).1 → Owner)
variable (anchorOwner : ∀ bin, isABin bin → ¬IsDeficit greedySlot optimalSlot isABin bin → Owner)

/-- The optimal origin of a non-A piece is its own ordinary owner, the owner of a non-deficit
A-bin, or a deficit bin whose owner is found by following predecessor links. -/
noncomputable def slotOrigin (item : Piece) : Owner ⊕ DeficitBin greedySlot optimalSlot isABin := by
  classical
  exact if deficit : IsDeficit greedySlot optimalSlot isABin (optimalSlot item).1 then
    .inr ⟨(optimalSlot item).1, deficit⟩
  else if inside : isABin (optimalSlot item).1 then
    .inl (anchorOwner (optimalSlot item).1 inside deficit)
  else
    .inl (ordinaryOwner item inside)

theorem slotOrigin_eq_inr_iff (item : Piece) (bin : DeficitBin greedySlot optimalSlot isABin) :
    slotOrigin greedySlot optimalSlot isABin ordinaryOwner anchorOwner item = .inr bin ↔
      (optimalSlot item).1 = bin.val := by
  by_cases deficit : IsDeficit greedySlot optimalSlot isABin (optimalSlot item).1
  · rw [slotOrigin, dif_pos deficit]
    simp [Subtype.ext_iff]
  · have different : (optimalSlot item).1 ≠ bin.val := fun same =>
      deficit (same.symm ▸ bin.property)
    by_cases inside : isABin (optimalSlot item).1 <;> simp [slotOrigin, deficit, inside, different]

theorem slotOrigin_of_nonA (item : Piece) (outside : ¬isABin (optimalSlot item).1) :
    slotOrigin greedySlot optimalSlot isABin ordinaryOwner anchorOwner item =
      .inl (ordinaryOwner item outside) := by
  have noDeficit : ¬IsDeficit greedySlot optimalSlot isABin (optimalSlot item).1 :=
    fun deficit => outside deficit.1
  simp [slotOrigin, noDeficit, outside]

/-- For a chain head, only the direct and deficit cases are possible. -/
theorem slotOrigin_of_head (head : Piece) (isHead :
    IsHead (slotPoints greedySlot optimalSlot isABin) head)
    (eligible : isABin (optimalSlot head).1 → (optimalSlot head).2 = 1 ∨ (optimalSlot head).2 = 2)
    (secondCovered : isABin (optimalSlot head).1 → (optimalSlot head).2 = 1 →
      ∃ earlier, greedySlot earlier = optimalSlot head) :
    (∃ outside : ¬isABin (optimalSlot head).1,
      slotOrigin greedySlot optimalSlot isABin ordinaryOwner anchorOwner head =
        .inl (ordinaryOwner head outside)) ∨
    (∃ bin : DeficitBin greedySlot optimalSlot isABin,
      optimalSlot head = (bin.val, 2) ∧
        slotOrigin greedySlot optimalSlot isABin ordinaryOwner anchorOwner head = .inr bin) := by
  rcases (slotPoints_head_iff greedySlot optimalSlot isABin eligible secondCovered).mp isHead with
    outside | ⟨deficit, third⟩
  · exact Or.inl ⟨outside,
      slotOrigin_of_nonA greedySlot optimalSlot isABin ordinaryOwner anchorOwner head outside⟩
  · exact Or.inr ⟨⟨(optimalSlot head).1, deficit⟩, Prod.ext rfl third,
      (slotOrigin_eq_inr_iff greedySlot optimalSlot isABin ordinaryOwner anchorOwner head _).mpr rfl⟩

variable (secondOccupied : ∀ bin : DeficitBin greedySlot optimalSlot isABin,
  ∃ item, greedySlot item = (bin.val, 1))

/-- The incoming link to a deficit bin is carried by the item in its second greedy slot. -/
noncomputable def deficitIncoming (bin : DeficitBin greedySlot optimalSlot isABin) : Piece :=
  (secondOccupied bin).choose

theorem deficitIncoming_slot (bin : DeficitBin greedySlot optimalSlot isABin) :
    greedySlot (deficitIncoming greedySlot optimalSlot isABin secondOccupied bin) =
      (bin.val, 1) :=
  (secondOccupied bin).choose_spec

theorem deficitIncoming_eq (greedyInjective : Function.Injective greedySlot)
    (bin : DeficitBin greedySlot optimalSlot isABin) {item : Piece}
    (atSlot : greedySlot item = (bin.val, 1)) :
    deficitIncoming greedySlot optimalSlot isABin secondOccupied bin = item :=
  greedyInjective ((deficitIncoming_slot greedySlot optimalSlot isABin secondOccupied bin).trans
    atSlot.symm)

noncomputable def slotDeficitPrevious (bin : DeficitBin greedySlot optimalSlot isABin) :
    Owner ⊕ DeficitBin greedySlot optimalSlot isABin :=
  slotOrigin greedySlot optimalSlot isABin ordinaryOwner anchorOwner
    (deficitIncoming greedySlot optimalSlot isABin secondOccupied bin)

theorem slotDeficitPrevious_eq_inr_iff (target source : DeficitBin greedySlot optimalSlot isABin) :
    slotDeficitPrevious greedySlot optimalSlot isABin ordinaryOwner anchorOwner
        secondOccupied target = .inr source ↔
      (optimalSlot (deficitIncoming greedySlot optimalSlot isABin secondOccupied target)).1 =
        source.val :=
  slotOrigin_eq_inr_iff greedySlot optimalSlot isABin ordinaryOwner anchorOwner _ _

/-- Claim 5.9.9 follows from Claim 5.9.8 and the capacity obstruction to a B-piece
lying in an optimal deficit bin. -/
theorem slotDeficitPrevious_noThree (isB : Piece → Prop)
    (noBInDeficit : ∀ item, IsDeficit greedySlot optimalSlot isABin (optimalSlot item).1 → ¬isB item)
    (incomingB : ∀ (source target : DeficitBin greedySlot optimalSlot isABin) (link inner : Piece),
      greedySlot link = (target.val, 1) → (optimalSlot link).1 = source.val →
      greedySlot inner = (source.val, 1) → isB inner) :
    NoThreeDeficits (slotDeficitPrevious greedySlot optimalSlot isABin ordinaryOwner anchorOwner
      secondOccupied) := by
  intro first middle last firstLink secondLink
  let inner := deficitIncoming greedySlot optimalSlot isABin secondOccupied middle
  let link := deficitIncoming greedySlot optimalSlot isABin secondOccupied last
  have originInner : (optimalSlot inner).1 = first.val :=
    (slotDeficitPrevious_eq_inr_iff greedySlot optimalSlot isABin ordinaryOwner anchorOwner
      secondOccupied middle first).mp firstLink
  have originLink : (optimalSlot link).1 = middle.val :=
    (slotDeficitPrevious_eq_inr_iff greedySlot optimalSlot isABin ordinaryOwner anchorOwner
      secondOccupied last middle).mp secondLink
  exact noBInDeficit inner (originInner.symm ▸ first.property)
    (incomingB middle last link inner
      (deficitIncoming_slot greedySlot optimalSlot isABin secondOccupied last) originLink
      (deficitIncoming_slot greedySlot optimalSlot isABin secondOccupied middle))

/-- Every greedy non-A occurrence has a unique owner in the slot model. -/
theorem existsUnique_slot_residual_owner [Finite Piece]
    (greedyInjective : Function.Injective greedySlot) (optimalInjective : Function.Injective optimalSlot)
    (noThree : NoThreeDeficits (slotDeficitPrevious greedySlot optimalSlot isABin ordinaryOwner
      anchorOwner secondOccupied)) {item : Piece} (outside : ¬isABin (greedySlot item).1) :
    ∃! owner, OwnsResidual (slotPoints greedySlot optimalSlot isABin)
      (fun head => slotOrigin greedySlot optimalSlot isABin ordinaryOwner anchorOwner head.val)
      (slotDeficitPrevious greedySlot optimalSlot isABin ordinaryOwner anchorOwner secondOccupied)
      owner item :=
  existsUnique_residual_owner (slotPoints_uniqueNext greedySlot optimalSlot isABin optimalInjective)
    (slotPoints_uniquePrevious greedySlot optimalSlot isABin greedyInjective) _ _ noThree
    ((slotPoints_tail_iff greedySlot optimalSlot isABin).mpr (.inl outside))

end BinPacking.Decreasing.PieceChains

end

/- chains/DeficitCounting.lean -/
section

namespace BinPacking.Decreasing.PieceChains

variable {Piece Bin Owner Deficit : Type*}

/-- A responsibility path has at most two edges. -/
theorem responsible_iff_parent_or_grandparent (previous : Deficit → Owner ⊕ Deficit)
    (noThree : NoThreeDeficits previous) (owner : Owner) (bin : Deficit) :
    ResponsibleFor previous owner bin ↔ previous bin = .inl owner ∨
      ∃ middle, previous bin = .inr middle ∧ previous middle = .inl owner := by
  constructor
  · intro owned
    cases parent : previous bin with
    | inl root =>
      exact Or.inl (congrArg Sum.inl ((existsUnique_responsible previous noThree bin).unique
        (Relation.ReflTransGen.single (show deficitPoints previous (.inl root) (.inr bin) from parent))
        owned))
    | inr middle =>
      cases grandparent : previous middle with
      | inl root =>
        have reached : ResponsibleFor previous root bin :=
          (Relation.ReflTransGen.single (show deficitPoints previous (.inl root) (.inr middle) from
            grandparent)).tail parent
        exact Or.inr ⟨middle, rfl,
          grandparent.trans (congrArg Sum.inl ((existsUnique_responsible previous noThree bin).unique
            reached owned))⟩
      | inr _ => exact (noThree grandparent parent).elim
  · rintro (parent | ⟨middle, parent, grandparent⟩)
    · exact Relation.ReflTransGen.single parent
    · exact (Relation.ReflTransGen.single
        (show deficitPoints previous (.inl owner) (.inr middle) from grandparent)).tail parent

noncomputable def deficitChildren [Fintype Deficit] (previous : Deficit → Owner ⊕ Deficit)
    (source : Owner ⊕ Deficit) : Finset Deficit := by
  classical
  exact Finset.univ.filter fun bin => previous bin = source

theorem mem_deficitChildren [Fintype Deficit] (previous : Deficit → Owner ⊕ Deficit)
    (source : Owner ⊕ Deficit) (bin : Deficit) :
    bin ∈ deficitChildren previous source ↔ previous bin = source := by
  simp [deficitChildren]

noncomputable def ownedDeficits [Fintype Deficit] (previous : Deficit → Owner ⊕ Deficit)
    (owner : Owner) : Finset Deficit := by
  classical
  exact Finset.univ.filter fun bin => ResponsibleFor previous owner bin

theorem mem_ownedDeficits [Fintype Deficit] (previous : Deficit → Owner ⊕ Deficit)
    (owner : Owner) (bin : Deficit) :
    bin ∈ ownedDeficits previous owner ↔ ResponsibleFor previous owner bin := by
  simp [ownedDeficits]

/-- Claim 5.9.11 counts directly owned deficit bins and their children. -/
theorem card_ownedDeficits_le [Fintype Deficit] (previous : Deficit → Owner ⊕ Deficit)
    (noThree : NoThreeDeficits previous) (owner : Owner) (directCap branchCap : ℕ)
    (directBound : (deficitChildren previous (.inl owner)).card ≤ directCap)
    (branchBound : ∀ bin, previous bin = .inl owner →
      (deficitChildren previous (.inr bin)).card ≤ branchCap) :
    (ownedDeficits previous owner).card ≤ directCap * (branchCap + 1) := by
  classical
  let direct := deficitChildren previous (.inl owner)
  let children (bin : Deficit) := deficitChildren previous (.inr bin)
  have cover : ownedDeficits previous owner ⊆ direct ∪ direct.biUnion children := by
    intro bin member
    rcases (responsible_iff_parent_or_grandparent previous noThree owner bin).mp
      ((mem_ownedDeficits previous owner bin).mp member) with parent | ⟨middle, parent, grandparent⟩
    · exact Finset.mem_union_left _ ((mem_deficitChildren previous _ bin).mpr parent)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨middle, (mem_deficitChildren previous _ middle).mpr grandparent,
          (mem_deficitChildren previous _ bin).mpr parent⟩)
  calc
    (ownedDeficits previous owner).card ≤ (direct ∪ direct.biUnion children).card :=
      Finset.card_le_card cover
    _ ≤ direct.card + (direct.biUnion children).card := Finset.card_union_le _ _
    _ ≤ direct.card + direct.card * branchCap := by
      exact Nat.add_le_add_left (Finset.card_biUnion_le_card_mul direct children branchCap
        (fun bin member => branchBound bin ((mem_deficitChildren previous _ bin).mp member))) _
    _ ≤ directCap * (branchCap + 1) := by
      simpa [Nat.mul_add, Nat.add_comm] using Nat.mul_le_mul_right (branchCap + 1) directBound

section Slots

variable (greedySlot optimalSlot : Piece → Bin × ℕ) (isABin : Bin → Prop)

local notation "points" => slotPoints greedySlot optimalSlot isABin
local notation "DeficitIndex" => DeficitBin greedySlot optimalSlot isABin

/-- Each indirect terminal comes from a different third slot of an owned deficit bin. -/
theorem card_indirect_terminals_le_ownedDeficits [Fintype DeficitIndex]
    (optimalInjective : Function.Injective optimalSlot) (previous : DeficitIndex → Owner ⊕ DeficitIndex)
    (owner : Owner) (terminals : Finset Piece) (tails : ∀ item ∈ terminals, IsTail points item)
    (origin : ∀ item ∈ terminals, ∃ (head : Piece) (bin : DeficitIndex), optimalSlot head = (bin.val, 2) ∧
      ResponsibleFor previous owner bin ∧ Relation.ReflTransGen points head item) :
    terminals.card ≤ (ownedDeficits previous owner).card := by
  classical
  let head (t : ↥terminals) := (origin t.val t.property).choose
  let bin (t : ↥terminals) := (origin t.val t.property).choose_spec.choose
  have facts (t : ↥terminals) := (origin t.val t.property).choose_spec.choose_spec
  let route (t : ↥terminals) : ↥(ownedDeficits previous owner) :=
    ⟨bin t, (mem_ownedDeficits previous owner (bin t)).mpr (facts t).2.1⟩
  refine Finset.card_le_card_of_injective (f := route) (fun a b same => ?_)
  have sameBin : bin a = bin b := congrArg Subtype.val same
  have sameHead : head a = head b := optimalInjective
    ((facts a).1.trans ((congrArg (fun d : DeficitIndex => (d.val, 2)) sameBin).trans (facts b).1.symm))
  exact Subtype.ext (tails_eq (slotPoints_uniqueNext greedySlot optimalSlot isABin optimalInjective)
    (tails a.val a.property) (tails b.val b.property) (facts a).2.2
    (Eq.mpr (congrArg (fun h => Relation.ReflTransGen points h b.val) sameHead) (facts b).2.2))

end Slots

/-- A direct head accounts for at most one residual terminal. -/
theorem card_terminals_from_head_le_one {points : Piece → Piece → Prop}
    (uniqueNext : ∀ ⦃a b c⦄, points a b → points a c → b = c)
    (terminals : Finset Piece) (head : Piece)
    (tailFromHead : ∀ item ∈ terminals, IsTail points item ∧ Relation.ReflTransGen points head item) :
    terminals.card ≤ 1 := by
  classical
  exact Finset.card_le_one_iff.mpr fun left right => tails_eq uniqueNext
    (tailFromHead _ left).1 (tailFromHead _ right).1 (tailFromHead _ left).2 (tailFromHead _ right).2

end BinPacking.Decreasing.PieceChains

end

/- assembly/Counting.lean -/
section

namespace BinPacking.Decreasing

/-- Indices of items larger than one half. Repeated item sizes retain their own indices. -/
noncomputable def largeItems (L : List ℝ) : Finset (Fin L.length) :=
  Finset.univ.filter (fun i => (1 / 2 : ℝ) < L.get i)

/-- Bins that contain an item larger than one half. -/
noncomputable def binsWithLargeItems {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b) :
    Finset (Fin b) :=
  (largeItems L).image assign

/-- Each large item in a feasible packing occupies a distinct bin. -/
theorem injOn_largeItems {L : List ℝ} (hL : IsList L) {b : ℕ}
    (assign : Fin L.length → Fin b)
    (hfit : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), L.get i ≤ 1) :
    Set.InjOn assign (largeItems L : Set (Fin L.length)) := by
  intro i hi k hk heq
  by_contra hne
  have hsubset : ({i, k} : Finset (Fin L.length)) ⊆
      Finset.univ.filter (fun t => assign t = assign k) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · simpa using heq
    · simp [Finset.mem_singleton.mp ht]
  have hsum :=
    (Finset.sum_le_sum_of_subset_of_nonneg (f := L.get) hsubset
      (fun t _ _ => (hL _ (List.get_mem L t)).1.le)).trans (hfit (assign k))
  rw [Finset.sum_pair hne] at hsum
  simp only [Finset.mem_coe, largeItems, Finset.mem_filter, Finset.mem_univ, true_and] at hi hk
  linarith

theorem largeItems_card (L : List ℝ) :
    (largeItems L).card = (L.filter (fun x => decide ((1 / 2 : ℝ) < x))).length := by
  have huniv : (List.finRange L.length).toFinset = (Finset.univ : Finset (Fin L.length)) := by
    ext i
    simp
  rw [largeItems, ← huniv, List.filter_toFinset,
    List.toFinset_card_of_nodup ((List.nodup_finRange L.length).filter _)]
  simpa only [List.filter_map, List.length_map, Function.comp_def] using
    congrArg (fun xs : List ℝ => (xs.filter (fun x => decide ((1 / 2 : ℝ) < x))).length)
      (List.map_get_finRange L)

/-- A feasible assignment has one occupied bin for each item larger than one half. -/
theorem binsWithLargeItems_card {L : List ℝ} (hL : IsList L) {b : ℕ}
    (assign : Fin L.length → Fin b)
    (hfit : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), L.get i ≤ 1) :
    (binsWithLargeItems assign).card =
      (L.filter (fun x => decide ((1 / 2 : ℝ) < x))).length := by
  rw [binsWithLargeItems, Finset.card_image_of_injOn (injOn_largeItems hL assign hfit),
    largeItems_card]

/-- The contribution of bins with no large piece is the bin count minus the large-item count. -/
theorem sum_nonLarge_bins {L : List ℝ} (hL : IsList L) {b : ℕ}
    (assign : Fin L.length → Fin b)
    (hfit : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), L.get i ≤ 1) :
    (∑ j : Fin b, if j ∈ binsWithLargeItems assign then (0 : ℝ) else 1) =
      (b : ℝ) - (L.filter (fun x => decide ((1 / 2 : ℝ) < x))).length := by
  have hstep (j : Fin b) :
      (if j ∈ binsWithLargeItems assign then (0 : ℝ) else 1) =
        (if j ∈ (binsWithLargeItems assign)ᶜ then (1 : ℝ) else 0) := by
    by_cases h : j ∈ binsWithLargeItems assign <;> simp [h]
  simp only [hstep, Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_compl, Fintype.card_fin]
  rw [Nat.cast_sub (by simpa using Finset.card_le_univ (s := binsWithLargeItems assign)),
    binsWithLargeItems_card hL assign hfit]

end BinPacking.Decreasing

end

/- small-only/OptimalAssignment.lean -/
section

set_option autoImplicit false

namespace BinPacking.Decreasing

/-- Positions of items assigned to a bin, in their input order. -/
def assignmentPositions {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b) (j : Fin b) :
    List (Fin L.length) :=
  (List.finRange L.length).filter (fun i => decide (assign i = j))

/-- Contents of an assigned bin, with multiplicities inherited from the input positions. -/
def assignmentBin {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b) (j : Fin b) : List ℝ :=
  (assignmentPositions assign j).map L.get

/-- Regrouping the item positions into the fibres of an assignment gives a permutation. -/
theorem assignmentPositions_flatten_perm {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b) :
    ((List.finRange b).map (assignmentPositions assign)).flatten.Perm (List.finRange L.length) := by
  apply (List.perm_ext_iff_of_nodup ?_ (List.nodup_finRange _)).mpr
  · simp [List.mem_flatten, List.mem_map, assignmentPositions]
  · rw [List.nodup_flatten, List.pairwise_map]
    constructor
    · intro bin hbin
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hbin
      exact (List.nodup_finRange _).filter _
    · apply (List.nodup_finRange b).imp
      exact fun {_ _} hne => List.disjoint_left.mpr fun i hi hj =>
        hne ((of_decide_eq_true (List.mem_filter.mp hi).2).symm.trans
          (of_decide_eq_true (List.mem_filter.mp hj).2))

/-- Concatenating the assigned bins recovers the input up to permutation. -/
theorem assignmentBins_flatten_perm {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b) :
    ((List.finRange b).map (assignmentBin assign)).flatten.Perm L := by
  change ((List.finRange b).map (fun j => (assignmentPositions assign j).map L.get)).flatten.Perm L
  simpa [Function.comp_def] using (assignmentPositions_flatten_perm assign).map L.get

@[simp] theorem mem_assignmentPositions {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b)
    (j : Fin b) (i : Fin L.length) : i ∈ assignmentPositions assign j ↔ assign i = j := by
  simp [assignmentPositions]

theorem mem_assignmentBin {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b)
    (j : Fin b) (a : ℝ) : a ∈ assignmentBin assign j ↔ ∃ i, assign i = j ∧ L.get i = a := by
  simp [assignmentBin, List.mem_map]

theorem assignmentBin_sum {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b) (j : Fin b) :
    (assignmentBin assign j).sum = ∑ i ∈ Finset.univ.filter (fun i => assign i = j), L.get i := by
  rw [assignmentBin, assignmentPositions, ← List.sum_toFinset L.get ((List.nodup_finRange _).filter _)]
  congr 1
  ext i
  simp

/-- An optimal bin count is attained by a feasible assignment. -/
theorem exists_optimal_assignment {L : List ℝ} (hL : IsList L) :
    ∃ assign : Fin L.length → Fin (optBins L),
      ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), L.get i ≤ 1 := by
  apply Nat.sInf_mem (s := {b : ℕ | ∃ assign : Fin L.length → Fin b,
    ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), L.get i ≤ 1})
  refine ⟨L.length, id, fun j => ?_⟩
  have onlyThis : Finset.univ.filter (fun i : Fin L.length => id i = j) = {j} := by ext i; simp
  simpa only [onlyThis, Finset.sum_singleton] using (hL _ (List.get_mem L j)).2

theorem optBins_le_of_assignment {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b)
    (hfit : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), L.get i ≤ 1) :
    optBins L ≤ b := by
  exact Nat.sInf_le (s := {n : ℕ | ∃ f : Fin L.length → Fin n,
    ∀ j, ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i ≤ 1}) ⟨assign, hfit⟩

end BinPacking.Decreasing

end

/- small-only/OptimalRestriction.lean -/
section

set_option autoImplicit false

namespace BinPacking.Decreasing

/-- An item-preserving injection of positions restricts feasible packings. -/
theorem optBins_le_of_positionEmbedding {L M : List ℝ} (hM : IsList M)
    (e : Fin L.length ↪ Fin M.length) (hsize : ∀ i, M.get (e i) = L.get i) :
    optBins L ≤ optBins M := by
  obtain ⟨assign, hfit⟩ := exists_optimal_assignment hM
  apply optBins_le_of_assignment (L := L) (assign ∘ e)
  intro j
  calc
    _ = ∑ i ∈ (Finset.univ.filter (fun i => (assign ∘ e) i = j)).map e, M.get i := by
      simp only [Finset.sum_map, hsize]
    _ ≤ 1 := ?_
  refine (Finset.sum_le_sum_of_subset_of_nonneg ?_
    (fun i _ _ => (hM _ (List.get_mem M i)).1.le)).trans (hfit j)
  intro target htarget
  rcases Finset.mem_map.mp htarget with ⟨source, hsource, rfl⟩
  simpa [Function.comp_def] using hsource

/-- Deleting items from a valid input cannot increase the optimum bin count. -/
theorem optBins_le_of_sublist {L M : List ℝ} (hM : IsList M) (hsub : L.Sublist M) :
    optBins L ≤ optBins M := by
  obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
  exact optBins_le_of_positionEmbedding hM e.toEmbedding (fun i => (he i).symm)

theorem optBins_take_le {L : List ℝ} (hL : IsList L) (k : ℕ) :
    optBins (L.take k) ≤ optBins L := by
  exact optBins_le_of_sublist hL (List.take_sublist k L)

private theorem sorted_sortDesc (L : List ℝ) : (sortDesc L).Pairwise (fun a b => b ≤ a) := by
  simpa only [sortDesc, decide_eq_true_eq] using
    List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
      (fun a b c => by simpa using (fun (h₁ : b ≤ a) (h₂ : c ≤ b) => le_trans h₂ h₁))
      (fun a b => by simpa using le_total b a) L

private theorem sortDesc_eq_ofFn_sort (L : List ℝ) :
    sortDesc L = List.ofFn (L.get ∘ Tuple.sort (fun i => -L.get i)) := by
  apply List.Perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => le_antisymm h₂ h₁) (sorted_sortDesc L)
  · rw [List.pairwise_ofFn]
    exact fun _ _ hij => neg_le_neg_iff.mp (Tuple.monotone_sort (fun i => -L.get i) hij.le)
  · refine (show (sortDesc L).Perm L from List.mergeSort_perm _ _).trans ?_
    simpa using ((Tuple.sort (fun i => -L.get i)).ofFn_comp_perm L.get).symm

private theorem optBins_ofFn_perm {L : List ℝ} (hL : IsList L) (σ : Equiv.Perm (Fin L.length)) :
    optBins (List.ofFn (L.get ∘ σ)) = optBins L := by
  let S := List.ofFn (L.get ∘ σ)
  let e : Fin S.length ≃ Fin L.length := (finCongr List.length_ofFn).trans σ
  have hget (i : Fin S.length) : L.get (e i) = S.get i := by
    simp only [e, S, List.get_ofFn, Equiv.trans_apply, Function.comp_apply, finCongr_apply]
  have hperm : S.Perm L := by simpa [S] using σ.ofFn_comp_perm L.get
  refine le_antisymm (optBins_le_of_positionEmbedding hL e.toEmbedding hget) ?_
  apply optBins_le_of_positionEmbedding (fun a ha => hL a (hperm.mem_iff.mp ha)) e.symm.toEmbedding
  exact fun i => by
    simpa only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply] using (hget (e.symm i)).symm

/-- Sorting the input in decreasing order preserves its optimum bin count. -/
theorem optBins_sortDesc {L : List ℝ} (hL : IsList L) : optBins (sortDesc L) = optBins L := by
  simpa only [sortDesc_eq_ofFn_sort] using optBins_ofFn_perm hL (Tuple.sort (fun i => -L.get i))

/-- The optimum bin count depends on the multiset of valid input items. -/
theorem optBins_perm {L M : List ℝ} (hL : IsList L) (hperm : L.Perm M) : optBins L = optBins M := by
  have sortedPerm : (sortDesc L).Perm (sortDesc M) :=
    (List.mergeSort_perm _ _).trans (hperm.trans (List.mergeSort_perm _ _).symm)
  have sortedEq := sortedPerm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => le_antisymm h₂ h₁)
    (sorted_sortDesc L) (sorted_sortDesc M)
  calc
    optBins L = optBins (sortDesc L) := (optBins_sortDesc hL).symm
    _ = optBins (sortDesc M) := congrArg optBins sortedEq
    _ = optBins M := optBins_sortDesc (fun a ha => hL a (hperm.mem_iff.mpr ha))

end BinPacking.Decreasing

end

/- small-only/LastOpeningPrefix.lean -/
section

set_option autoImplicit false

namespace BinPacking.Decreasing

/-- An additional item either keeps the First Fit bin count or increases it by one. -/
theorem ff_append_singleton_count (L : List ℝ) (a : ℝ) :
    FF (L ++ [a]) = if ffChoice (run ffChoice L) a < FF L then FF L else FF L + 1 := by
  simp only [FF, run, List.foldl_append, List.foldl_cons, List.foldl_nil, placeAt]
  split <;> simp [*]

theorem ff_take_succ_count (L : List ℝ) (i : Fin L.length) :
    FF (L.take ((i : ℕ) + 1)) =
      if binOf ffChoice L i < FF (L.take i) then FF (L.take i) else FF (L.take i) + 1 := by
  rw [List.take_succ_eq_append_getElem i.isLt, ff_append_singleton_count]
  rfl

/-- First Fit cannot lose bins when more items are appended. -/
theorem ff_le_append (L R : List ℝ) : FF L ≤ FF (L ++ R) := by
  induction R using List.reverseRecOn with
  | nil => simp
  | append_singleton R a ih =>
    rw [← List.append_assoc, ff_append_singleton_count]
    split <;> omega

theorem ff_le_of_prefix {L M : List ℝ} (h : L <+: M) : FF L ≤ FF M := by
  obtain ⟨R, rfl⟩ := h
  exact ff_le_append L R

/-- Restricting a run to a prefix preserves the placements within that prefix. -/
theorem binOf_take_eq (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ) (k : ℕ)
    (i : Fin (L.take k).length) :
    binOf choose (L.take k) i = binOf choose L (i.castLE (List.length_take_le' k L)) := by
  simp [binOf, List.take_take, Nat.min_eq_left (i.isLt.le.trans (List.length_take_le k L))]

/-- The shortest prefix with the final First Fit count ends by opening a new bin. -/
theorem exists_last_opening_prefix (L : List ℝ) (hFF : 0 < FF L) :
    ∃ i : Fin L.length,
      FF (L.take ((i : ℕ) + 1)) = FF L ∧ binOf ffChoice L i = FF (L.take i) := by
  have hreach : ∃ k, FF (L.take k) = FF L := ⟨L.length, by simp⟩
  let k := Nat.find hreach
  have hcount : FF (L.take k) = FF L := Nat.find_spec hreach
  have hlength : k ≤ L.length := Nat.find_min' hreach (by simp)
  have hpos : 0 < k := by
    by_contra hz
    have zero : k = 0 := by omega
    have noBins : FF (L.take k) = 0 := by simp [zero, FF, run]
    omega
  let i : Fin L.length := ⟨k - 1, by omega⟩
  have hsucc : (i : ℕ) + 1 = k := by
    dsimp [i]
    omega
  have hafter : FF (L.take ((i : ℕ) + 1)) = FF L := by simpa only [hsucc] using hcount
  have hprevious : FF (L.take i) ≠ FF L :=
    Nat.find_min hreach (show (i : ℕ) < k by omega)
  refine ⟨i, hafter, ?_⟩
  have hle : binOf ffChoice L i ≤ FF (L.take i) := List.findIdx_le_length
  by_contra hnot
  exact hprevious (by
    simpa only [ff_take_succ_count L i, if_pos (lt_of_le_of_ne hle hnot)] using hafter)

/-- Trimming after the last opening preserves a violation of the desired First Fit bound. -/
theorem exists_violating_last_opening_prefix {L : List ℝ} (hL : IsList L)
    (hviol : (11 / 9 : ℝ) * (optBins L : ℝ) + 4 < (FF L : ℝ)) :
    ∃ i : Fin L.length,
      FF (L.take ((i : ℕ) + 1)) = FF L ∧
      binOf ffChoice L i = FF (L.take i) ∧
      (11 / 9 : ℝ) * (optBins (L.take ((i : ℕ) + 1)) : ℝ) + 4 <
        (FF (L.take ((i : ℕ) + 1)) : ℝ) := by
  have hFF : 0 < FF L := by
    exact_mod_cast (show (0 : ℝ) < (FF L : ℝ) by
      linarith only [hviol, Nat.cast_nonneg (α := ℝ) (optBins L)])
  obtain ⟨i, hcount, hopens⟩ := exists_last_opening_prefix L hFF
  refine ⟨i, hcount, hopens, ?_⟩
  have hopt : (optBins (L.take ((i : ℕ) + 1)) : ℝ) ≤ optBins L := by
    exact_mod_cast optBins_take_le hL ((i : ℕ) + 1)
  linarith only [hopt, hviol, congrArg (fun n : ℕ => (n : ℝ)) hcount]

/-- A violating input has a violating prefix whose own terminal placement opens a bin. -/
theorem exists_violating_prefix_ending_at_opening {L : List ℝ} (hL : IsList L)
    (hviol : (11 / 9 : ℝ) * (optBins L : ℝ) + 4 < (FF L : ℝ)) :
    ∃ P : List ℝ, P <+: L ∧ FF P = FF L ∧
      (11 / 9 : ℝ) * (optBins P : ℝ) + 4 < (FF P : ℝ) ∧
      ∃ j : Fin P.length, (j : ℕ) + 1 = P.length ∧ binOf ffChoice P j = FF (P.take j) := by
  obtain ⟨i, hcount, hopens, hshort⟩ := exists_violating_last_opening_prefix hL hviol
  let P := L.take ((i : ℕ) + 1)
  have hlen : P.length = (i : ℕ) + 1 := List.length_take_of_le (Nat.succ_le_of_lt i.isLt)
  let j : Fin P.length := ⟨i, by omega⟩
  refine ⟨P, List.take_prefix _ _, hcount, hshort, j, hlen.symm, ?_⟩
  rw [binOf_take_eq ffChoice L ((i : ℕ) + 1) j,
    show j.castLE (List.length_take_le' ((i : ℕ) + 1) L) = i from Fin.ext rfl]
  simpa [P, j, List.take_take, Nat.min_eq_left (Nat.le_succ (i : ℕ))] using hopens

end BinPacking.Decreasing

end

/- Residual.lean -/
section

namespace BinPacking.Decreasing

noncomputable def firstFitStep (bins : List (List ℝ)) (item : ℝ) : List (List ℝ) :=
  placeAt bins (ffChoice bins item) item

/-- First fit operates on the later bins only after rejecting all earlier bins. -/
theorem firstFitStep_append (early late : List (List ℝ)) (item : ℝ) :
    firstFitStep (early ++ late) item =
      if ffChoice early item < early.length then firstFitStep early item ++ late
      else early ++ firstFitStep late item := by
  by_cases fits : ffChoice early item < early.length <;>
    simp only [firstFitStep, ffChoice, List.findIdx_append] at fits ⊢ <;>
    simp only [fits, if_true, if_false, placeAt, List.length_append, List.mapIdx_append]
  · rw [if_pos (by omega)]
    congr 1
    apply List.ext_getElem?
    intro i
    simp [List.getElem?_mapIdx, show i + early.length ≠
      early.findIdx (fun B => decide (B.sum + item ≤ 1)) by omega]
  · split
    · rw [if_pos (show late.findIdx (fun B => decide (B.sum + item ≤ 1)) < late.length by omega)]
      simp only [Nat.add_right_cancel_iff]
      congr 1
      apply List.ext_getElem (by simp)
      intro i _ hi
      simp [show i ≠ late.findIdx (fun B => decide (B.sum + item ≤ 1)) + early.length by omega]
    · rw [if_neg (show ¬ late.findIdx (fun B => decide (B.sum + item ≤ 1)) < late.length by omega),
        List.append_assoc]

/-- The items that first fit sends past the initial segment of bins, in placement order. -/
noncomputable def laterItems : List ℝ → List (List ℝ) → List (List ℝ) → List ℝ
  | [], _, _ => []
  | x :: xs, early, late =>
      if ffChoice early x < early.length then laterItems xs (firstFitStep early x) late
      else x :: laterItems xs early (firstFitStep late x)

/-- The later bins can be reconstructed by running first fit on only the items sent to them. -/
theorem firstFitFold_append (L : List ℝ) (early late : List (List ℝ)) :
    ∃ finalEarly : List (List ℝ), finalEarly.length = early.length ∧
      L.foldl firstFitStep (early ++ late) =
        finalEarly ++ (laterItems L early late).foldl firstFitStep late := by
  induction L generalizing early late with
  | nil => exact ⟨early, rfl, rfl⟩
  | cons x xs ih =>
    rw [List.foldl_cons, firstFitStep_append, laterItems]
    by_cases fits : ffChoice early x < early.length <;>
      simp only [fits, if_true, if_false, List.foldl_cons]
    · simpa only [show (firstFitStep early x).length = early.length by
        simp [firstFitStep, placeAt, fits]] using ih (firstFitStep early x) late
    · exact ih early (firstFitStep late x)

theorem laterItems_sublist (L : List ℝ) (early late : List (List ℝ)) :
    (laterItems L early late).Sublist L := by
  induction L generalizing early late with
  | nil => exact .slnil
  | cons x xs ih =>
    by_cases fits : ffChoice early x < early.length <;>
      simp only [laterItems, fits, if_true, if_false]
    · exact (ih (firstFitStep early x) late).cons x
    · exact (ih early (firstFitStep late x)).cons_cons x

/-- Items larger than half a bin each open a separate bin. -/
theorem firstFitFold_large (L prior : List ℝ)
    (hL : ∀ a ∈ L, (1 / 2 : ℝ) < a) (hprior : ∀ a ∈ prior, (1 / 2 : ℝ) < a) :
    L.foldl firstFitStep (prior.map (fun a => [a])) = (prior ++ L).map (fun a => [a]) := by
  induction L generalizing prior with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons]
    have nofit : ffChoice (prior.map (fun a => [a])) x = (prior.map (fun a => [a])).length := by
      apply List.findIdx_eq_length.mpr
      intro bin hbin
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hbin
      simp [show ¬ y + x ≤ 1 by linarith [hprior y hy, hL x (by simp)]]
    rw [show firstFitStep (prior.map (fun a => [a])) x = (prior ++ [x]).map (fun a => [a]) by
      simp [firstFitStep, nofit, placeAt]]
    rw [ih (prior ++ [x]) (fun a ha => hL a (List.mem_cons_of_mem _ ha))]
    · simp [List.append_assoc]
    · exact fun a ha => (List.mem_append.mp ha).elim (hprior a)
        (fun ha => hL a (List.mem_cons.mpr (.inl (List.mem_singleton.mp ha))))

theorem sortDesc_sorted (L : List ℝ) : (sortDesc L).Pairwise (fun a b => b ≤ a) := by
  simpa [sortDesc] using List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; linarith)
    (fun a b => by simpa using le_total b a) L

private theorem sortDesc_eq_of_perm (L M : List ℝ) (h : L.Perm M)
    (sorted : M.Pairwise (fun a b => b ≤ a)) : sortDesc L = M := by
  exact ((List.mergeSort_perm _ _).trans h).eq_of_pairwise
    (fun _ _ _ _ h₁ h₂ => le_antisymm h₂ h₁) (sortDesc_sorted L) sorted

theorem sortDesc_eq_self_of_sorted {L : List ℝ} (sorted : L.Pairwise (fun a b => b ≤ a)) :
    sortDesc L = L :=
  sortDesc_eq_of_perm L L (List.Perm.refl L) sorted

/-- The large items form an initial segment of a decreasing input. -/
theorem split_large_of_sorted {L : List ℝ} (hsorted : L.Pairwise (fun a b => b ≤ a)) :
    L = (L.filter (fun a => decide ((1 / 2 : ℝ) < a))) ++
      (L.filter (fun a => !decide ((1 / 2 : ℝ) < a))) := by
  let isLarge : ℝ → Bool := fun a => decide ((1 / 2 : ℝ) < a)
  exact (List.filter_append_perm isLarge L).symm.eq_of_pairwise
    (fun _ _ _ _ h₁ h₂ => le_antisymm h₂ h₁) hsorted
    (List.pairwise_append.mpr ⟨hsorted.filter isLarge, hsorted.filter _, fun a ha b hb =>
      (show b ≤ (1 / 2 : ℝ) by simpa [isLarge] using (List.mem_filter.mp hb).2).trans
        (show (1 / 2 : ℝ) < a from of_decide_eq_true (List.mem_filter.mp ha).2).le⟩)

/-- The ordered items first fit puts into bins with no item larger than half a bin. -/
noncomputable def residualItems (L : List ℝ) : List ℝ :=
  let sorted := sortDesc L
  let large := sorted.filter (fun a => decide ((1 / 2 : ℝ) < a))
  let small := sorted.filter (fun a => !decide ((1 / 2 : ℝ) < a))
  laterItems small (large.map (fun a => [a])) []

/-- Removing the bins with an item over half a bin leaves a first-fit decreasing run. -/
theorem residual_firstFit (L : List ℝ) :
    (residualItems L).Sublist ((sortDesc L).filter (fun a => !decide ((1 / 2 : ℝ) < a))) ∧
    FFD L = (L.filter (fun a => decide ((1 / 2 : ℝ) < a))).length + FFD (residualItems L) := by
  let isLarge : ℝ → Bool := fun a => decide ((1 / 2 : ℝ) < a)
  let sorted := sortDesc L
  let large := sorted.filter isLarge
  let small := sorted.filter (fun a => !isLarge a)
  let early := large.map (fun a => [a])
  refine ⟨laterItems_sublist small early [], ?_⟩
  have hlarge : ∀ a ∈ large, (1 / 2 : ℝ) < a := fun a ha =>
    of_decide_eq_true (List.mem_filter.mp ha).2
  have hsorted : sorted.Pairwise (fun a b => b ≤ a) := sortDesc_sorted L
  have hsplit : sorted = large ++ small := split_large_of_sorted hsorted
  have hresSort : sortDesc (laterItems small early []) = laterItems small early [] :=
    sortDesc_eq_of_perm _ _ (List.Perm.refl _)
      ((hsorted.filter _).sublist (laterItems_sublist small early []))
  have hfoldLarge : large.foldl firstFitStep [] = early := by
    simpa [early] using firstFitFold_large large [] hlarge (by simp)
  have hlargeCount : early.length = (L.filter isLarge).length := by
    simpa only [early, List.length_map] using
      ((show sorted.Perm L from List.mergeSort_perm _ _).filter isLarge).length_eq
  change (sorted.foldl firstFitStep []).length = (L.filter isLarge).length +
    ((sortDesc (laterItems small early [])).foldl firstFitStep []).length
  rw [hsplit, List.foldl_append, hfoldLarge, hresSort, ← hlargeCount]
  obtain ⟨finalEarly, hlength, hpack⟩ := firstFitFold_append small early []
  simpa only [List.append_nil, List.length_append, hlength] using congrArg List.length hpack

end BinPacking.Decreasing

end

/- Counterexample.lean -/
section

namespace BinPacking.Decreasing

private theorem ff_le_length (L : List ℝ) : FF L ≤ L.length := by
  induction L using List.reverseRecOn with
  | nil => simp [FF, run]
  | append_singleton rest item ih =>
    rw [ff_append_singleton_count]
    split <;> simp <;> omega

/-- The remaining proof can take the counterexample in decreasing order and
end at the first opening of its last bin, beyond all large-item bins. -/
theorem exists_sorted_counterexample_ending_outside {L : List ℝ}
    (valid : IsList L) (threshold : ∀ a ∈ L, (2 / 11 : ℝ) < a)
    (violates : (11 / 9 : ℝ) * (optBins L : ℝ) + 4 < (FFD L : ℝ)) :
    ∃ S : List ℝ,
      S.Pairwise (fun a b => b ≤ a) ∧ IsList S ∧ (∀ a ∈ S, (2 / 11 : ℝ) < a) ∧
      ((11 / 9 : ℝ) * (optBins S : ℝ) + 4 < (FF S : ℝ)) ∧
      ∃ last : Fin S.length, last.val + 1 = S.length ∧
        let cutoff := (S.filter (fun a => decide ((1 / 2 : ℝ) < a))).length
        cutoff ≤ last.val ∧ cutoff ≤ binOf ffChoice S last := by
  have validSorted : IsList (sortDesc L) := fun a ha => valid a (List.mem_mergeSort.mp ha)
  have sortedViolation : (11 / 9 : ℝ) * (optBins (sortDesc L) : ℝ) + 4 <
      (FF (sortDesc L) : ℝ) := by
    rw [optBins_sortDesc valid]
    exact violates
  obtain ⟨S, pref, _, violation, last, terminal, opens⟩ :=
    exists_violating_prefix_ending_at_opening validSorted sortedViolation
  have original (a : ℝ) (ha : a ∈ S) : a ∈ L := List.mem_mergeSort.mp (pref.subset ha)
  have validS : IsList S := fun a ha => valid a (original a ha)
  refine ⟨S, (sortDesc_sorted L).sublist pref.sublist, validS, fun a ha => threshold a (original a ha),
    violation, last, terminal, ?_⟩
  let cutoff := (S.filter (fun a => decide ((1 / 2 : ℝ) < a))).length
  change cutoff ≤ last.val ∧ cutoff ≤ binOf ffChoice S last
  obtain ⟨assign, fits⟩ := exists_optimal_assignment validS
  have cutoffBound : cutoff ≤ optBins S := by
    rw [show cutoff = (binsWithLargeItems assign).card from (binsWithLargeItems_card validS assign fits).symm]
    simpa using Finset.card_le_univ (s := binsWithLargeItems assign)
  have counts : FF S = binOf ffChoice S last + 1 := by
    simpa only [terminal, List.take_length, opens, Nat.lt_irrefl, if_false] using ff_take_succ_count S last
  have castCounts : (FF S : ℝ) = (binOf ffChoice S last : ℝ) + 1 := by exact_mod_cast counts
  have optBound : optBins S ≤ binOf ffChoice S last := by
    exact_mod_cast (show (optBins S : ℝ) ≤ (binOf ffChoice S last : ℝ) by
      linarith [Nat.cast_nonneg (α := ℝ) (optBins S)])
  have outside := cutoffBound.trans optBound
  refine ⟨?_, outside⟩
  rw [opens] at outside
  exact outside.trans ((ff_le_length _).trans (List.length_take_le _ _))

end BinPacking.Decreasing

end

/- small-only/AssignmentCounting.lean -/
section

set_option autoImplicit false

namespace BinPacking.Decreasing

/-- The marked bins are exactly the ones whose contents contain a large item. -/
theorem mem_binsWithLargeItems_iff_assignmentBin {L : List ℝ} {b : ℕ}
    (assign : Fin L.length → Fin b) (j : Fin b) :
    j ∈ binsWithLargeItems assign ↔ ∃ a ∈ assignmentBin assign j, (1 / 2 : ℝ) < a := by
  simp only [binsWithLargeItems, Finset.mem_image, largeItems, Finset.mem_filter,
    Finset.mem_univ, true_and, mem_assignmentBin]
  exact ⟨fun ⟨i, hsize, hbin⟩ => ⟨L.get i, ⟨i, hbin, rfl⟩, hsize⟩,
    fun ⟨_, ⟨i, hbin, rfl⟩, hsize⟩ => ⟨i, hsize, hbin⟩⟩

/-- The number of unmarked bins is the total minus the number of large item positions. -/
theorem card_bins_without_largeItems {L : List ℝ} (hL : IsList L) {b : ℕ}
    (assign : Fin L.length → Fin b)
    (hfit : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), L.get i ≤ 1) :
    (binsWithLargeItems assign)ᶜ.card =
      b - (L.filter (fun x => decide ((1 / 2 : ℝ) < x))).length := by
  rw [Finset.card_compl, Fintype.card_fin, binsWithLargeItems_card hL assign hfit]

end BinPacking.Decreasing

end

/- small-only/OptimalSlots.lean -/
section

set_option autoImplicit false

namespace BinPacking.Decreasing

/-- A zero-based slot in a bin, using the order of positions in the input list. -/
def assignmentSlot {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b) (i : Fin L.length) : ℕ :=
  (assignmentPositions assign (assign i)).idxOf i

/-- The bin and slot of an item in an assignment with bins ordered by input position. -/
def optimalPosition {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b)
    (i : Fin L.length) : ℕ × ℕ :=
  ((assign i).val, assignmentSlot assign i)

theorem assignmentSlot_lt {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b)
    (i : Fin L.length) : assignmentSlot assign i < (assignmentPositions assign (assign i)).length := by
  exact List.idxOf_lt_length_of_mem ((mem_assignmentPositions assign _ i).mpr rfl)

theorem assignmentPositions_get_slot {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b)
    (i : Fin L.length) :
    (assignmentPositions assign (assign i))[assignmentSlot assign i]? = some i := by
  exact List.getElem?_idxOf ((mem_assignmentPositions assign _ i).mpr rfl)

theorem optimalPosition_injective {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b) :
    Function.Injective (optimalPosition assign) := by
  intro i k h
  have hbin : assign i = assign k := Fin.ext (congrArg Prod.fst h)
  have hslot : assignmentSlot assign i = assignmentSlot assign k := congrArg Prod.snd h
  simpa only [hbin, hslot, assignmentPositions_get_slot, Option.some.injEq]
    using (assignmentPositions_get_slot assign i).symm

theorem assignmentBin_get_slot {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b)
    (i : Fin L.length) :
    (assignmentBin assign (assign i))[assignmentSlot assign i]? = some (L.get i) := by
  simp only [assignmentBin, List.getElem?_map, assignmentPositions_get_slot, Option.map_some]

theorem assignmentBin_sublist {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b) (j : Fin b) :
    (assignmentBin assign j).Sublist L := by
  simpa only [assignmentBin, assignmentPositions, List.map_get_finRange] using
    (List.filter_sublist (p := fun i => decide (assign i = j)) (l := List.finRange L.length)).map L.get

theorem assignmentBin_sorted {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b) (j : Fin b)
    (hsort : L.Pairwise (fun a b => b ≤ a)) : (assignmentBin assign j).Pairwise (fun a b => b ≤ a) := by
  exact hsort.sublist (assignmentBin_sublist assign j)

end BinPacking.Decreasing

end

/- small-only/HeavyBinRelabeling.lean -/
section

set_option autoImplicit false

namespace BinPacking.Decreasing

private theorem sorted_split_large {L : List ℝ} (hsort : L.Pairwise (fun a b => b ≤ a)) :
    L = (L.filter (fun a => decide ((1 / 2 : ℝ) < a))) ++
      (L.filter (fun a => !decide ((1 / 2 : ℝ) < a))) := by
  let large : ℝ → Bool := fun a => decide ((1 / 2 : ℝ) < a)
  apply (List.filter_append_perm large L).symm.eq_of_pairwise
    (fun _ _ _ _ hab hba => le_antisymm hba hab) hsort
  exact List.pairwise_append.mpr ⟨hsort.filter large, hsort.filter _, fun a ha b hb =>
    (show b ≤ (1 / 2 : ℝ) by simpa [large] using (List.mem_filter.mp hb).2).trans
      (show (1 / 2 : ℝ) ≤ a from (of_decide_eq_true (List.mem_filter.mp ha).2).le)⟩

/-- In descending order, the large items occupy exactly the leading positions. -/
theorem largeItem_iff_lt_filter_length {L : List ℝ} (hsort : L.Pairwise (fun a b => b ≤ a))
    (i : Fin L.length) :
    (1 / 2 : ℝ) < L.get i ↔ (i : ℕ) < (L.filter (fun a => decide ((1 / 2 : ℝ) < a))).length := by
  let first := L.filter (fun a => decide ((1 / 2 : ℝ) < a))
  let rest := L.filter (fun a => !decide ((1 / 2 : ℝ) < a))
  have hsplit : L = first ++ rest := sorted_split_large hsort
  have hin : (i : ℕ) < (first ++ rest).length := hsplit ▸ i.isLt
  have hget : L.get i = (first ++ rest)[(i : ℕ)] :=
    List.get_eq_getElem.trans (getElem_congr hsplit rfl i.isLt)
  change (1 / 2 : ℝ) < L.get i ↔ (i : ℕ) < first.length
  rw [hget]
  by_cases h : (i : ℕ) < first.length
  · rw [List.getElem_append_left h]
    exact iff_of_true (of_decide_eq_true (List.mem_filter.mp (List.getElem_mem h)).2) h
  · rw [List.getElem_append_right (Nat.le_of_not_gt h)]
    refine iff_of_false ?_ h
    have hrest : (i : ℕ) - first.length < rest.length := by
      simp only [List.length_append] at hin
      omega
    simpa [rest] using (List.mem_filter.mp (List.getElem_mem hrest)).2

private theorem exists_perm_transport_embeddings {α β : Type*} [Finite β]
    (old desired : α ↪ β) : ∃ π : Equiv.Perm β, ∀ i, π (old i) = desired i := by
  classical
  let e : Set.range old ≃ Set.range desired :=
    (Equiv.ofInjective old old.injective).symm.trans (Equiv.ofInjective desired desired.injective)
  refine ⟨e.extendSubtype, fun i => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (old i) (Set.mem_range_self i)]
  simp [e]

/-- Relabel a feasible assignment so its bins containing large items come first, in item order. -/
theorem exists_perm_align_largeBins {L : List ℝ} (hL : IsList L)
    (hsort : L.Pairwise (fun a b => b ≤ a)) {b : ℕ} (assign : Fin L.length → Fin b)
    (hfit : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), L.get i ≤ 1) :
    ∃ π : Equiv.Perm (Fin b),
      ∀ i : Fin L.length, (1 / 2 : ℝ) < L.get i → (π (assign i) : ℕ) = (i : ℕ) := by
  let count := (L.filter (fun a => decide ((1 / 2 : ℝ) < a))).length
  have hlen : count ≤ L.length := List.length_filter_le _ _
  have hbins : count ≤ b := by
    simpa only [binsWithLargeItems_card hL assign hfit, Fintype.card_fin] using
      Finset.card_le_univ (s := binsWithLargeItems assign)
  let first : Fin count ↪ Fin L.length := Fin.castLEEmb hlen
  have hlarge (i : Fin count) : first i ∈ largeItems L := by
    simp only [largeItems, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (largeItem_iff_lt_filter_length hsort (first i)).mpr i.isLt
  let old : Fin count ↪ Fin b := ⟨fun i => assign (first i), fun i j hij =>
    first.injective (injOn_largeItems hL assign hfit (hlarge i) (hlarge j) hij)⟩
  obtain ⟨π, hπ⟩ := exists_perm_transport_embeddings old (Fin.castLEEmb hbins)
  refine ⟨π, fun i hi => ?_⟩
  let rank : Fin count := ⟨i, (largeItem_iff_lt_filter_length hsort i).mp hi⟩
  have same : first rank = i := Fin.ext rfl
  have label : (π (assign (first rank)) : ℕ) = (rank : ℕ) := congrArg Fin.val (hπ rank)
  simpa only [same, rank, Fin.val_mk] using label

theorem assignment_relabel_fits {L : List ℝ} {b : ℕ} (assign : Fin L.length → Fin b)
    (hfit : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), L.get i ≤ 1)
    (π : Equiv.Perm (Fin b)) :
    ∀ j, ∑ i ∈ Finset.univ.filter (fun i => (π ∘ assign) i = j), L.get i ≤ 1 := by
  intro j
  simpa only [Function.comp_apply, ← π.eq_symm_apply] using hfit (π.symm j)

/-- A sorted valid input admits a feasible optimal assignment with aligned large-item bins. -/
theorem exists_optimal_assignment_aligned {L : List ℝ} (hL : IsList L)
    (hsort : L.Pairwise (fun a b => b ≤ a)) :
    ∃ assign : Fin L.length → Fin (optBins L),
      (∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), L.get i ≤ 1) ∧
      (∀ i, (1 / 2 : ℝ) < L.get i → (assign i : ℕ) = (i : ℕ)) := by
  obtain ⟨assign, hfit⟩ := exists_optimal_assignment hL
  obtain ⟨π, hπ⟩ := exists_perm_align_largeBins hL hsort assign hfit
  exact ⟨π ∘ assign, assignment_relabel_fits assign hfit π, hπ⟩

theorem mem_aligned_binsWithLargeItems_iff_lt_count {L : List ℝ}
    (hsort : L.Pairwise (fun a b => b ≤ a)) {b : ℕ} (assign : Fin L.length → Fin b)
    (halign : ∀ i, (1 / 2 : ℝ) < L.get i → (assign i : ℕ) = (i : ℕ)) (j : Fin b) :
    j ∈ binsWithLargeItems assign ↔ (j : ℕ) <
      (L.filter (fun a => decide ((1 / 2 : ℝ) < a))).length := by
  simp only [binsWithLargeItems, Finset.mem_image, largeItems, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simpa only [halign i hi] using (largeItem_iff_lt_filter_length hsort i).mp hi
  · intro hj
    let i : Fin L.length := ⟨j, hj.trans_le (List.length_filter_le _ _)⟩
    have hi := (largeItem_iff_lt_filter_length hsort i).mpr hj
    exact ⟨i, hi, Fin.ext (halign i hi)⟩

/-- The large item in an assigned bin is its first item in descending input order. -/
theorem assignmentSlot_eq_zero_of_large {L : List ℝ} (hL : IsList L)
    (hsort : L.Pairwise (fun a b => b ≤ a)) {b : ℕ} (assign : Fin L.length → Fin b)
    (hfit : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), L.get i ≤ 1)
    (i : Fin L.length) (hi : (1 / 2 : ℝ) < L.get i) : assignmentSlot assign i = 0 := by
  by_contra hnonzero
  have hpos : 0 < assignmentSlot assign i := Nat.pos_of_ne_zero hnonzero
  have hslot := assignmentSlot_lt assign i
  have hzero := hpos.trans hslot
  let k := (assignmentPositions assign (assign i))[0]
  have hordered : (assignmentPositions assign (assign i)).Pairwise (· < ·) :=
    (List.pairwise_lt_finRange L.length).filter _
  have hiSlot : (assignmentPositions assign (assign i))[assignmentSlot assign i] = i :=
    List.getElem_idxOf hslot
  have earlier : k < i := by
    simpa only [k, hiSlot] using List.pairwise_iff_getElem.mp hordered 0 _ hzero hslot hpos
  have hsize : L.get i ≤ L.get k := List.pairwise_iff_getElem.mp hsort _ _ k.isLt i.isLt earlier
  have sameBin : assign k = assign i :=
    (mem_assignmentPositions assign (assign i) k).mp (List.getElem_mem hzero)
  exact (ne_of_lt earlier) (injOn_largeItems hL assign hfit
    (by simpa [largeItems] using hi.trans_le hsize) (by simpa [largeItems] using hi) sameBin)

theorem aligned_optimalPosition_of_large {L : List ℝ} (hL : IsList L)
    (hsort : L.Pairwise (fun a b => b ≤ a)) {b : ℕ} (assign : Fin L.length → Fin b)
    (hfit : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), L.get i ≤ 1)
    (halign : ∀ i, (1 / 2 : ℝ) < L.get i → (assign i : ℕ) = (i : ℕ))
    (i : Fin L.length) (hi : (1 / 2 : ℝ) < L.get i) :
    optimalPosition assign i = (i.val, 0) := by
  exact Prod.ext (halign i hi) (assignmentSlot_eq_zero_of_large hL hsort assign hfit i hi)

end BinPacking.Decreasing

end

/- LargeBin.lean -/
section

namespace BinPacking.Decreasing

private theorem minimum_sum (bound : ℝ) (items : List ℝ) (h : ∀ x ∈ items, bound ≤ x) :
    bound * (items.length : ℝ) ≤ items.sum := by
  induction items with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, Nat.cast_succ, List.sum_cons]
    linarith [h x (by simp), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Johnson's Claim 5.9.2 applies to any feasible bin with a large item. -/
theorem large_bin_length_le_three (items : List ℝ) (hcap : items.sum ≤ 1)
    (hitems : ∀ x ∈ items, (2 / 11 : ℝ) < x)
    (hlarge : ∃ a ∈ items, (1 / 2 : ℝ) < a) : items.length ≤ 3 := by
  obtain ⟨a, ha, halarge⟩ := hlarge
  obtain ⟨prev, next, rfl⟩ := List.append_of_mem ha
  have hperm : (prev ++ a :: next).Perm (a :: (prev ++ next)) := List.perm_middle
  have hmin := minimum_sum (2 / 11) (prev ++ next) (fun x hx =>
    (hitems x (hperm.mem_iff.mpr (List.mem_cons_of_mem _ hx))).le)
  rw [hperm.sum_eq, List.sum_cons] at hcap
  rw [hperm.length_eq, List.length_cons]
  by_contra hmany
  linarith [show (3 : ℝ) ≤ ((prev ++ next).length : ℝ) by
    exact_mod_cast (show (3 : ℕ) ≤ (prev ++ next).length by omega)]

/-- A bin that rejects a later, smaller item has grown beyond any prefix that
could accommodate the larger candidate. This gives the extra-slot test for Claims 5.9.3 and 5.9.4. -/
theorem extra_slot_of_rejection (bins : List (List ℝ)) (index : ℕ) (fixed : List ℝ)
    (candidate last : ℝ) (hfit : fixed.sum + candidate ≤ 1) (hmin : last ≤ candidate)
    (hprefix : fixed <+: bins.getD index []) (hleft : index < ffChoice bins last) :
    fixed.length < (bins.getD index []).length := by
  have hindex : index < bins.length := hleft.trans_le (show ffChoice bins last ≤ bins.length from
    List.findIdx_le_length (p := fun bin : List ℝ => decide (bin.sum + last ≤ 1)))
  have rejected : 1 < (bins[index]'hindex).sum + last := by
    simpa using List.not_of_lt_findIdx (xs := bins)
      (p := fun bin : List ℝ => decide (bin.sum + last ≤ 1)) hleft
  have contents : bins.getD index [] = bins[index]'hindex := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hindex]
    rfl
  by_contra hshort
  have same := hprefix.eq_of_length_le (le_of_not_gt hshort)
  linarith [show 1 < fixed.sum + last by
    rw [same, contents]
    exact rejected]

end BinPacking.Decreasing

end

/- AlignedPacking.lean -/
section

namespace BinPacking.Decreasing

noncomputable section

/-- Large items from the decreasing input, in the same order. -/
def largePrefixItems (S : List ℝ) : List ℝ := S.filter (fun a => decide ((1 / 2 : ℝ) < a))

/-- On a counterexample trimmed to its terminal opening, the greedy and
optimal bins containing large items carry the same labels. -/
structure AlignedPacking (S : List ℝ) where
  valid : IsList S
  sorted : S.Pairwise (fun a b => b ≤ a)
  threshold : ∀ a ∈ S, (2 / 11 : ℝ) < a
  last : Fin S.length
  terminal : last.val + 1 = S.length
  lastAfter : (largePrefixItems S).length ≤ last.val
  lastOutside : (largePrefixItems S).length ≤ binOf ffChoice S last
  assign : Fin S.length → Fin (optBins S)
  fits : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), S.get i ≤ 1
  aligned : ∀ i, (1 / 2 : ℝ) < S.get i → (assign i).val = i.val

theorem exists_aligned_counterexample {L : List ℝ} (valid : IsList L)
    (threshold : ∀ a ∈ L, (2 / 11 : ℝ) < a)
    (violates : (11 / 9 : ℝ) * (optBins L : ℝ) + 4 < (FFD L : ℝ)) :
    ∃ S, Nonempty (AlignedPacking S) ∧ (11 / 9 : ℝ) * (optBins S : ℝ) + 4 < (FF S : ℝ) := by
  obtain ⟨S, sorted, validS, thresholdS, violation, last, terminal, lastAfter, lastOutside⟩ :=
    exists_sorted_counterexample_ending_outside valid threshold violates
  obtain ⟨assign, fits, aligned⟩ := exists_optimal_assignment_aligned validS sorted
  exact ⟨S, ⟨⟨validS, sorted, thresholdS, last, terminal, lastAfter, lastOutside,
    assign, fits, aligned⟩⟩, violation⟩

namespace AlignedPacking

variable {S : List ℝ} (p : AlignedPacking S)

include p in
theorem starts : largePrefixItems S <+: S :=
  ⟨S.filter (fun a => !decide ((1 / 2 : ℝ) < a)), (split_large_of_sorted p.sorted).symm⟩

theorem allLarge (items : List ℝ) : ∀ a ∈ largePrefixItems items, (1 / 2 : ℝ) < a :=
  fun _ ha => of_decide_eq_true (List.mem_filter.mp ha).2

def anchorIndex (j : Fin (largePrefixItems S).length) : Fin S.length :=
  ⟨j.val, j.isLt.trans_le (List.length_filter_le _ _)⟩

include p in
theorem anchor_index_size (j : Fin (largePrefixItems S).length) :
    S.get (anchorIndex j) = (largePrefixItems S).get j := by
  exact (p.starts.getElem j.isLt).symm

def anchorBin (j : Fin (largePrefixItems S).length) : Fin (optBins S) :=
  p.assign (anchorIndex j)

include p in
theorem anchor_index_large (j : Fin (largePrefixItems S).length) :
    (1 / 2 : ℝ) < S.get (anchorIndex j) := by
  rw [p.anchor_index_size j]
  exact allLarge S _ (List.get_mem _ j)

theorem anchor_bin_index (j : Fin (largePrefixItems S).length) : (p.anchorBin j).val = j.val :=
  p.aligned (anchorIndex j) (p.anchor_index_large j)

theorem assign_eq_anchor_bin (j : Fin (largePrefixItems S).length) (i : Fin S.length)
    (label : (p.assign i).val = j.val) : p.assign i = p.anchorBin j :=
  Fin.ext (label.trans (p.anchor_bin_index j).symm)

theorem optimal_anchor_slot (j : Fin (largePrefixItems S).length) :
    optimalPosition p.assign (anchorIndex j) = (j.val, 0) :=
  aligned_optimalPosition_of_large p.valid p.sorted p.assign p.fits p.aligned
    (anchorIndex j) (p.anchor_index_large j)

theorem optimal_large_bin_length_le_three (j : Fin (largePrefixItems S).length) :
    (assignmentBin p.assign (p.anchorBin j)).length ≤ 3 := by
  apply large_bin_length_le_three
  · rw [assignmentBin_sum]
    exact p.fits _
  · exact fun a ha => p.threshold a ((assignmentBin_sublist _ _).subset ha)
  · exact ⟨S.get (anchorIndex j), (mem_assignmentBin _ _ _).mpr ⟨anchorIndex j, rfl, rfl⟩,
      p.anchor_index_large j⟩

end AlignedPacking
end

end BinPacking.Decreasing

end

/- chains/FirstFitBefore.lean -/
section

namespace BinPacking.Decreasing.FirstFitHistory

/-- The contents of bin `b` immediately before placement at rank `t`. -/
noncomputable def contents (S : List ℝ) (t b : ℕ) : List ℝ :=
  (run ffChoice (S.take t)).getD b []

private theorem getD_inside {α : Type*} (xs : List α) (i : ℕ) (fallback : α)
    (inside : i < xs.length) : xs.getD i fallback = xs[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside]
  rfl

private theorem getD_outside {α : Type*} (xs : List α) (i : ℕ) (fallback : α)
    (outside : xs.length ≤ i) : xs.getD i fallback = fallback := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none outside]
  rfl

private theorem contents_placeAt {bins : List (List ℝ)} {chosen : ℕ} {item : ℝ}
    (atMost : chosen ≤ bins.length) (b : ℕ) :
    (placeAt bins chosen item).getD b [] =
      if b = chosen then bins.getD b [] ++ [item] else bins.getD b [] := by
  rcases lt_or_eq_of_le atMost with inside | rfl
  · simp only [placeAt, inside, if_true]
    rcases lt_or_ge b bins.length with inBins | outOfBins
    · rw [getD_inside _ _ _ (by simpa using inBins), getD_inside _ _ _ inBins, List.getElem_mapIdx]
    · rw [getD_outside _ _ _ (by simpa using outOfBins), getD_outside _ _ _ outOfBins]
      have ne : b ≠ chosen := by omega
      simp [ne]
  · simp only [placeAt, lt_irrefl, if_false]
    rcases lt_trichotomy b bins.length with before | atEnd | after
    · rw [getD_inside _ _ _ (by simp; omega), getD_inside _ _ _ before,
        List.getElem_append_left before]
      simp [Nat.ne_of_lt before]
    · subst b
      rw [getD_inside _ _ _ (by simp), getD_outside _ _ _ le_rfl]
      simp
    · rw [getD_outside _ _ _ (by simp; omega), getD_outside _ _ _ (by omega)]
      simp [Nat.ne_of_gt after]

private theorem contents_prefix_fold (items : List ℝ) (bins : List (List ℝ)) (j : ℕ) :
    bins.getD j [] <+: (items.foldl firstFitStep bins).getD j [] := by
  induction items generalizing bins with
  | nil => exact List.prefix_rfl
  | cons item items ih =>
      refine List.IsPrefix.trans ?_ (ih (firstFitStep bins item))
      rw [firstFitStep, contents_placeAt (show ffChoice bins item ≤ bins.length from
        List.findIdx_le_length (p := fun bin : List ℝ => decide (bin.sum + item ≤ 1))) j]
      split <;> simp

/-- Each bin grows by appending items, so earlier contents are a prefix of later contents. -/
theorem contents_prefix (S : List ℝ) {i j b : ℕ} (order : i ≤ j) :
    contents S i b <+: contents S j b := by
  obtain ⟨items, after⟩ := List.take_prefix_take_left (l := S) order
  change ((S.take i).foldl firstFitStep []).getD b [] <+:
    ((S.take j).foldl firstFitStep []).getD b []
  simpa only [← after, List.foldl_append] using
    contents_prefix_fold items ((S.take i).foldl firstFitStep []) b

theorem contents_succ (S : List ℝ) (i : Fin S.length) (b : ℕ) :
    contents S (i.val + 1) b =
      if b = binOf ffChoice S i then contents S i b ++ [S.get i] else contents S i b := by
  rw [contents, List.take_add_one, List.getElem?_eq_getElem i.isLt, Option.toList_some, run,
    List.foldl_append]
  exact contents_placeAt (List.findIdx_le_length (xs := run ffChoice (S.take i.val))
    (p := fun bin : List ℝ => decide (bin.sum + S.get i ≤ 1))) b

/-- A piece processed before an existing bin's second occupant is packed to the left
of that bin, provided it fits beside the bin's first item. -/
theorem binOf_lt_before_second {S : List ℝ} (i blocker : Fin S.length)
    (earlier : i.val < blocker.val) (second : slotOf ffChoice S blocker = 1)
    (anchor : ℝ) (anchorPresent :
      [anchor] <+: contents S i.val (binOf ffChoice S blocker))
    (fits : anchor + S.get i ≤ 1) : binOf ffChoice S i < binOf ffChoice S blocker := by
  let b := binOf ffChoice S blocker
  have singleton : contents S i.val b = [anchor] :=
    (anchorPresent.eq_of_length_le (show (contents S i.val b).length ≤ 1 from
      (contents_prefix S (b := b) (le_of_lt earlier)).length_le.trans (le_of_eq second))).symm
  have noSkip : binOf ffChoice S i ≤ b := by
    apply le_of_not_gt
    intro skipped
    have rejected := List.not_of_lt_findIdx (show b < (run ffChoice (S.take i.val)).findIdx
      (fun bin => decide (bin.sum + S.get i ≤ 1)) from skipped)
    have existsBin : b < (run ffChoice (S.take i.val)).length :=
      skipped.trans_le (List.findIdx_le_length (xs := run ffChoice (S.take i.val))
        (p := fun bin : List ℝ => decide (bin.sum + S.get i ≤ 1)))
    have atIndex : (run ffChoice (S.take i.val))[b] = [anchor] :=
      (getD_inside _ _ [] existsBin).symm.trans singleton
    simp [atIndex] at rejected
    exact (not_lt_of_ge fits) rejected
  refine lt_of_le_of_ne noSkip ?_
  intro same
  have tooMany : 2 ≤ 1 := calc
    2 = (contents S (i.val + 1) b).length := by
      rw [contents_succ, if_pos (show b = binOf ffChoice S i from same.symm), singleton]
      rfl
    _ ≤ (contents S blocker.val b).length :=
      (contents_prefix S (b := b) (Nat.succ_le_of_lt earlier)).length_le
    _ = 1 := second
  exact (by omega : ¬ (2 : ℕ) ≤ 1) tooMany

/-- Each large item occupies the first position in its own bin throughout the later run. -/
theorem large_anchor_prefix {large S : List ℝ} (startsWithLarge : large <+: S)
    (allLarge : ∀ item ∈ large, (1 / 2 : ℝ) < item)
    {i b : ℕ} (afterLarge : large.length ≤ i) (isABin : b < large.length) :
    [large[b]] <+: contents S i b := by
  obtain ⟨small, rfl⟩ := startsWithLarge
  have initial : run ffChoice large = large.map fun item => [item] :=
    show large.foldl firstFitStep [] = _ from
      by simpa using firstFitFold_large large [] allLarge (by simp)
  have initialContents : contents (large ++ small) large.length b = [large[b]] := by
    rw [contents, List.take_append_length, initial, getD_inside _ _ [] (by simpa using isABin)]
    exact List.getElem_map _
  exact initialContents ▸ contents_prefix (large ++ small) afterLarge

/-- The first-fit premise of Claim 5.9.7 for the published run model. The item
fits beside its optimal A-bin's large item, and the blocker is in a later A-bin. -/
theorem binOf_lt_before_second_of_largePrefix {large S : List ℝ}
    (startsWithLarge : large <+: S) (allLarge : ∀ item ∈ large, (1 / 2 : ℝ) < item)
    (decreasing : large.Pairwise (fun a b => b ≤ a)) (i blocker : Fin S.length)
    (afterLarge : large.length ≤ i.val) (earlier : i.val < blocker.val)
    (second : slotOf ffChoice S blocker = 1)
    (blockerABin : binOf ffChoice S blocker < large.length) (optimalBin : Fin large.length)
    (optimalEarlier : optimalBin.val ≤ binOf ffChoice S blocker)
    (fitsOptimal : large.get optimalBin + S.get i ≤ 1) :
    binOf ffChoice S i < binOf ffChoice S blocker := by
  apply binOf_lt_before_second i blocker earlier second large[binOf ffChoice S blocker]
    (large_anchor_prefix startsWithLarge allLarge afterLarge blockerABin)
  refine (add_le_add ?_ le_rfl).trans fitsOptimal
  rcases lt_or_eq_of_le optimalEarlier with before | same
  · exact (List.pairwise_iff_getElem.mp decreasing) _ _ optimalBin.isLt blockerABin before
  · simp [List.get_eq_getElem, same]

end BinPacking.Decreasing.FirstFitHistory

end

/- DeficitGeometry.lean -/
section

namespace BinPacking.Decreasing.FirstFitHistory

/-- The first two occupants of a large-item bin remain a prefix of its contents. -/
theorem large_second_prefix {large S : List ℝ} (starts : large <+: S)
    (hlarge : ∀ a ∈ large, (1 / 2 : ℝ) < a) (j : Fin large.length) (second : Fin S.length)
    (afterLarge : large.length ≤ second.val) (hbin : binOf ffChoice S second = j.val)
    (hslot : slotOf ffChoice S second = 1) {t : ℕ} (ht : second.val < t) :
    [large.get j, S.get second] <+: contents S t j.val := by
  have anchor : [large.get j] <+: contents S second.val j.val :=
    large_anchor_prefix starts hlarge afterLarge j.isLt
  have hlength : (contents S second.val j.val).length = 1 := by
    simpa only [slotOf, hbin, contents] using hslot
  have singleton : contents S second.val j.val = [large.get j] :=
    (anchor.eq_of_length_le (by simp [hlength])).symm
  have pair : contents S (second.val + 1) j.val = [large.get j, S.get second] := by
    rw [contents_succ, if_pos hbin.symm, singleton]
    rfl
  exact pair ▸ contents_prefix S (Nat.succ_le_of_lt ht)

/-- With the terminal item routed past the large bins, a large bin with only
two occupants could not also accommodate a candidate at least as large as that item. -/
theorem short_large_bin_rejects_third {large S : List ℝ} (starts : large <+: S)
    (hlarge : ∀ a ∈ large, (1 / 2 : ℝ) < a) (j : Fin large.length)
    (second last : Fin S.length) (afterLarge : large.length ≤ second.val)
    (hbin : binOf ffChoice S second = j.val) (hslot : slotOf ffChoice S second = 1)
    (terminal : last.val + 1 = S.length) (lastOutside : large.length ≤ binOf ffChoice S last)
    (hshort : (contents S S.length j.val).length ≤ 2) (candidate : ℝ)
    (hleast : S.get last ≤ candidate) : 1 < large.get j + S.get second + candidate := by
  have earlier : second.val < last.val := by
    by_contra hlate
    have same : second = last := Fin.ext (by omega)
    exact (Nat.not_lt_of_ge lastOutside) (same ▸ (hbin.symm ▸ j.isLt))
  have pair := large_second_prefix starts hlarge j second afterLarge hbin hslot earlier
  have hlength : (contents S last.val j.val).length ≤ 2 :=
    (contents_prefix S (b := j.val) last.isLt.le).length_le.trans hshort
  apply lt_of_not_ge
  intro fits
  have grows := extra_slot_of_rejection (run ffChoice (S.take last.val)) j.val
    [large.get j, S.get second] candidate (S.get last) (by simpa using fits)
    hleast pair (j.isLt.trans_le lastOutside)
  exact (Nat.not_lt_of_ge hlength) grows

/-- Claim 5.9.3. A large-item bin gets a second greedy occupant if an item
at least as large as the terminal item fits beside its anchor. -/
theorem second_slot_of_fitting_companion {large S : List ℝ} (starts : large <+: S)
    (hlarge : ∀ a ∈ large, (1 / 2 : ℝ) < a) (j : Fin large.length)
    (last : Fin S.length) (lastAfter : large.length ≤ last.val)
    (lastOutside : large.length ≤ binOf ffChoice S last) (candidate : ℝ)
    (hleast : S.get last ≤ candidate) (hfit : large.get j + candidate ≤ 1) :
    2 ≤ (contents S S.length j.val).length := by
  have anchor : [large.get j] <+: contents S last.val j.val :=
    large_anchor_prefix starts hlarge lastAfter j.isLt
  have grows := extra_slot_of_rejection (run ffChoice (S.take last.val)) j.val
    [large.get j] candidate (S.get last) (by simpa using hfit) hleast anchor
    (j.isLt.trans_le lastOutside)
  exact (show 2 ≤ (contents S last.val j.val).length from grows).trans
    (contents_prefix S (b := j.val) last.isLt.le).length_le

/-- A companion in a feasible three-piece large bin is smaller than a B-piece. -/
theorem deficit_optimal_companion_le_third {anchor item other : ℝ}
    (large : (1 / 2 : ℝ) < anchor) (hother : (2 / 11 : ℝ) < other)
    (fits : anchor + item + other ≤ 1) : item ≤ 1 / 3 := by
  linarith

theorem size_le_of_rank_le {S : List ℝ} (sorted : S.Pairwise (fun a b => b ≤ a))
    {i j : Fin S.length} (ranks : i.val ≤ j.val) : S.get j ≤ S.get i := by
  rcases lt_or_eq_of_le ranks with before | same
  · exact (List.pairwise_iff_getElem.mp sorted) _ _ i.isLt j.isLt before
  · exact (Fin.ext same : i = j) ▸ le_rfl

/-- Claim 5.9.8. If the second greedy occupant of a short large bin came
from another deficit bin in the optimal assignment, that source bin's own
second greedy occupant has size greater than `1/3`. -/
theorem deficit_edge_second_gt_third {large S : List ℝ} (starts : large <+: S)
    (hlarge : ∀ a ∈ large, (1 / 2 : ℝ) < a) (sorted : S.Pairwise (fun a b => b ≤ a))
    (source target : Fin large.length) (sourceSecond targetSecond other last : Fin S.length)
    (sourceAfter : large.length ≤ sourceSecond.val) (targetAfter : large.length ≤ targetSecond.val)
    (sourceBin : binOf ffChoice S sourceSecond = source.val)
    (targetBin : binOf ffChoice S targetSecond = target.val)
    (sourceSlot : slotOf ffChoice S sourceSecond = 1) (targetSlot : slotOf ffChoice S targetSecond = 1)
    (terminal : last.val + 1 = S.length) (lastOutside : large.length ≤ binOf ffChoice S last)
    (sourceShort : (contents S S.length source.val).length ≤ 2)
    (targetShort : (contents S S.length target.val).length ≤ 2)
    (sourceFit : large.get source + S.get targetSecond + S.get other ≤ 1)
    (targetSpace : large.get target + (4 / 11 : ℝ) ≤ 1) : (1 / 3 : ℝ) < S.get sourceSecond := by
  have least (item : Fin S.length) : S.get last ≤ S.get item :=
    size_le_of_rank_le sorted (by have := item.isLt; omega)
  have targetRejects := short_large_bin_rejects_third starts hlarge target targetSecond last
    targetAfter targetBin targetSlot terminal lastOutside targetShort (S.get other) (least other)
  have sourceRejects := short_large_bin_rejects_third starts hlarge source sourceSecond last
    sourceAfter sourceBin sourceSlot terminal lastOutside sourceShort (S.get other) (least other)
  have targetBefore : target.val < source.val := by
    by_contra reversed
    have smaller := size_le_of_rank_le (sorted.sublist starts.sublist)
      (i := source) (j := target) (le_of_not_gt reversed)
    linarith
  apply lt_of_not_ge
  intro small
  have fits : large.get target + S.get sourceSecond ≤ 1 := by linarith
  have rankOrder : targetSecond.val ≤ sourceSecond.val := by
    by_contra reversed
    have anchor : [large.get target] <+: contents S sourceSecond.val (binOf ffChoice S targetSecond) := by
      rw [targetBin]
      exact large_anchor_prefix starts hlarge sourceAfter target.isLt
    have backwards := binOf_lt_before_second sourceSecond targetSecond (by omega)
      targetSlot (large.get target) anchor fits
    rw [sourceBin, targetBin] at backwards
    omega
  linarith [size_le_of_rank_le sorted rankOrder]

end BinPacking.Decreasing.FirstFitHistory

end

/- chains/GreedySlots.lean -/
section

namespace BinPacking.Decreasing.FirstFitHistory

/-- The zero-based bin and slot of each item occurrence in the first-fit run. -/
noncomputable def greedySlot (S : List ℝ) (item : Fin S.length) : ℕ × ℕ :=
  (binOf ffChoice S item, slotOf ffChoice S item)

private theorem contents_chosen_succ (S : List ℝ) (item : Fin S.length) :
    contents S (item.val + 1) (binOf ffChoice S item) =
      contents S item.val (binOf ffChoice S item) ++ [S.get item] := by
  rw [contents, List.take_add_one, List.getElem?_eq_getElem item.isLt, Option.toList_some, run,
    List.foldl_append]
  let bins := run ffChoice (S.take item.val)
  let chosen := ffChoice bins (S.get item)
  change (placeAt bins chosen (S.get item)).getD chosen [] = bins.getD chosen [] ++ [S.get item]
  have atMost : chosen ≤ bins.length := List.findIdx_le_length (xs := bins)
    (p := fun bin : List ℝ => decide (bin.sum + S.get item ≤ 1))
  rcases lt_or_eq_of_le atMost with inside | atEnd
  · simp [placeAt, inside, List.getD_eq_getElem?_getD]
  · simp [placeAt, atEnd, List.getD_eq_getElem?_getD]

/-- Two items in one bin appear in arrival order. -/
theorem slotOf_lt_of_lt_of_binOf_eq {S : List ℝ} {i j : Fin S.length}
    (earlier : i.val < j.val) (sameBin : binOf ffChoice S i = binOf ffChoice S j) :
    slotOf ffChoice S i < slotOf ffChoice S j := by
  calc
    slotOf ffChoice S i < (contents S (i.val + 1) (binOf ffChoice S i)).length := by
      rw [contents_chosen_succ, List.length_append, List.length_singleton]
      exact Nat.lt_succ_self _
    _ ≤ (contents S j.val (binOf ffChoice S i)).length :=
      (contents_prefix S (Nat.succ_le_of_lt earlier)).length_le
    _ = slotOf ffChoice S j := by rw [sameBin]; rfl

theorem greedySlot_injective (S : List ℝ) : Function.Injective (greedySlot S) := by
  intro i j sameSlot
  rcases lt_trichotomy i.val j.val with earlier | same | later
  · exact (Nat.ne_of_lt (slotOf_lt_of_lt_of_binOf_eq earlier (congrArg Prod.fst sameSlot))
      (congrArg Prod.snd sameSlot)).elim
  · exact Fin.ext same
  · exact (Nat.ne_of_lt (slotOf_lt_of_lt_of_binOf_eq later (congrArg Prod.fst sameSlot.symm))
      (congrArg Prod.snd sameSlot.symm)).elim

end BinPacking.Decreasing.FirstFitHistory

end

/- small-only/FirstFitCoverage.lean -/
section

set_option autoImplicit false

namespace BinPacking.Decreasing.FirstFitHistory

/-- Every occupied slot at a given stage comes from an earlier input position. -/
theorem exists_greedySlot_of_lt_contents (S : List ℝ) (t b k : ℕ) (ht : t ≤ S.length)
    (hslot : k < (contents S t b).length) :
    ∃ i : Fin S.length, i.val < t ∧ greedySlot S i = (b, k) ∧
      (contents S t b)[k]? = some (S.get i) := by
  induction t with
  | zero => simp [contents, run] at hslot
  | succ t ih =>
    by_cases previous : k < (contents S t b).length
    · obtain ⟨i, hi, hindex, hvalue⟩ := ih (Nat.le_of_succ_le ht) previous
      refine ⟨i, hi.trans (Nat.lt_succ_self t), hindex, ?_⟩
      obtain ⟨_, after⟩ := contents_prefix S (b := b) (Nat.le_succ t)
      simpa only [← after, List.getElem?_append_left previous] using hvalue
    · let i : Fin S.length := ⟨t, Nat.lt_of_succ_le ht⟩
      have step := contents_succ S i b
      have chosen : b = binOf ffChoice S i := by
        by_contra different
        have unchanged : contents S (t + 1) b = contents S t b := by
          simpa only [i, Fin.val_mk, if_neg different] using step
        exact previous (unchanged ▸ hslot)
      have appended : contents S (t + 1) b = contents S t b ++ [S.get i] := by
        simpa only [i, Fin.val_mk, if_pos chosen] using step
      have atEnd : k = (contents S t b).length := by
        rw [appended, List.length_append, List.length_singleton] at hslot
        omega
      refine ⟨i, Nat.lt_succ_self t, ?_, ?_⟩
      · apply Prod.ext chosen.symm
        change (contents S t (binOf ffChoice S i)).length = k
        simpa only [← chosen] using atEnd.symm
      · simp [appended, atEnd]

/-- Every occupied slot of the final run is the slot of an input occurrence. -/
theorem exists_greedySlot_of_lt_run (S : List ℝ) (b k : ℕ)
    (hslot : k < ((run ffChoice S).getD b []).length) :
    ∃ i : Fin S.length, greedySlot S i = (b, k) ∧
      ((run ffChoice S).getD b [])[k]? = some (S.get i) := by
  obtain ⟨i, _, hindex, hvalue⟩ := exists_greedySlot_of_lt_contents S S.length b k le_rfl
    (by simpa only [contents, List.take_length] using hslot)
  exact ⟨i, hindex, by simpa only [contents, List.take_length] using hvalue⟩

private theorem chosen_capacity (bins : List (List ℝ)) (a : ℝ) (ha : a ≤ 1) :
    (bins.getD (ffChoice bins a) []).sum + a ≤ 1 := by
  cases h : bins[ffChoice bins a]? with
  | none => simpa [List.getD_eq_getElem?_getD, h] using ha
  | some bin =>
    have fits := List.findIdx_of_getElem?_eq_some
      (p := fun B : List ℝ => decide (B.sum + a ≤ 1)) h
    simpa [List.getD_eq_getElem?_getD, h] using of_decide_eq_true fits

/-- First Fit maintains the unit capacity of each bin at every stage of a valid input. -/
theorem contents_sum_le_one {S : List ℝ} (hS : IsList S) (t b : ℕ) (ht : t ≤ S.length) :
    (contents S t b).sum ≤ 1 := by
  induction t with
  | zero => simp [contents, run]
  | succ t ih =>
    let i : Fin S.length := ⟨t, Nat.lt_of_succ_le ht⟩
    have step := contents_succ S i b
    by_cases chosen : b = binOf ffChoice S i
    · have appended : contents S (t + 1) b = contents S t b ++ [S.get i] := by
        simpa only [i, Fin.val_mk, if_pos chosen] using step
      rw [appended, List.sum_append, List.sum_singleton, chosen]
      exact chosen_capacity (run ffChoice (S.take t)) (S.get i) (hS _ (List.get_mem S i)).2
    · have unchanged : contents S (t + 1) b = contents S t b := by
        simpa only [i, Fin.val_mk, if_neg chosen] using step
      simpa only [unchanged] using ih (Nat.le_of_succ_le ht)

theorem run_getD_sum_le_one {S : List ℝ} (hS : IsList S) (b : ℕ) :
    ((run ffChoice S).getD b []).sum ≤ 1 := by
  simpa only [contents, List.take_length] using contents_sum_le_one hS S.length b le_rfl

/-- The contents of a bin come from the part of the input already processed. -/
theorem contents_subset_take (S : List ℝ) (t b : ℕ) (ht : t ≤ S.length) :
    contents S t b ⊆ S.take t := by
  intro a ha
  obtain ⟨k, hk, hitem⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨i, earlier, _, hvalue⟩ := exists_greedySlot_of_lt_contents S t b k ht hk
  rw [List.getElem?_eq_getElem hk, hitem] at hvalue
  rw [Option.some.inj hvalue]
  exact List.mem_iff_getElem.mpr ⟨i.val, by rwa [List.length_take_of_le ht], by simp⟩

theorem run_getD_subset (S : List ℝ) (b : ℕ) : (run ffChoice S).getD b [] ⊆ S := by
  simpa only [contents, List.take_length] using contents_subset_take S S.length b le_rfl

/-- Every final bin fits within capacity and contains only items from the input. -/
theorem run_bin_valid {S B : List ℝ} (hS : IsList S) (hB : B ∈ run ffChoice S) :
    B.sum ≤ 1 ∧ B ⊆ S := by
  obtain ⟨b, hb, hvalue⟩ := List.mem_iff_getElem.mp hB
  have hbin : (run ffChoice S).getD b [] = B := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some] using hvalue
  rw [← hbin]
  exact ⟨run_getD_sum_le_one hS b, run_getD_subset S b⟩

end BinPacking.Decreasing.FirstFitHistory

end

/- small-only/LargeGreedySlots.lean -/
section

set_option autoImplicit false

namespace BinPacking.Decreasing.FirstFitHistory

/-- Each item in an initial prefix of large items opens its own bin in index order. -/
theorem greedySlot_of_large {large S : List ℝ} (startsWithLarge : large <+: S)
    (allLarge : ∀ a ∈ large, (1 / 2 : ℝ) < a) (i : Fin S.length) (hi : i.val < large.length) :
    greedySlot S i = (i.val, 0) := by
  obtain ⟨rest, rfl⟩ := startsWithLarge
  have itemLarge : (1 / 2 : ℝ) < (large ++ rest).get i := by
    rw [List.get_eq_getElem, List.getElem_append_left hi]
    exact allLarge _ (List.getElem_mem hi)
  have runBefore : run ffChoice ((large ++ rest).take i.val) =
      (large.take i.val).map (fun a => [a]) := by
    rw [List.take_append_of_le_length hi.le]
    change (large.take i.val).foldl firstFitStep [] = (large.take i.val).map (fun a => [a])
    simpa only [List.map_nil, List.nil_append] using
      firstFitFold_large (large.take i.val) [] (fun a ha => allLarge a (List.mem_of_mem_take ha))
        (by simp)
  have noFit : ffChoice (run ffChoice ((large ++ rest).take i.val)) ((large ++ rest).get i) =
      (run ffChoice ((large ++ rest).take i.val)).length := by
    rw [runBefore]
    apply List.findIdx_eq_length.mpr
    intro bin hbin
    obtain ⟨earlier, hear, rfl⟩ := List.mem_map.mp hbin
    simp only [List.sum_singleton, decide_eq_false_iff_not]
    linarith only [allLarge earlier (List.mem_of_mem_take hear), itemLarge]
  have countBefore : (run ffChoice ((large ++ rest).take i.val)).length = i.val := by
    rw [runBefore, List.length_map, List.length_take_of_le hi.le]
  have binEq : binOf ffChoice (large ++ rest) i = i.val := noFit.trans countBefore
  apply Prod.ext binEq
  change ((run ffChoice ((large ++ rest).take i.val)).getD
    (binOf ffChoice (large ++ rest) i) []).length = 0
  rw [binEq, List.getD_eq_getElem?_getD, List.getElem?_eq_none countBefore.le]
  rfl

end BinPacking.Decreasing.FirstFitHistory

end

/- small-only/OptimalCompanion.lean -/
section

set_option autoImplicit false

namespace BinPacking.Decreasing

/-- Summing any subset of positions assigned to one bin respects capacity. -/
theorem assignment_sum_le_one_of_same_bin {S : List ℝ} (hS : IsList S) {b : ℕ}
    (assign : Fin S.length → Fin b)
    (hfit : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), S.get i ≤ 1)
    (j : Fin b) (positions : Finset (Fin S.length))
    (same : ∀ i ∈ positions, assign i = j) : ∑ i ∈ positions, S.get i ≤ 1 := by
  have included : positions ⊆ Finset.univ.filter (fun i => assign i = j) := fun i hi =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, same i hi⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg (f := S.get) included
    (fun i _ _ => (hS _ (List.get_mem S i)).1.le)).trans (hfit j)

theorem assignment_pair_sum_le_one {S : List ℝ} (hS : IsList S) {b : ℕ}
    (assign : Fin S.length → Fin b)
    (hfit : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), S.get i ≤ 1)
    (a x : Fin S.length) (different : a ≠ x) (same : assign x = assign a) :
    S.get a + S.get x ≤ 1 := by
  have within : ∀ i ∈ ({a, x} : Finset (Fin S.length)), assign i = assign a := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro i (rfl | rfl)
    · rfl
    · exact same
  simpa only [Finset.sum_pair different] using
    assignment_sum_le_one_of_same_bin hS assign hfit (assign a) {a, x} within

theorem assignment_triple_sum_le_one {S : List ℝ} (hS : IsList S) {b : ℕ}
    (assign : Fin S.length → Fin b)
    (hfit : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), S.get i ≤ 1)
    (a x y : Fin S.length) (hax : a ≠ x) (hay : a ≠ y) (hxy : x ≠ y)
    (sameX : assign x = assign a) (sameY : assign y = assign a) : S.get a + S.get x + S.get y ≤ 1 := by
  have within : ∀ i ∈ ({a, x, y} : Finset (Fin S.length)), assign i = assign a := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro i (rfl | rfl | rfl)
    · rfl
    · exact sameX
    · exact sameY
  have outside : a ∉ ({x, y} : Finset (Fin S.length)) := by simp [hax, hay]
  simpa only [Finset.sum_insert outside, Finset.sum_pair hxy, add_assoc] using
    assignment_sum_le_one_of_same_bin hS assign hfit (assign a) {a, x, y} within

/-- A third occupied slot supplies a second small item beside an anchor and a given small item. -/
theorem exists_small_companion_of_slot_two {S : List ℝ} (hS : IsList S) {b : ℕ}
    (assign : Fin S.length → Fin b)
    (hfit : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), S.get i ≤ 1)
    (a x third : Fin S.length) (ha : (1 / 2 : ℝ) < S.get a) (hx : S.get x ≤ 1 / 2)
    (hbin : assign x = assign a) (hthird : assign third = assign a)
    (hslot : assignmentSlot assign third = 2) :
    ∃ other : Fin S.length, assign other = assign a ∧ other ≠ x ∧ other ≠ a ∧
      S.get other ≤ 1 / 2 ∧ S.get a + S.get x + S.get other ≤ 1 := by
  let positions := (assignmentPositions assign (assign a)).toFinset
  have atLeastThree : 2 < (assignmentPositions assign (assign a)).length := by
    simpa only [hslot, hthird] using assignmentSlot_lt assign third
  have distinctPositions : (assignmentPositions assign (assign a)).Nodup :=
    (List.nodup_finRange _).filter _
  have enough : 2 < positions.card := by
    simpa only [positions, List.toFinset_card_of_nodup distinctPositions] using atLeastThree
  obtain ⟨other, hother⟩ := Finset.sdiff_nonempty_of_card_lt_card
    ((show ({a, x} : Finset (Fin S.length)).card ≤ 2 from Finset.card_le_two).trans_lt enough)
  obtain ⟨present, hnot⟩ := Finset.mem_sdiff.mp hother
  have sameBin : assign other = assign a := by
    simpa only [positions, List.mem_toFinset, mem_assignmentPositions] using present
  have different : other ≠ a ∧ other ≠ x := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hnot
  have anchorNeX : a ≠ x := fun equal => (not_lt_of_ge hx) (equal ▸ ha)
  refine ⟨other, sameBin, different.2, different.1, ?_,
    assignment_triple_sum_le_one hS assign hfit a x other anchorNeX different.1.symm
      different.2.symm hbin sameBin⟩
  linarith only [ha, assignment_pair_sum_le_one hS assign hfit a other different.1.symm sameBin]

end BinPacking.Decreasing

end

/- PackingSlots.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

open FirstFitHistory

noncomputable section

abbrev NonLargePosition (S : List ℝ) := {i : Fin S.length // (largePrefixItems S).length ≤ i.val}

def smallGreedySlot {S : List ℝ} (i : NonLargePosition S) : ℕ × ℕ := greedySlot S i.val

def smallOptimalSlot {S : List ℝ} (p : AlignedPacking S) (i : NonLargePosition S) : ℕ × ℕ :=
  optimalPosition p.assign i.val

abbrev isLargeBin (S : List ℝ) (j : ℕ) : Prop := j < (largePrefixItems S).length

abbrev Deficit {S : List ℝ} (p : AlignedPacking S) :=
  PieceChains.DeficitBin smallGreedySlot p.smallOptimalSlot (isLargeBin S)

variable {S : List ℝ} (p : AlignedPacking S)

theorem smallGreedySlot_injective : Function.Injective (smallGreedySlot (S := S)) :=
  fun _ _ same => Subtype.ext (greedySlot_injective S same)

theorem smallOptimalSlot_injective : Function.Injective p.smallOptimalSlot :=
  fun _ _ same => Subtype.ext (optimalPosition_injective p.assign same)

include p in
theorem nonLarge_at_greedy_slot (bin slot : ℕ) (positive : 0 < slot)
    (occupied : slot < (contents S S.length bin).length) :
    ∃ i : NonLargePosition S, smallGreedySlot i = (bin, slot) := by
  obtain ⟨i, _, observed, _⟩ := exists_greedySlot_of_lt_contents S S.length bin slot le_rfl occupied
  have nonLarge : (largePrefixItems S).length ≤ i.val := by
    by_contra inside
    have zero := greedySlot_of_large p.starts (allLarge S) i (lt_of_not_ge inside)
    rw [observed] at zero
    exact (Nat.ne_of_gt positive) (congrArg Prod.snd zero)
  exact ⟨⟨i, nonLarge⟩, observed⟩

include p in
theorem greedy_large_bin_length_le_three (j : Fin (largePrefixItems S).length) :
    (contents S S.length j.val).length ≤ 3 := by
  apply large_bin_length_le_three
  · exact contents_sum_le_one p.valid S.length j.val le_rfl
  · exact fun a ha => p.threshold a (List.mem_of_mem_take (contents_subset_take S S.length j.val le_rfl ha))
  · have anchor := large_anchor_prefix p.starts (allLarge S) (List.length_filter_le _ _) j.isLt
    exact ⟨(largePrefixItems S).get j, anchor.subset (by simp), allLarge S _ (List.get_mem _ j)⟩

theorem optimal_small_slot_eligible (i : NonLargePosition S)
    (inside : isLargeBin S (p.smallOptimalSlot i).1) :
    (p.smallOptimalSlot i).2 = 1 ∨ (p.smallOptimalSlot i).2 = 2 := by
  let j : Fin (largePrefixItems S).length := ⟨(p.assign i.val).val, inside⟩
  have assigned := p.assign_eq_anchor_bin j i.val rfl
  have occupied : assignmentSlot p.assign i.val < (assignmentBin p.assign (p.anchorBin j)).length := by
    simpa only [assignmentBin, List.length_map, assigned] using assignmentSlot_lt p.assign i.val
  have bounded := p.optimal_large_bin_length_le_three j
  have nonzero : assignmentSlot p.assign i.val ≠ 0 := by
    intro zero
    have same : optimalPosition p.assign i.val = (j.val, 0) := Prod.ext rfl zero
    have eqIndex := optimalPosition_injective p.assign (same.trans (p.optimal_anchor_slot j).symm)
    have eqRank : i.val.val = j.val := congrArg Fin.val eqIndex
    exact (Nat.not_lt_of_ge i.property) (eqRank.symm ▸ j.isLt)
  change assignmentSlot p.assign i.val = 1 ∨ assignmentSlot p.assign i.val = 2
  omega

theorem fits_beside_anchor (j : Fin (largePrefixItems S).length) (i : NonLargePosition S)
    (label : (p.smallOptimalSlot i).1 = j.val) :
    (largePrefixItems S).get j + S.get i.val ≤ 1 := by
  have distinct : anchorIndex j ≠ i.val := by
    intro same
    exact (Nat.not_lt_of_ge i.property) (same ▸ j.isLt)
  rw [← p.anchor_index_size j]
  exact assignment_pair_sum_le_one p.valid p.assign p.fits _ _ distinct
    (p.assign_eq_anchor_bin j _ label)

theorem last_size_le (i : Fin S.length) : S.get p.last ≤ S.get i :=
  size_le_of_rank_le p.sorted (by have := p.terminal; have := i.isLt; omega)

theorem greedy_second_occupied (j : Fin (largePrefixItems S).length) (i : NonLargePosition S)
    (label : (p.smallOptimalSlot i).1 = j.val) :
    ∃ second : NonLargePosition S, smallGreedySlot second = (j.val, 1) := by
  have length := second_slot_of_fitting_companion p.starts (allLarge S) j p.last p.lastAfter
    p.lastOutside (S.get i.val) (p.last_size_le i.val) (p.fits_beside_anchor j i label)
  exact p.nonLarge_at_greedy_slot j.val 1 (by decide) length

theorem deficit_greedy_short (d : p.Deficit) : (contents S S.length d.val).length ≤ 2 := by
  by_contra long
  obtain ⟨i, slot⟩ := p.nonLarge_at_greedy_slot d.val 2 (by decide) (lt_of_not_ge long)
  exact d.property.2.2 i slot

theorem deficit_second_occupied (d : p.Deficit) :
    ∃ second : NonLargePosition S, smallGreedySlot second = (d.val, 1) := by
  obtain ⟨top, htop⟩ := d.property.2.1
  exact p.greedy_second_occupied ⟨d.val, d.property.1⟩ top (congrArg Prod.fst htop)

theorem exists_optimal_companion_of_third (j : Fin (largePrefixItems S).length)
    (i top : NonLargePosition S) (label : (p.smallOptimalSlot i).1 = j.val)
    (htop : p.smallOptimalSlot top = (j.val, 2)) :
    ∃ other : Fin S.length, (largePrefixItems S).get j + S.get i.val + S.get other ≤ 1 := by
  have iSmall : S.get i.val ≤ 1 / 2 := by
    apply le_of_not_gt
    intro large
    exact (Nat.not_lt_of_ge i.property) ((largeItem_iff_lt_filter_length p.sorted i.val).mp large)
  obtain ⟨other, _, _, _, _, fits⟩ := exists_small_companion_of_slot_two p.valid p.assign p.fits
    (anchorIndex j) i.val top.val (p.anchor_index_large j) iSmall
    (p.assign_eq_anchor_bin j _ label) (p.assign_eq_anchor_bin j _ (congrArg Prod.fst htop))
    (congrArg Prod.snd htop)
  exact ⟨other, (p.anchor_index_size j) ▸ fits⟩

theorem exists_optimal_deficit_companion (d : p.Deficit) (i : NonLargePosition S)
    (label : (p.smallOptimalSlot i).1 = d.val) :
    ∃ other : Fin S.length, (largePrefixItems S).get ⟨d.val, d.property.1⟩ +
      S.get i.val + S.get other ≤ 1 := by
  obtain ⟨top, htop⟩ := d.property.2.1
  exact p.exists_optimal_companion_of_third ⟨d.val, d.property.1⟩ i top label htop

def optimalHasB (bin : ℕ) : Prop :=
  ∃ item : NonLargePosition S, (p.smallOptimalSlot item).1 = bin ∧ (1 / 3 : ℝ) < S.get item.val

theorem no_optimal_B_of_third (j : Fin (largePrefixItems S).length) (top : NonLargePosition S)
    (htop : p.smallOptimalSlot top = (j.val, 2)) : ¬p.optimalHasB j.val := by
  rintro ⟨item, label, large⟩
  obtain ⟨other, fits⟩ := p.exists_optimal_companion_of_third j item top label htop
  exact (not_lt_of_ge (deficit_optimal_companion_le_third
    (allLarge S _ (List.get_mem _ j)) (p.threshold _ (List.get_mem S other)) fits)) large

theorem deficit_anchor_space (d : p.Deficit) :
    (largePrefixItems S).get ⟨d.val, d.property.1⟩ + (4 / 11 : ℝ) ≤ 1 := by
  obtain ⟨top, htop⟩ := d.property.2.1
  obtain ⟨other, fit⟩ := p.exists_optimal_deficit_companion d top (congrArg Prod.fst htop)
  linarith only [fit, p.threshold _ (List.get_mem S top.val), p.threshold _ (List.get_mem S other)]

theorem no_large_companion_in_optimal_deficit (i : NonLargePosition S)
    (deficit : PieceChains.IsDeficit smallGreedySlot p.smallOptimalSlot (isLargeBin S)
      (p.smallOptimalSlot i).1) : S.get i.val ≤ 1 / 3 := by
  let d : p.Deficit := ⟨(p.smallOptimalSlot i).1, deficit⟩
  obtain ⟨other, fit⟩ := p.exists_optimal_deficit_companion d i rfl
  exact deficit_optimal_companion_le_third (allLarge S _ (List.get_mem _ ⟨d.val, d.property.1⟩))
    (p.threshold _ (List.get_mem S other)) fit

theorem deficit_predecessor_second_large (source target : p.Deficit)
    (link inner : NonLargePosition S) (linkSlot : smallGreedySlot link = (target.val, 1))
    (sourceLabel : (p.smallOptimalSlot link).1 = source.val)
    (innerSlot : smallGreedySlot inner = (source.val, 1)) : (1 / 3 : ℝ) < S.get inner.val := by
  obtain ⟨other, fits⟩ := p.exists_optimal_deficit_companion source link sourceLabel
  exact deficit_edge_second_gt_third p.starts (allLarge S) p.sorted
    ⟨source.val, source.property.1⟩ ⟨target.val, target.property.1⟩
    inner.val link.val other p.last inner.property link.property
    (congrArg Prod.fst innerSlot) (congrArg Prod.fst linkSlot)
    (congrArg Prod.snd innerSlot) (congrArg Prod.snd linkSlot)
    p.terminal p.lastOutside (p.deficit_greedy_short source) (p.deficit_greedy_short target)
    fits (p.deficit_anchor_space target)

theorem firstFitBefore {blocker item : NonLargePosition S}
    (second : (smallGreedySlot blocker).2 = 1)
    (inside : (smallGreedySlot blocker).1 < (largePrefixItems S).length)
    (optimalEarlier : (p.smallOptimalSlot item).1 ≤ (smallGreedySlot blocker).1)
    (earlier : item.val.val < blocker.val.val) :
    (smallGreedySlot item).1 < (smallGreedySlot blocker).1 := by
  let optimalBin : Fin (largePrefixItems S).length :=
    ⟨(p.smallOptimalSlot item).1, optimalEarlier.trans_lt inside⟩
  exact binOf_lt_before_second_of_largePrefix p.starts (allLarge S)
    (p.sorted.sublist p.starts.sublist) item.val blocker.val item.property earlier second inside
    optimalBin optimalEarlier (p.fits_beside_anchor optimalBin item rfl)

end

end BinPacking.Decreasing.AlignedPacking

end

/- PackingOwnership.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

open PieceChains

noncomputable section

variable {S : List ℝ} (p : AlignedPacking S)

abbrev points := slotPoints smallGreedySlot p.smallOptimalSlot (isLargeBin S)

def ordinaryOwner (item : NonLargePosition S) : Fin S.length := item.val

def largeOwner (bin : ℕ) (inside : isLargeBin S bin) : Fin S.length :=
  anchorIndex ⟨bin, inside⟩

def origin := slotOrigin smallGreedySlot p.smallOptimalSlot (isLargeBin S)
  (fun item _ => ordinaryOwner item) (fun bin inside _ => largeOwner bin inside)

def predecessor := slotDeficitPrevious smallGreedySlot p.smallOptimalSlot (isLargeBin S)
  (fun item _ => ordinaryOwner item) (fun bin inside _ => largeOwner bin inside)
  p.deficit_second_occupied

theorem predecessor_noThree : NoThreeDeficits p.predecessor :=
  slotDeficitPrevious_noThree smallGreedySlot p.smallOptimalSlot (isLargeBin S)
    (fun item _ => ordinaryOwner item) (fun bin inside _ => largeOwner bin inside)
    p.deficit_second_occupied (fun item => (1 / 3 : ℝ) < S.get item.val)
    (fun item deficit => not_lt_of_ge (p.no_large_companion_in_optimal_deficit item deficit))
    p.deficit_predecessor_second_large

abbrev ResidualPosition (S : List ℝ) :=
  {item : NonLargePosition S // ¬isLargeBin S (smallGreedySlot item).1}

theorem residual_isTail {item : NonLargePosition S} (outside : ¬isLargeBin S (smallGreedySlot item).1) :
    IsTail p.points item :=
  (slotPoints_tail_iff smallGreedySlot p.smallOptimalSlot (isLargeBin S)).mpr (.inl outside)

def owner (item : ResidualPosition S) : Fin S.length :=
  residualOwner
    (slotPoints_uniqueNext smallGreedySlot p.smallOptimalSlot (isLargeBin S)
      p.smallOptimalSlot_injective)
    (slotPoints_uniquePrevious smallGreedySlot p.smallOptimalSlot (isLargeBin S)
      (smallGreedySlot_injective (S := S)))
    (fun head => p.origin head.val) p.predecessor p.predecessor_noThree
    (fun {_} outside => p.residual_isTail outside) item

theorem owner_eq_iff (item : ResidualPosition S) (position : Fin S.length) :
    p.owner item = position ↔
      OwnsResidual p.points (fun head => p.origin head.val) p.predecessor position item.val :=
  residualOwner_eq_iff _ _ _ _ _ _ _ _

theorem owner_head_cases (item : ResidualPosition S) :
    ∃ head : NonLargePosition S, IsHead p.points head ∧ Relation.ReflTransGen p.points head item.val ∧
      ((¬isLargeBin S (p.smallOptimalSlot head).1 ∧ p.owner item = head.val) ∨
        ∃ bin : p.Deficit, p.smallOptimalSlot head = (bin.val, 2) ∧
          ResponsibleFor p.predecessor (p.owner item) bin) := by
  obtain ⟨head, path, owns⟩ := (p.owner_eq_iff item _).mp rfl
  have classified := slotOrigin_of_head smallGreedySlot p.smallOptimalSlot (isLargeBin S)
    (fun source _ => ordinaryOwner source) (fun bin inside _ => largeOwner bin inside)
    head.val head.property (p.optimal_small_slot_eligible head.val) (by
      intro inside slot
      let bin : Fin (largePrefixItems S).length := ⟨(p.smallOptimalSlot head.val).1, inside⟩
      obtain ⟨earlier, atSecond⟩ := p.greedy_second_occupied bin head.val rfl
      exact ⟨earlier, atSecond.trans (Prod.ext rfl slot.symm)⟩)
  change ownsHead p.predecessor (p.origin head.val) (p.owner item) at owns
  refine ⟨head.val, head.property, path, ?_⟩
  rcases classified with ⟨outside, direct⟩ | ⟨bin, third, indirect⟩
  · change p.origin head.val = .inl head.val at direct
    rw [direct] at owns
    exact .inl ⟨outside, owns⟩
  · change p.origin head.val = .inr bin at indirect
    rw [indirect] at owns
    exact .inr ⟨bin, third, owns⟩

theorem residual_eq_of_same_head {head : NonLargePosition S} {x y : ResidualPosition S}
    (pathX : Relation.ReflTransGen p.points head x.val)
    (pathY : Relation.ReflTransGen p.points head y.val) : x = y :=
  Subtype.ext (tails_eq
    (slotPoints_uniqueNext smallGreedySlot p.smallOptimalSlot (isLargeBin S)
      p.smallOptimalSlot_injective)
    (p.residual_isTail x.property) (p.residual_isTail y.property) pathX pathY)

private theorem exists_origin_of_owner (item : ResidualPosition S) :
    ∃ source : NonLargePosition S, p.origin source = .inl (p.owner item) := by
  obtain ⟨head, _, owns⟩ := (p.owner_eq_iff item _).mp rfl
  change ownsHead p.predecessor (p.origin head.val) (p.owner item) at owns
  cases classification : p.origin head.val with
  | inl direct =>
    rw [classification] at owns
    exact ⟨head.val, (show p.owner item = direct from owns).symm ▸ classification⟩
  | inr deficit =>
    rw [classification] at owns
    have reaches : Relation.ReflTransGen (deficitPoints p.predecessor)
        (.inl (p.owner item)) (.inr deficit) := owns
    obtain ⟨next, first, _⟩ := reaches.cases_head.resolve_left (by simp)
    cases next with
    | inl _ => exact first.elim
    | inr bin =>
      let source := deficitIncoming smallGreedySlot p.smallOptimalSlot (isLargeBin S)
        p.deficit_second_occupied bin
      exact ⟨source, first⟩

theorem owner_anchor_of_label (item : ResidualPosition S) (j : Fin (largePrefixItems S).length)
    (label : (p.assign (p.owner item)).val = j.val) : p.owner item = anchorIndex j ∧
      ¬IsDeficit smallGreedySlot p.smallOptimalSlot (isLargeBin S) j.val := by
  classical
  obtain ⟨source, originOwner⟩ := p.exists_origin_of_owner item
  unfold origin slotOrigin at originOwner
  split at originOwner
  · contradiction
  next nondeficit =>
    split at originOwner
    next inside =>
      have equal : largeOwner (p.smallOptimalSlot source).1 inside = p.owner item :=
        Sum.inl.inj originOwner
      let k : Fin (largePrefixItems S).length := ⟨(p.smallOptimalSlot source).1, inside⟩
      have kLabel : k.val = j.val := (p.anchor_bin_index k).symm.trans
        ((congrArg (fun i => (p.assign i).val) equal).trans label)
      exact ⟨equal.symm.trans (congrArg anchorIndex (Fin.ext kLabel)), kLabel ▸ nondeficit⟩
    next outside =>
      have equal : source.val = p.owner item := Sum.inl.inj originOwner
      have sourceLabel : (p.smallOptimalSlot source).1 = j.val :=
        (congrArg (fun i => (p.assign i).val) equal).trans label
      exact (outside (sourceLabel.symm ▸ j.isLt)).elim

theorem owner_eq_anchor_of_label (item : ResidualPosition S) (j : Fin (largePrefixItems S).length)
    (label : (p.assign (p.owner item)).val = j.val) : p.owner item = anchorIndex j :=
  (p.owner_anchor_of_label item j label).1

end

end BinPacking.Decreasing.AlignedPacking

end

/- ResidualPositions.lean -/
section

namespace BinPacking.Decreasing

/-- Keep the items routed to bins at or beyond a fixed index. -/
private noncomputable def routedAfter (cutoff : ℕ) : List ℝ → List (List ℝ) → List ℝ
  | [], _ => []
  | x :: xs, bins =>
      let rest := routedAfter cutoff xs (firstFitStep bins x)
      if cutoff ≤ ffChoice bins x then x :: rest else rest

private theorem choice_after_append (early late : List (List ℝ)) (item : ℝ) :
    early.length ≤ ffChoice (early ++ late) item ↔ ¬ ffChoice early item < early.length := by
  simp only [ffChoice, List.findIdx_append]
  split <;> omega

private theorem routedAfter_append_bins (items : List ℝ) (early late : List (List ℝ)) :
    routedAfter early.length items (early ++ late) = laterItems items early late := by
  induction items generalizing early late with
  | nil => rfl
  | cons x xs ih =>
    simp only [routedAfter, laterItems, firstFitStep_append, choice_after_append]
    by_cases fits : ffChoice early x < early.length
    · have hlength : (firstFitStep early x).length = early.length := by
        simp [firstFitStep, placeAt, fits]
      simpa [fits, hlength] using ih (firstFitStep early x) late
    · simpa [fits] using congrArg (List.cons x) (ih early (firstFitStep late x))

private theorem routedAfter_indexed (cutoff : ℕ) (items : List ℝ) (bins : List (List ℝ)) :
    routedAfter cutoff items bins =
      ((List.finRange items.length).filter (fun i => decide
        (cutoff ≤ ffChoice ((items.take i.val).foldl firstFitStep bins) (items.get i)))).map items.get := by
  induction items generalizing bins with
  | nil => simp [routedAfter]
  | cons x xs ih =>
    simp only [routedAfter, List.length_cons, List.finRange_succ]
    by_cases kept : cutoff ≤ ffChoice bins x <;>
      simp [kept, List.filter_map, List.map_map, Function.comp_def, ih] <;> rfl

private theorem routedAfter_items_append (cutoff : ℕ) (first rest : List ℝ)
    (bins : List (List ℝ)) :
    routedAfter cutoff (first ++ rest) bins =
      routedAfter cutoff first bins ++ routedAfter cutoff rest (first.foldl firstFitStep bins) := by
  induction first generalizing bins with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, List.foldl_cons, routedAfter, ih]
    split <;> rfl

private theorem routedAfter_large_nil (large : List ℝ) (hlarge : ∀ a ∈ large, (1 / 2 : ℝ) < a) :
    routedAfter large.length large [] = [] := by
  rw [routedAfter_indexed]
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro i _
  have hlength : ((large.take i.val).foldl firstFitStep []).length = i.val := by
    simpa [List.length_take, Nat.min_eq_left i.isLt.le] using
      congrArg List.length (firstFitFold_large (large.take i.val) []
        (fun a ha => hlarge a (List.mem_of_mem_take ha)) (by simp))
  simp only [decide_eq_true_eq, not_le]
  exact (show ffChoice ((large.take i.val).foldl firstFitStep []) (large.get i) ≤
      ((large.take i.val).foldl firstFitStep []).length from List.findIdx_le_length).trans_lt
    (hlength.symm ▸ i.isLt)

/-- The residual list keeps exactly the sorted input positions packed outside
the initial segment of bins for large items. Repeated sizes keep separate positions. -/
theorem residualItems_eq_positions (L : List ℝ) :
    let S := sortDesc L
    let cutoff := (S.filter (fun a => decide ((1 / 2 : ℝ) < a))).length
    residualItems L = ((List.finRange S.length).filter (fun i =>
      decide (cutoff ≤ binOf ffChoice S i))).map S.get := by
  let S := sortDesc L
  let large := S.filter (fun a => decide ((1 / 2 : ℝ) < a))
  let small := S.filter (fun a => !decide ((1 / 2 : ℝ) < a))
  let early := large.map (fun a => [a])
  change laterItems small early [] = ((List.finRange S.length).filter (fun i =>
      decide (large.length ≤ binOf ffChoice S i))).map S.get
  have hsplit : S = large ++ small := split_large_of_sorted (sortDesc_sorted L)
  have hlarge : ∀ item ∈ large, (1 / 2 : ℝ) < item := fun item hitem =>
    of_decide_eq_true (List.mem_filter.mp hitem).2
  have hfirst : large.foldl firstFitStep [] = early := by
    simpa [early] using firstFitFold_large large [] hlarge (by simp)
  calc
    _ = routedAfter early.length small early := by
      simpa only [List.append_nil] using (routedAfter_append_bins small early []).symm
    _ = routedAfter large.length (large ++ small) [] := by
      rw [routedAfter_items_append, routedAfter_large_nil large hlarge, List.nil_append, hfirst]
      simp [early]
    _ = routedAfter large.length S [] := congrArg (fun items => routedAfter large.length items []) hsplit.symm
    _ = _ := routedAfter_indexed large.length S []

end BinPacking.Decreasing

end

/- PackingResponsibilities.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

open PieceChains FirstFitHistory

noncomputable section

variable {S : List ℝ} (p : AlignedPacking S)

private def residualIndices (S : List ℝ) : List (Fin S.length) :=
  (List.finRange S.length).filter (fun i =>
    decide ((largePrefixItems S).length ≤ binOf ffChoice S i))

include p in
private theorem afterLarge_of_residual (i : Fin S.length)
    (outside : (largePrefixItems S).length ≤ binOf ffChoice S i) :
    (largePrefixItems S).length ≤ i.val := by
  by_contra before
  have slot := greedySlot_of_large p.starts (allLarge S) i (lt_of_not_ge before)
  have label : binOf ffChoice S i = i.val := congrArg Prod.fst slot
  exact before (label ▸ outside)

def residualPositionOfIndex (i : Fin S.length)
    (outside : (largePrefixItems S).length ≤ binOf ffChoice S i) : ResidualPosition S :=
  ⟨⟨i, p.afterLarge_of_residual i outside⟩, Nat.not_lt_of_ge outside⟩

def residualPositions : List (ResidualPosition S) :=
  (residualIndices S).pmap (P := fun i => (largePrefixItems S).length ≤ binOf ffChoice S i)
    p.residualPositionOfIndex
    (fun _ mem => of_decide_eq_true (List.mem_filter.mp mem).2)

theorem residualPositions_nodup : p.residualPositions.Nodup := by
  exact ((List.nodup_finRange S.length).filter _).pmap
    (fun _ _ _ _ equal => congrArg (fun item : ResidualPosition S => item.val.val) equal)

theorem mem_residualPositions (item : ResidualPosition S) : item ∈ p.residualPositions := by
  unfold residualPositions
  apply List.mem_pmap.mpr
  refine ⟨item.val.val, List.mem_filter.mpr ⟨List.mem_finRange _, ?_⟩, ?_⟩
  · exact decide_eq_true (Nat.le_of_not_gt item.property)
  · rfl

def residualSize (item : ResidualPosition S) : ℝ := S.get item.val.val

theorem residualItems_eq_residualPositions : residualItems S = p.residualPositions.map residualSize := by
  have indexed : residualItems S = (residualIndices (sortDesc S)).map (sortDesc S).get :=
    residualItems_eq_positions S
  have sorted := congrArg (fun T : List ℝ => (residualIndices T).map T.get)
    (sortDesc_eq_self_of_sorted p.sorted)
  replace indexed := indexed.trans sorted
  rw [indexed, residualPositions, List.map_pmap]
  exact (List.pmap_eq_map _).symm

def responsibilityBin (item : ResidualPosition S) : Fin (optBins S) := p.assign (p.owner item)

theorem responsibilityBin_eq_anchorBin_iff (item : ResidualPosition S)
    (j : Fin (largePrefixItems S).length) :
    p.responsibilityBin item = p.anchorBin j ↔ p.owner item = anchorIndex j := by
  constructor
  · intro bin
    apply p.owner_eq_anchor_of_label item j
    exact (congrArg Fin.val bin).trans (p.anchor_bin_index j)
  · exact congrArg p.assign

def responsiblePositions (bin : Fin (optBins S)) : List (ResidualPosition S) :=
  ownerGroup p.responsibilityBin p.residualPositions bin

theorem responsiblePositions_nodup (bin : Fin (optBins S)) : (p.responsiblePositions bin).Nodup :=
  p.residualPositions_nodup.filter _

theorem mem_responsiblePositions_iff (bin : Fin (optBins S)) (item : ResidualPosition S) :
    item ∈ p.responsiblePositions bin ↔ p.responsibilityBin item = bin := by
  simp [responsiblePositions, mem_ownerGroup_iff, p.mem_residualPositions]

def responsiblePieces (bin : Fin (optBins S)) : List ℝ :=
  (p.responsiblePositions bin).map residualSize

theorem residualItems_perm_responsiblePieces :
    (residualItems S).Perm (List.ofFn p.responsiblePieces).flatten := by
  rw [p.residualItems_eq_residualPositions]
  exact grouped_occurrences_by_bin_perm p.responsibilityBin p.residualPositions residualSize

end

end BinPacking.Decreasing.AlignedPacking

end

/- PackingCredit.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

open PieceChains

noncomputable section

variable {S : List ℝ} (p : AlignedPacking S)

abbrev largeBins (S : List ℝ) : Finset ℕ := Finset.range (largePrefixItems S).length

def indirectTerminals : Finset (NonLargePosition S) := by
  classical
  exact Finset.univ.filter fun item => ¬isLargeBin S (smallGreedySlot item).1 ∧
    ∃ head, IsDeficit smallGreedySlot p.smallOptimalSlot (isLargeBin S)
      (p.smallOptimalSlot head).1 ∧ (p.smallOptimalSlot head).2 = 2 ∧
      Relation.ReflTransGen p.points head item

def thirdSlotTerminals : Finset (NonLargePosition S) := by
  classical
  exact Finset.univ.filter fun item => ¬isLargeBin S (smallGreedySlot item).1 ∧
    ∃ head witness, (p.smallOptimalSlot witness).2 = 2 ∧
      Relation.TransGen p.points head witness ∧ Relation.ReflTransGen p.points witness item

theorem indirectTerminals_outside (item : ↥p.indirectTerminals) :
    ¬isLargeBin S (smallGreedySlot item.val).1 := by
  classical
  exact (Finset.mem_filter.mp item.property).2.1

theorem thirdSlotTerminals_outside (item : ↥p.thirdSlotTerminals) :
    ¬isLargeBin S (smallGreedySlot item.val).1 := by
  classical
  exact (Finset.mem_filter.mp item.property).2.1

def anchorRoute (bin : ↥(largeBins S)) : Fin (optBins S) :=
  p.anchorBin ⟨bin.val, Finset.mem_range.mp bin.property⟩

def indirectRoute (item : ↥p.indirectTerminals) : Fin (optBins S) :=
  p.responsibilityBin ⟨item.val, p.indirectTerminals_outside item⟩

def thirdSlotRoute (item : ↥p.thirdSlotTerminals) : Fin (optBins S) :=
  p.responsibilityBin ⟨item.val, p.thirdSlotTerminals_outside item⟩

def credit (bin : Fin (optBins S)) : ℝ :=
  firstCredit (IsDeficit smallGreedySlot p.smallOptimalSlot (· ∈ largeBins S)) p.optimalHasB
    p.anchorRoute p.indirectRoute bin + secondCredit p.thirdSlotRoute bin

theorem anchorRoute_injective : Function.Injective p.anchorRoute := by
  intro x y same
  apply Subtype.ext
  have label (bin : ↥(largeBins S)) : (p.anchorRoute bin).val = bin.val :=
    p.anchor_bin_index ⟨bin.val, Finset.mem_range.mp bin.property⟩
  exact (label x).symm.trans ((congrArg Fin.val same).trans (label y))

theorem mem_indirectTerminals_of_anchorOwner (item : ResidualPosition S)
    (j : Fin (largePrefixItems S).length) (owner : p.owner item = anchorIndex j) :
    item.val ∈ p.indirectTerminals := by
  classical
  obtain ⟨head, _, path, direct | ⟨bin, third, _⟩⟩ := p.owner_head_cases item
  · exact ((Nat.not_lt_of_ge head.property)
      ((direct.2.symm.trans owner).symm ▸ j.isLt)).elim
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, item.property, head,
      (congrArg Prod.fst third).symm ▸ bin.property, congrArg Prod.snd third, path⟩

theorem routed_anchorCredit_eq (j : Fin (largePrefixItems S).length) :
    routedCredit p.anchorRoute (fun bin => anchorCredit
      (IsDeficit smallGreedySlot p.smallOptimalSlot (· ∈ largeBins S)) p.optimalHasB bin.val)
      (p.anchorBin j) =
    anchorCredit (IsDeficit smallGreedySlot p.smallOptimalSlot (isLargeBin S)) p.optimalHasB j.val := by
  classical
  let key : ↥(largeBins S) := ⟨j.val, Finset.mem_range.mpr j.isLt⟩
  let _ : DecidablePred (fun bin : ↥(largeBins S) => p.anchorRoute bin = p.anchorBin j) :=
    Classical.decPred _
  unfold routedCredit
  rw [Finset.sum_eq_single key]
  · simp only [Finset.mem_range, key]
  · intro other mem different
    exact (different (p.anchorRoute_injective (Finset.mem_filter.mp mem).2)).elim
  · intro missing
    exact (missing (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)).elim

theorem routed_indirectCredit_eq_count_of_anchor (j : Fin (largePrefixItems S).length) :
    routedCredit p.indirectRoute (fun _ => 1) (p.anchorBin j) =
      ((p.responsiblePositions (p.anchorBin j)).length : ℝ) := by
  classical
  let inBin (item : ↥p.indirectTerminals) := p.indirectRoute item = p.anchorBin j
  let _ : DecidablePred inBin := Classical.decPred _
  let positions := (p.responsiblePositions (p.anchorBin j)).toFinset
  let tag (item : ResidualPosition S) (mem : item ∈ positions) : ↥p.indirectTerminals :=
    ⟨item.val, p.mem_indirectTerminals_of_anchorOwner item j
      ((p.responsibilityBin_eq_anchorBin_iff item j).mp
        ((p.mem_responsiblePositions_iff _ item).mp (List.mem_toFinset.mp mem)))⟩
  have counts : positions.card = (Finset.univ.filter inBin).card := by
    apply Finset.card_bij tag
    · intro item mem
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact (p.mem_responsiblePositions_iff _ item).mp (List.mem_toFinset.mp mem)
    · intro x _ y _ equal
      exact Subtype.ext (congrArg (fun item : ↥p.indirectTerminals => item.val) equal)
    · intro item mem
      let atResidual : ResidualPosition S := ⟨item.val, p.indirectTerminals_outside item⟩
      refine ⟨atResidual, List.mem_toFinset.mpr ((p.mem_responsiblePositions_iff _ _).mpr
        (Finset.mem_filter.mp mem).2), ?_⟩
      exact Subtype.ext rfl
  unfold routedCredit
  change (∑ _ ∈ Finset.univ.filter inBin, (1 : ℝ)) = _
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, ← counts]
  exact_mod_cast List.toFinset_card_of_nodup (p.responsiblePositions_nodup (p.anchorBin j))

theorem sum_credit_le : (∑ bin, p.credit bin) ≤ ((largePrefixItems S).length : ℝ) := by
  classical
  have bound := grouped_slot_credit_le smallGreedySlot p.smallOptimalSlot (largeBins S)
    p.smallOptimalSlot_injective p.optimalHasB p.indirectTerminals p.thirdSlotTerminals
    p.anchorRoute p.indirectRoute p.thirdSlotRoute
  apply le_trans (b := ((largeBins S).card : ℝ))
  · apply bound
    · rintro item (indirect | third)
      · simpa only [Finset.mem_range] using
          p.residual_isTail (p.indirectTerminals_outside ⟨item, indirect⟩)
      · simpa only [Finset.mem_range] using
          p.residual_isTail (p.thirdSlotTerminals_outside ⟨item, third⟩)
    · intro item mem
      simpa only [Finset.mem_range] using (Finset.mem_filter.mp mem).2.2
    · intro item mem
      simpa only [Finset.mem_range] using (Finset.mem_filter.mp mem).2.2
    · intro top inside slot
      exact p.no_optimal_B_of_third ⟨_, Finset.mem_range.mp inside⟩ top (Prod.ext rfl slot)
  · rw [Finset.card_range]

end

end BinPacking.Decreasing.AlignedPacking

end

/- chains/PackingDeficitCounting.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

open PieceChains FirstFitHistory Classical

noncomputable section

variable {S : List ℝ} (p : AlignedPacking S)

instance deficitFintype : Fintype p.Deficit :=
  let e : p.Deficit ↪ Fin (largePrefixItems S).length :=
    ⟨fun d => ⟨d.val, d.property.1⟩, fun _ _ h => Subtype.ext (congrArg Fin.val h)⟩
  Fintype.ofInjective e e.injective

private def incoming (d : p.Deficit) : NonLargePosition S :=
  deficitIncoming smallGreedySlot p.smallOptimalSlot (isLargeBin S) p.deficit_second_occupied d

private theorem incoming_slot (d : p.Deficit) : smallGreedySlot (p.incoming d) = (d.val, 1) :=
  deficitIncoming_slot smallGreedySlot p.smallOptimalSlot (isLargeBin S) p.deficit_second_occupied d

private theorem incoming_injective : Function.Injective p.incoming := fun a b same =>
  Subtype.ext (congrArg Prod.fst ((p.incoming_slot a).symm.trans
    ((congrArg smallGreedySlot same).trans (p.incoming_slot b))))

private theorem incoming_origin (d : p.Deficit) : p.predecessor d = p.origin (p.incoming d) :=
  rfl

private theorem incoming_optimal_bin {d source : p.Deficit} (link : p.predecessor d = .inr source) :
    (p.smallOptimalSlot (p.incoming d)).1 = source.val :=
  (slotOrigin_eq_inr_iff smallGreedySlot p.smallOptimalSlot (isLargeBin S)
    (fun item _ => ordinaryOwner item) (fun bin inside _ => largeOwner bin inside) _ _).mp link

private theorem origin_eq_ordinary {item head : NonLargePosition S}
    (origin : p.origin item = .inl (ordinaryOwner head)) : item = head := by
  unfold AlignedPacking.origin slotOrigin at origin
  split at origin
  · cases origin
  · split at origin
    · rename_i _ inside
      exact ((Nat.not_lt_of_ge head.property) ((congrArg Fin.val (Sum.inl.inj origin)) ▸ inside)).elim
    · exact Subtype.ext (Sum.inl.inj origin)

private theorem no_successor_of_small_incoming (d target : p.Deficit)
    (small : S.get (p.incoming d).val ≤ 1 / 3) (link : p.predecessor target = .inr d) : False :=
  (not_lt_of_ge small) (p.deficit_predecessor_second_large d target (p.incoming target) (p.incoming d)
    (p.incoming_slot target) (p.incoming_optimal_bin link) (p.incoming_slot d))

/-- A non-B ordinary owner directly supplies the second greedy item of each deficit it owns. -/
theorem ordinary_responsible_greedySlot (item : NonLargePosition S) (d : p.Deficit)
    (small : S.get item.val ≤ 1 / 3) (owns : ResponsibleFor p.predecessor (ordinaryOwner item) d) :
    smallGreedySlot item = (d.val, 1) := by
  rcases (responsible_iff_parent_or_grandparent p.predecessor p.predecessor_noThree _ d).mp owns
    with direct | ⟨middle, link, through⟩
  · exact (p.origin_eq_ordinary direct : p.incoming d = item) ▸ p.incoming_slot d
  · exact (p.no_successor_of_small_incoming middle d
      ((p.origin_eq_ordinary through : p.incoming middle = item).symm ▸ small) link).elim

private theorem origin_eq_anchor {item : NonLargePosition S} (j : Fin (largePrefixItems S).length)
    (origin : p.origin item = .inl (largeOwner j.val j.isLt)) :
    (p.smallOptimalSlot item).1 = j.val := by
  unfold AlignedPacking.origin slotOrigin at origin
  split at origin
  · cases origin
  · split at origin
    · exact congrArg Fin.val (Sum.inl.inj origin)
    · exact ((Nat.not_lt_of_ge item.property) ((congrArg Fin.val (Sum.inl.inj origin)).symm ▸ j.isLt)).elim

private theorem card_children_le_of_slots (source : Fin S.length ⊕ p.Deficit) (bin cap : ℕ)
    (slots : ∀ d, p.predecessor d = source → (p.smallOptimalSlot (p.incoming d)).1 = bin ∧
      0 < (p.smallOptimalSlot (p.incoming d)).2 ∧ (p.smallOptimalSlot (p.incoming d)).2 ≤ cap) :
    (deficitChildren p.predecessor source).card ≤ cap := by
  let index (d : ↥(deficitChildren p.predecessor source)) : Fin cap :=
    ⟨(p.smallOptimalSlot (p.incoming d.val)).2 - 1, by
      have bounds := slots d.val ((mem_deficitChildren _ _ _).mp d.property)
      omega⟩
  rw [← Fintype.card_coe (deficitChildren p.predecessor source), ← Fintype.card_fin cap]
  refine Fintype.card_le_of_injective index (fun a b same => ?_)
  have aBounds := slots a.val ((mem_deficitChildren _ _ _).mp a.property)
  have bBounds := slots b.val ((mem_deficitChildren _ _ _).mp b.property)
  exact Subtype.ext (p.incoming_injective (p.smallOptimalSlot_injective
    (Prod.ext (aBounds.1.trans bBounds.1.symm) (by
      have equalIndex := congrArg Fin.val same
      dsimp [index] at equalIndex
      omega))))

private theorem card_deficit_children_le_two (d : p.Deficit) :
    (deficitChildren p.predecessor (.inr d)).card ≤ 2 := by
  exact p.card_children_le_of_slots (.inr d) d.val 2 fun target link =>
    let label := p.incoming_optimal_bin link
    let eligible := p.optimal_small_slot_eligible (p.incoming target) (label.symm ▸ d.property.1)
    ⟨label, by omega, by omega⟩

private theorem card_children_eq_zero_of_incoming_notB (d : p.Deficit)
    (small : S.get (p.incoming d).val ≤ 1 / 3) :
    (deficitChildren p.predecessor (.inr d)).card = 0 := by
  exact Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun target member =>
    p.no_successor_of_small_incoming d target small ((mem_deficitChildren _ _ _).mp member))

private theorem card_ordinary_children_le_one (item : NonLargePosition S) :
    (deficitChildren p.predecessor (.inl (ordinaryOwner item))).card ≤ 1 := by
  exact Finset.card_le_one_iff.mpr fun {a b} ha hb =>
    p.incoming_injective ((p.origin_eq_ordinary ((mem_deficitChildren _ _ _).mp ha) :
      p.incoming a = item).trans
      (p.origin_eq_ordinary ((mem_deficitChildren _ _ _).mp hb) : p.incoming b = item).symm)

private theorem card_anchor_children_le (j : Fin (largePrefixItems S).length) :
    (deficitChildren p.predecessor (.inl (largeOwner j.val j.isLt))).card ≤
      if p.optimalHasB j.val then 1 else 2 := by
  refine p.card_children_le_of_slots (.inl (largeOwner j.val j.isLt)) j.val _ (fun d link => ?_)
  have label := p.origin_eq_anchor j link
  have eligible := p.optimal_small_slot_eligible (p.incoming d) (label.symm ▸ j.isLt)
  exact ⟨label, by omega, by
    split_ifs with hasB
    · have notThird : (p.smallOptimalSlot (p.incoming d)).2 ≠ 2 :=
        fun third => p.no_optimal_B_of_third j (p.incoming d) (Prod.ext label third) hasB
      omega
    · omega⟩

/-- Claim 5.9.11 for an ordinary owner. -/
theorem card_ownedDeficits_ordinary_le (item : NonLargePosition S) :
    (ownedDeficits p.predecessor (ordinaryOwner item)).card ≤
      if (1 / 3 : ℝ) < S.get item.val then 3 else 1 := by
  split_ifs with isB
  · exact card_ownedDeficits_le p.predecessor p.predecessor_noThree (ordinaryOwner item) 1 2
      (p.card_ordinary_children_le_one item) fun d _ => p.card_deficit_children_le_two d
  · exact card_ownedDeficits_le p.predecessor p.predecessor_noThree (ordinaryOwner item) 1 0
      (p.card_ordinary_children_le_one item) fun d link =>
        (p.card_children_eq_zero_of_incoming_notB d
          ((p.origin_eq_ordinary link : p.incoming d = item).symm ▸ le_of_not_gt isB)).le

/-- Claim 5.9.11 for an A-bin owner. -/
theorem card_ownedDeficits_large_le (j : Fin (largePrefixItems S).length) :
    (ownedDeficits p.predecessor (largeOwner j.val j.isLt)).card ≤
      if p.optimalHasB j.val then 3 else 2 := by
  split_ifs with hasB
  · exact card_ownedDeficits_le p.predecessor p.predecessor_noThree (largeOwner j.val j.isLt) 1 2
      (by simpa [hasB] using p.card_anchor_children_le j) fun d _ => p.card_deficit_children_le_two d
  · exact card_ownedDeficits_le p.predecessor p.predecessor_noThree (largeOwner j.val j.isLt) 2 0
      (by simpa [hasB] using p.card_anchor_children_le j) fun d link =>
        (p.card_children_eq_zero_of_incoming_notB d (le_of_not_gt fun large =>
          hasB ⟨p.incoming d, p.origin_eq_anchor j link, large⟩)).le

private theorem incoming_gt_quarter_of_residualC (r : ResidualPosition S)
    (quarter : (1 / 4 : ℝ) < S.get r.val.val) (third : S.get r.val.val ≤ 1 / 3)
    (d : p.Deficit) : (1 / 4 : ℝ) < S.get (p.incoming d).val := by
  by_contra! small
  have earlier : r.val.val.val < (p.incoming d).val.val :=
    lt_of_not_ge fun reversed => (not_lt_of_ge
      (size_le_of_rank_le p.sorted reversed)) (small.trans_lt quarter)
  let j : Fin (largePrefixItems S).length := ⟨d.val, d.property.1⟩
  have incomingBin : binOf ffChoice S (p.incoming d).val = j.val :=
    congrArg Prod.fst (p.incoming_slot d)
  have anchor : [(largePrefixItems S).get j] <+:
      contents S r.val.val.val (binOf ffChoice S (p.incoming d).val) :=
    incomingBin.symm ▸ large_anchor_prefix p.starts (allLarge S) r.val.property j.isLt
  exact r.property ((binOf_lt_before_second r.val.val (p.incoming d).val
    earlier (congrArg Prod.snd (p.incoming_slot d)) _ anchor
    (by linarith only [p.deficit_anchor_space d, third])).trans_le (incomingBin ▸ j.isLt.le))

private theorem card_deficit_children_le_one_of_residualC (r : ResidualPosition S)
    (quarter : (1 / 4 : ℝ) < S.get r.val.val) (third : S.get r.val.val ≤ 1 / 3)
    (d : p.Deficit) : (deficitChildren p.predecessor (.inr d)).card ≤ 1 := by
  refine Finset.card_le_one_iff.mpr (fun {a b} childA childB => ?_)
  by_contra distinct
  let j : Fin (largePrefixItems S).length := ⟨d.val, d.property.1⟩
  have anchorDifferent (x : p.Deficit) : anchorIndex j ≠ (p.incoming x).val :=
    fun same => (Nat.not_lt_of_ge (p.incoming x).property) (same ▸ j.isLt)
  have fits := assignment_triple_sum_le_one p.valid p.assign p.fits (anchorIndex j)
    (p.incoming a).val (p.incoming b).val (anchorDifferent a) (anchorDifferent b)
    (fun same => distinct (p.incoming_injective (Subtype.ext same)))
    (p.assign_eq_anchor_bin j _ (p.incoming_optimal_bin
      ((mem_deficitChildren _ _ _).mp childA)))
    (p.assign_eq_anchor_bin j _ (p.incoming_optimal_bin
      ((mem_deficitChildren _ _ _).mp childB)))
  linarith only [fits, p.anchor_index_large j, p.incoming_gt_quarter_of_residualC r quarter third a,
    p.incoming_gt_quarter_of_residualC r quarter third b]

/-- The responsibility count behind Claim 5.9.15. -/
theorem card_ownedDeficits_ordinary_le_of_residualC (item : NonLargePosition S) (r : ResidualPosition S)
    (quarter : (1 / 4 : ℝ) < S.get r.val.val) (third : S.get r.val.val ≤ 1 / 3) :
    (ownedDeficits p.predecessor (ordinaryOwner item)).card ≤ 2 := by
  exact card_ownedDeficits_le p.predecessor p.predecessor_noThree (ordinaryOwner item) 1 1
    (p.card_ordinary_children_le_one item)
    (fun d _ => p.card_deficit_children_le_one_of_residualC r quarter third d)

end

end BinPacking.Decreasing.AlignedPacking

end

/- chains/PackingTerminalCounting.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

open PieceChains

noncomputable section

variable {S : List ℝ} (p : AlignedPacking S)

private theorem card_residuals_le_ownedDeficits (owner : Fin S.length)
    (items : Finset (ResidualPosition S))
    (witness : ∀ item ∈ items, ∃ (head : NonLargePosition S) (d : p.Deficit),
      p.smallOptimalSlot head = (d.val, 2) ∧ ResponsibleFor p.predecessor owner d ∧
        Relation.ReflTransGen p.points head item.val) :
    items.card ≤ (ownedDeficits p.predecessor owner).card := by
  let pieces := items.map (Function.Embedding.subtype _)
  suffices bound : pieces.card ≤ (ownedDeficits p.predecessor owner).card by
    simpa [pieces] using bound
  exact card_indirect_terminals_le_ownedDeficits smallGreedySlot p.smallOptimalSlot (isLargeBin S)
    p.smallOptimalSlot_injective p.predecessor owner pieces
    (fun _ mem => (Finset.mem_map.mp mem).elim fun item h =>
      (show item.val = _ from h.2) ▸ p.residual_isTail item.property)
    (fun _ mem => (Finset.mem_map.mp mem).elim fun item h =>
      (show item.val = _ from h.2) ▸ witness item h.1)

theorem length_responsiblePositions_anchor_le_ownedDeficits (j : Fin (largePrefixItems S).length) :
    (p.responsiblePositions (p.anchorBin j)).length ≤
      (ownedDeficits p.predecessor (largeOwner j.val j.isLt)).card := by
  classical
  rw [← List.toFinset_card_of_nodup (p.responsiblePositions_nodup (p.anchorBin j))]
  refine p.card_residuals_le_ownedDeficits (largeOwner j.val j.isLt) _ (fun item mem => ?_)
  have owner := (p.responsibilityBin_eq_anchorBin_iff item j).mp
    ((p.mem_responsiblePositions_iff _ item).mp (List.mem_toFinset.mp mem))
  obtain ⟨head, _, path, direct | ⟨deficit, third, owned⟩⟩ := p.owner_head_cases item
  · exact ((Nat.not_lt_of_ge head.property) ((direct.2.symm.trans owner).symm ▸ j.isLt)).elim
  · exact ⟨head, deficit, third, (show p.owner item = largeOwner j.val j.isLt from owner) ▸ owned, path⟩

/-- Residual occurrences assigned indirectly to the ordinary item. -/
def ordinaryIndirectPositions (item : NonLargePosition S) : Finset (ResidualPosition S) := by
  classical
  exact p.residualPositions.toFinset.filter fun r =>
    p.owner r = ordinaryOwner item ∧ r.val ∈ p.indirectTerminals

theorem mem_ordinaryIndirectPositions_iff (item : NonLargePosition S) (r : ResidualPosition S) :
    r ∈ p.ordinaryIndirectPositions item ↔
      p.owner r = ordinaryOwner item ∧ r.val ∈ p.indirectTerminals := by
  simp [ordinaryIndirectPositions, p.mem_residualPositions]

theorem ordinaryIndirectPosition_head (item : NonLargePosition S) (r : ResidualPosition S)
    (mem : r ∈ p.ordinaryIndirectPositions item) :
    ∃ (head : NonLargePosition S) (d : p.Deficit),
      p.smallOptimalSlot head = (d.val, 2) ∧ ResponsibleFor p.predecessor (ordinaryOwner item) d ∧
        Relation.ReflTransGen p.points head r.val := by
  classical
  obtain ⟨owner, indirect⟩ := (p.mem_ordinaryIndirectPositions_iff item r).mp mem
  obtain ⟨head, isHead, path, direct | ⟨deficit, third, owned⟩⟩ := p.owner_head_cases r
  · obtain ⟨other, deficit, third, otherPath⟩ := (Finset.mem_filter.mp indirect).2.2
    have otherHead : IsHead p.points other := fun previous arrow =>
      deficit.2.2 previous (arrow.2.trans (Prod.ext rfl third))
    have same := (slotPoints_existsUnique_head_of_nonA smallGreedySlot p.smallOptimalSlot
      (isLargeBin S) (smallGreedySlot_injective (S := S)) p.smallOptimalSlot_injective
      r.property).unique ⟨isHead, path⟩ ⟨otherHead, otherPath⟩
    exact ((same ▸ direct.1) deficit.1).elim
  · exact ⟨head, deficit, third, owner ▸ owned, path⟩

theorem card_ordinaryIndirectPositions_le_ownedDeficits (item : NonLargePosition S) :
    (p.ordinaryIndirectPositions item).card ≤ (ownedDeficits p.predecessor (ordinaryOwner item)).card :=
  p.card_residuals_le_ownedDeficits (ordinaryOwner item) _ (p.ordinaryIndirectPosition_head item)

/-- Residual occurrences with this ordinary occurrence as their chain head. -/
def ordinaryDirectPositions (item : NonLargePosition S) : Finset (ResidualPosition S) := by
  classical
  exact p.residualPositions.toFinset.filter fun r =>
    p.owner r = ordinaryOwner item ∧ r.val ∉ p.indirectTerminals

theorem mem_ordinaryDirectPositions_iff (item : NonLargePosition S) (r : ResidualPosition S) :
    r ∈ p.ordinaryDirectPositions item ↔
      p.owner r = ordinaryOwner item ∧ r.val ∉ p.indirectTerminals := by
  simp [ordinaryDirectPositions, p.mem_residualPositions]

theorem ordinaryDirectPosition_path (item : NonLargePosition S) (r : ResidualPosition S)
    (mem : r ∈ p.ordinaryDirectPositions item) :
    Relation.ReflTransGen p.points item r.val := by
  classical
  obtain ⟨owner, notIndirect⟩ := (p.mem_ordinaryDirectPositions_iff item r).mp mem
  obtain ⟨head, _, path, direct | ⟨deficit, third, _⟩⟩ := p.owner_head_cases r
  · exact (show head = item from Subtype.ext (direct.2.symm.trans owner)) ▸ path
  · exact (notIndirect (Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.property, head,
      (congrArg Prod.fst third).symm ▸ deficit.property, congrArg Prod.snd third, path⟩)).elim

theorem card_ordinaryDirectPositions_le_one (item : NonLargePosition S) :
    (p.ordinaryDirectPositions item).card ≤ 1 := by
  exact Finset.card_le_one_iff.mpr fun left right => p.residual_eq_of_same_head
    (p.ordinaryDirectPosition_path item _ left) (p.ordinaryDirectPosition_path item _ right)

theorem ordinary_positions_disjoint (item : NonLargePosition S) :
    Disjoint (p.ordinaryDirectPositions item) (p.ordinaryIndirectPositions item) := by
  exact Finset.disjoint_left.mpr fun {r} direct indirect =>
    ((p.mem_ordinaryDirectPositions_iff item r).mp direct).2
      ((p.mem_ordinaryIndirectPositions_iff item r).mp indirect).2

/-- The ordinary cases of Claim 5.9.14. -/
theorem card_ordinaryIndirectPositions_le (item : NonLargePosition S) :
    (p.ordinaryIndirectPositions item).card ≤ if (1 / 3 : ℝ) < S.get item.val then 3 else 1 :=
  (p.card_ordinaryIndirectPositions_le_ownedDeficits item).trans (p.card_ownedDeficits_ordinary_le item)

/-- Claim 5.9.15. A residual C-piece limits the ordinary indirect credit to two. -/
theorem card_ordinaryIndirectPositions_le_of_residualC (item : NonLargePosition S) (r : ResidualPosition S)
    (quarter : (1 / 4 : ℝ) < S.get r.val.val) (third : S.get r.val.val ≤ 1 / 3) :
    (p.ordinaryIndirectPositions item).card ≤ 2 :=
  (p.card_ordinaryIndirectPositions_le_ownedDeficits item).trans
    (p.card_ownedDeficits_ordinary_le_of_residualC item r quarter third)

end

end BinPacking.Decreasing.AlignedPacking

end

/- assembly/ChainSizes.lean -/
section

namespace BinPacking.Decreasing.PieceChains

universe u

variable {Piece : Type u}
variable (greedySlot optimalSlot : Piece → ℕ × ℕ) (largeBins : ℕ)

local notation "Arrow" => slotPoints greedySlot optimalSlot (· < largeBins)
local notation "SecondArrow" => secondSlotPoints greedySlot optimalSlot largeBins

/-- A chain either uses only second-slot arrows, or has a noninitial
third-slot target after which all remaining arrows target second slots. -/
theorem chain_second_suffix
    (eligible : ∀ p : Piece, (optimalSlot p).1 < largeBins →
      (optimalSlot p).2 = 1 ∨ (optimalSlot p).2 = 2)
    {head terminal : Piece} (path : Relation.ReflTransGen Arrow head terminal) :
    Relation.ReflTransGen SecondArrow head terminal ∨
      ∃ third : Piece, (optimalSlot third).1 < largeBins ∧ (optimalSlot third).2 = 2 ∧
        Relation.TransGen Arrow head third ∧ Relation.ReflTransGen SecondArrow third terminal := by
  induction path with
  | refl => exact Or.inl .refl
  | tail preceding step ih =>
      rcases eligible _ step.1 with atSecond | atThird
      · rcases ih with suffix | ⟨third, inside, slot, onPath, suffix⟩
        · exact Or.inl (suffix.tail ⟨step, atSecond⟩)
        · exact Or.inr ⟨third, inside, slot, onPath, suffix.tail ⟨step, atSecond⟩⟩
      · exact Or.inr ⟨_, step.1, atThird, Relation.TransGen.tail' preceding step, .refl⟩

/-- A second-slot suffix ending outside the large bins has nonincreasing
size between its endpoints. -/
theorem terminal_size_le_of_second_slot_path [Finite Piece] (rank : Piece → ℕ) (size : Piece → ℝ)
    (rankInjective : Function.Injective rank) (optimalInjective : Function.Injective optimalSlot)
    (firstFitBefore : ∀ ⦃blocker piece⦄,
      (greedySlot blocker).2 = 1 → (greedySlot blocker).1 < largeBins →
      (optimalSlot piece).1 ≤ (greedySlot blocker).1 → rank piece < rank blocker →
      (greedySlot piece).1 < (greedySlot blocker).1)
    (decreasing : ∀ ⦃a b : Piece⦄, rank a ≤ rank b → size b ≤ size a)
    {first terminal : Piece} (outside : largeBins ≤ (greedySlot terminal).1)
    (suffix : Relation.ReflTransGen SecondArrow first terminal) : size terminal ≤ size first := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp suffix with rfl | positive
  · exact le_rfl
  · exact decreasing (rank_lt_of_secondSlotPath greedySlot optimalSlot largeBins rank
      rankInjective optimalInjective firstFitBefore outside positive).le

/-- Johnson's size lemma on the second-slot suffix gives either the original
head comparison or a third-slot witness for the promotion charge. -/
theorem terminal_size_or_third_slot [Finite Piece] (rank : Piece → ℕ) (size : Piece → ℝ)
    (rankInjective : Function.Injective rank) (optimalInjective : Function.Injective optimalSlot)
    (firstFitBefore : ∀ ⦃blocker piece⦄,
      (greedySlot blocker).2 = 1 → (greedySlot blocker).1 < largeBins →
      (optimalSlot piece).1 ≤ (greedySlot blocker).1 → rank piece < rank blocker →
      (greedySlot piece).1 < (greedySlot blocker).1)
    (eligible : ∀ p : Piece, (optimalSlot p).1 < largeBins →
      (optimalSlot p).2 = 1 ∨ (optimalSlot p).2 = 2)
    (decreasing : ∀ ⦃a b : Piece⦄, rank a ≤ rank b → size b ≤ size a)
    {upper : ℝ} (thirdCap : ∀ p : Piece, (optimalSlot p).1 < largeBins →
      (optimalSlot p).2 = 2 → size p ≤ upper)
    {head terminal : Piece} (outside : largeBins ≤ (greedySlot terminal).1)
    (path : Relation.ReflTransGen Arrow head terminal) :
    (Relation.ReflTransGen SecondArrow head terminal ∧ size terminal ≤ size head) ∨
      ∃ third : Piece, (optimalSlot third).1 < largeBins ∧ (optimalSlot third).2 = 2 ∧
        Relation.TransGen Arrow head third ∧ Relation.ReflTransGen SecondArrow third terminal ∧
        size terminal ≤ size third ∧ size third ≤ upper := by
  have suffix_le {first : Piece} (suffix : Relation.ReflTransGen SecondArrow first terminal) :=
    terminal_size_le_of_second_slot_path greedySlot optimalSlot largeBins rank size rankInjective
      optimalInjective firstFitBefore decreasing outside suffix
  rcases chain_second_suffix greedySlot optimalSlot largeBins eligible path with
      second | ⟨third, inside, slot, onPath, second⟩
  · exact Or.inl ⟨second, suffix_le second⟩
  · exact Or.inr ⟨third, inside, slot, onPath, second, suffix_le second,
      thirdCap third inside slot⟩

end BinPacking.Decreasing.PieceChains

namespace BinPacking.Decreasing

/-- The third item of a feasible ordered triple with a large anchor
has size strictly below `1/4`. -/
theorem optimal_third_size_lt_quarter {anchor second third : ℝ}
    (large : 1 / 2 < anchor) (ordered : third ≤ second)
    (fits : anchor + second + third ≤ 1) : third < 1 / 4 := by
  linarith

/-- The second item in a deficit bin's optimal triple has size strictly
below `7/22` when the third item exceeds `2/11`. -/
theorem deficit_second_size_lt_seven_div_twenty_two {anchor second third : ℝ}
    (large : 1 / 2 < anchor) (threshold : 2 / 11 < third)
    (fits : anchor + second + third ≤ 1) : second < 7 / 22 := by
  linarith

end BinPacking.Decreasing

end

/- assembly/ExceptionalGeometry.lean -/
section

namespace BinPacking.Decreasing.FirstFitHistory

/-- Whenever an item sent outside fits beside an anchor, the second item
of that greedy bin is at least as large as the outside item. -/
theorem residual_size_le_fitting_greedy_second {large S : List ℝ}
    (starts : large <+: S) (hlarge : ∀ a ∈ large, (1 / 2 : ℝ) < a)
    (sorted : S.Pairwise (fun a b => b ≤ a)) (j : Fin large.length)
    (second outside : Fin S.length) (afterLarge : large.length ≤ outside.val)
    (hbin : binOf ffChoice S second = j.val) (hslot : slotOf ffChoice S second = 1)
    (houtside : large.length ≤ binOf ffChoice S outside)
    (fits : large.get j + S.get outside ≤ 1) : S.get outside ≤ S.get second := by
  apply size_le_of_rank_le sorted
  apply le_of_not_gt
  intro earlier
  have anchor : [large.get j] <+: contents S outside.val (binOf ffChoice S second) := by
    rw [hbin]
    exact large_anchor_prefix starts hlarge afterLarge j.isLt
  have left := binOf_lt_before_second outside second earlier hslot (large.get j) anchor fits
  exact not_lt_of_ge houtside (left.trans (hbin.symm ▸ j.isLt))

/-- A residual item larger than the second greedy item could not fit beside
that bin's anchor. -/
theorem greedy_gap_lt_larger_residual {large S : List ℝ}
    (starts : large <+: S) (hlarge : ∀ a ∈ large, (1 / 2 : ℝ) < a)
    (sorted : S.Pairwise (fun a b => b ≤ a)) (j : Fin large.length)
    (second outside : Fin S.length) (afterLarge : large.length ≤ outside.val)
    (hbin : binOf ffChoice S second = j.val) (hslot : slotOf ffChoice S second = 1)
    (houtside : large.length ≤ binOf ffChoice S outside)
    (larger : S.get second < S.get outside) : 1 - large.get j < S.get outside := by
  by_contra tooSmall
  have fits : large.get j + S.get outside ≤ 1 := by linarith
  exact (not_le_of_gt larger) (residual_size_le_fitting_greedy_second starts hlarge sorted j
    second outside afterLarge hbin hslot houtside fits)

/-- The tight BBC deficit gap rules out keeping both the larger C-piece and
the upper D-piece. -/
theorem optimal_companion_demotion_of_BBC_gap {anchor optSecond optThird : ℝ}
    (gap : 1 - anchor < 5 / 12) (fits : anchor + optSecond + optThird ≤ 1) :
    optSecond ≤ 1 / 4 ∨ optThird ≤ 1 / 5 := by
  by_contra keepsBoth
  push Not at keepsBoth
  linarith

/-- The two optimal companions of a deficit anchor fit in strictly less
space than its second greedy item and any candidate at least as large as
the terminal item. -/
theorem optimal_companions_lt_rejected_sum {large S : List ℝ} (starts : large <+: S)
    (hlarge : ∀ a ∈ large, (1 / 2 : ℝ) < a) (j : Fin large.length)
    (second last : Fin S.length) (afterLarge : large.length ≤ second.val)
    (hbin : binOf ffChoice S second = j.val) (hslot : slotOf ffChoice S second = 1)
    (terminal : last.val + 1 = S.length) (lastOutside : large.length ≤ binOf ffChoice S last)
    (hshort : (contents S S.length j.val).length ≤ 2) {candidate lower upper : ℝ}
    (hleast : S.get last ≤ candidate) (fits : large.get j + lower + upper ≤ 1) :
    lower + upper < S.get second + candidate := by
  have rejects := short_large_bin_rejects_third starts hlarge j second last afterLarge hbin
    hslot terminal lastOutside hshort candidate hleast
  linarith

/-- An optimal third item is E-sized when its two companions use at most
two fifths of the capacity beside the anchor. -/
theorem optimal_top_lt_fifth_of_companion_sum {lower upper bound : ℝ}
    (ordered : upper ≤ lower) (companionSum : lower + upper < bound)
    (smallGap : bound ≤ 2 / 5) : upper < 1 / 5 := by
  linarith

/-- A sufficiently large anchor leaves less than two fifths for its ordered
optimal companions. -/
theorem optimal_top_lt_fifth_of_anchor {anchor second third : ℝ}
    (large : 3 / 5 < anchor) (ordered : third ≤ second)
    (fits : anchor + second + third ≤ 1) : third < 1 / 5 := by
  linarith

/-- With a residual B-piece of size at most two fifths, an A-bin whose greedy
second item is smaller than a B-piece has an E-sized optimal third item. -/
theorem optimal_top_lt_fifth_of_small_residual_B {large S : List ℝ}
    (starts : large <+: S) (hlarge : ∀ a ∈ large, (1 / 2 : ℝ) < a)
    (sorted : S.Pairwise (fun a b => b ≤ a)) (j : Fin large.length)
    (second outside : Fin S.length) (afterLarge : large.length ≤ outside.val)
    (hbin : binOf ffChoice S second = j.val) (hslot : slotOf ffChoice S second = 1)
    (houtside : large.length ≤ binOf ffChoice S outside)
    (residualB : (1 / 3 : ℝ) < S.get outside ∧ S.get outside ≤ 2 / 5)
    (secondSmall : S.get second ≤ 1 / 3) {optSecond optThird : ℝ}
    (ordered : optThird ≤ optSecond) (fits : large.get j + optSecond + optThird ≤ 1) :
    optThird < 1 / 5 := by
  apply optimal_top_lt_fifth_of_anchor _ ordered fits
  by_contra smallAnchor
  have candidateFits : large.get j + S.get outside ≤ 1 := by linarith [residualB.2]
  have sizes := residual_size_le_fitting_greedy_second starts hlarge sorted j second outside
    afterLarge hbin hslot houtside candidateFits
  linarith [residualB.1]

/-- A greedy A-bin with a B-piece in its second slot has no third item when
the input is above the large-item cutoff. -/
theorem greedy_large_bin_short_of_B_second {large S : List ℝ}
    (starts : large <+: S) (hlarge : ∀ a ∈ large, (1 / 2 : ℝ) < a) (valid : IsList S)
    (threshold : ∀ a ∈ S, (2 / 11 : ℝ) < a) (j : Fin large.length)
    (second : Fin S.length) (afterLarge : large.length ≤ second.val)
    (hbin : binOf ffChoice S second = j.val) (hslot : slotOf ffChoice S second = 1)
    (secondB : (1 / 3 : ℝ) < S.get second) : (contents S S.length j.val).length ≤ 2 := by
  obtain ⟨rest, together⟩ := large_second_prefix starts hlarge j second afterLarge hbin hslot
    second.isLt
  cases rest with
  | nil => simp [← together]
  | cons third rest =>
      have sizes (a : ℝ) (mem : a ∈ contents S S.length j.val) : (2 / 11 : ℝ) < a :=
        threshold a (List.mem_of_mem_take (contents_subset_take S S.length j.val le_rfl mem))
      have thirdLarge := sizes third (by simp [← together])
      have restNonnegative : 0 ≤ rest.sum :=
        List.sum_nonneg fun a mem => (show (0 : ℝ) ≤ 2 / 11 by norm_num).trans
          (sizes a (by simp [← together, mem])).le
      have capacity := contents_sum_le_one valid S.length j.val le_rfl
      rw [← together] at capacity
      simp only [List.cons_append, List.nil_append, List.sum_cons] at capacity
      linarith [hlarge _ (List.get_mem large j)]

end BinPacking.Decreasing.FirstFitHistory

end

/- assembly/AlignedExceptionalGeometry.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

open FirstFitHistory PieceChains

variable {S : List ℝ} (p : AlignedPacking S)

/-- The optimal second item alongside a third-slot item is at least as
large, and the three items fit together. -/
theorem optimal_second_and_fit_of_third (j : Fin (largePrefixItems S).length)
    (third : NonLargePosition S) (slot : p.smallOptimalSlot third = (j.val, 2)) :
    ∃ second : NonLargePosition S, p.smallOptimalSlot second = (j.val, 1) ∧
      S.get third.val ≤ S.get second.val ∧
      (largePrefixItems S).get j + S.get second.val + S.get third.val ≤ 1 := by
  have thirdBin := p.assign_eq_anchor_bin j third.val (congrArg Prod.fst slot)
  have thirdAt : assignmentSlot p.assign third.val = 2 := congrArg Prod.snd slot
  have thirdSmall : S.get third.val ≤ 1 / 2 := le_of_not_gt fun large =>
    (Nat.not_lt_of_ge third.property) ((largeItem_iff_lt_filter_length p.sorted third.val).mp large)
  obtain ⟨other, same, distinct, _, otherSmall, fits⟩ := exists_small_companion_of_slot_two
    p.valid p.assign p.fits (anchorIndex j) third.val third.val (p.anchor_index_large j)
    thirdSmall thirdBin thirdBin thirdAt
  let second : NonLargePosition S := ⟨other, Nat.le_of_not_lt fun early =>
    (not_lt_of_ge otherSmall) ((largeItem_iff_lt_filter_length p.sorted other).mpr early)⟩
  have secondBin : (p.smallOptimalSlot second).1 = j.val := by
    change (p.assign other).val = j.val
    exact (congrArg Fin.val same).trans (p.anchor_bin_index j)
  have secondAt : (p.smallOptimalSlot second).2 = 1 := by
    rcases p.optimal_small_slot_eligible second (secondBin.symm ▸ j.isLt) with low | high
    · exact low
    · have sameSlot : p.smallOptimalSlot second = p.smallOptimalSlot third :=
        (Prod.ext secondBin high).trans slot.symm
      exact (distinct (congrArg Subtype.val (p.smallOptimalSlot_injective sameSlot))).elim
  let bin := assignmentBin p.assign (p.anchorBin j)
  have thirdIn : 2 < bin.length := by
    simpa only [bin, assignmentBin, List.length_map, thirdBin, thirdAt] using
      assignmentSlot_lt p.assign third.val
  have secondIn : 1 < bin.length := (by decide : 1 < 2).trans thirdIn
  have getSecond : bin[1] = S.get other := by
    have seen := assignmentBin_get_slot p.assign other
    change assignmentSlot p.assign other = 1 at secondAt
    rw [same, secondAt] at seen
    change bin[1]? = some (S.get other) at seen
    rw [List.getElem?_eq_getElem secondIn] at seen
    exact Option.some.inj seen
  have getThird : bin[2] = S.get third.val := by
    have seen := assignmentBin_get_slot p.assign third.val
    rw [thirdBin, thirdAt] at seen
    change bin[2]? = some (S.get third.val) at seen
    rw [List.getElem?_eq_getElem thirdIn] at seen
    exact Option.some.inj seen
  have ordered := (List.pairwise_iff_getElem.mp (assignmentBin_sorted p.assign _ p.sorted))
    1 2 secondIn thirdIn (by decide)
  change bin[2] ≤ bin[1] at ordered
  rw [getThird, getSecond] at ordered
  exact ⟨second, Prod.ext secondBin secondAt, ordered,
    by linarith [p.anchor_index_size j]⟩

/-- Third-slot items in large optimal bins are not bigger than one quarter. -/
theorem optimal_third_lt_quarter (third : NonLargePosition S)
    (inside : isLargeBin S (p.smallOptimalSlot third).1) (slot : (p.smallOptimalSlot third).2 = 2) :
    S.get third.val < 1 / 4 := by
  let j : Fin (largePrefixItems S).length := ⟨(p.smallOptimalSlot third).1, inside⟩
  obtain ⟨second, _, ordered, fits⟩ := p.optimal_second_and_fit_of_third j third (Prod.ext rfl slot)
  exact optimal_third_size_lt_quarter (allLarge S _ (List.get_mem _ j)) ordered fits

private theorem second_suffix_size_le {head terminal : NonLargePosition S}
    (outside : (largePrefixItems S).length ≤ (smallGreedySlot terminal).1)
    (path : Relation.ReflTransGen
      (secondSlotPoints smallGreedySlot p.smallOptimalSlot (largePrefixItems S).length)
      head terminal) : S.get terminal.val ≤ S.get head.val :=
  terminal_size_le_of_second_slot_path smallGreedySlot p.smallOptimalSlot
    (largePrefixItems S).length (fun i => i.val.val) (fun i => S.get i.val)
    (fun _ _ same => Subtype.ext (Fin.ext same))
    p.smallOptimalSlot_injective (fun ⦃_ _⦄ => p.firstFitBefore)
    (fun ⦃_ _⦄ => size_le_of_rank_le p.sorted) outside path

/-- An uncharged terminal is no larger than any earlier item on its chain. -/
theorem uncharged_terminal_size_le {head terminal : NonLargePosition S}
    (outside : (largePrefixItems S).length ≤ (smallGreedySlot terminal).1)
    (uncharged : terminal ∉ p.thirdSlotTerminals)
    (path : Relation.ReflTransGen p.points head terminal) : S.get terminal.val ≤ S.get head.val := by
  classical
  rcases chain_second_suffix smallGreedySlot p.smallOptimalSlot (largePrefixItems S).length
    p.optimal_small_slot_eligible path with after | ⟨witness, _, atThird, reached, after⟩
  · exact p.second_suffix_size_le outside after
  · apply (uncharged _).elim
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.not_lt_of_ge outside,
      head, witness, atThird, reached, ?_⟩
    exact Relation.ReflTransGen.mono (fun _ _ step => step.1) _ _ after

/-- Every terminal is no larger than the greater of its head and one quarter. -/
theorem terminal_size_le_max_head_quarter {head terminal : NonLargePosition S}
    (outside : (largePrefixItems S).length ≤ (smallGreedySlot terminal).1)
    (path : Relation.ReflTransGen p.points head terminal) :
    S.get terminal.val ≤ max (S.get head.val) (1 / 4) := by
  rcases chain_second_suffix smallGreedySlot p.smallOptimalSlot (largePrefixItems S).length
    p.optimal_small_slot_eligible path with after | ⟨witness, inside, atThird, _, after⟩
  · exact (p.second_suffix_size_le outside after).trans (le_max_left _ _)
  · exact (p.second_suffix_size_le outside after).trans
      ((p.optimal_third_lt_quarter witness inside atThird).le.trans (le_max_right _ _))

/-- The ordered optimal companions of a deficit bin use less space than
the bin's second greedy item and a residual candidate. -/
theorem deficit_companion_sum_lt_rejected {d : p.Deficit} {greedySecond optSecond optThird : NonLargePosition S}
    (slot : smallGreedySlot greedySecond = (d.val, 1))
    (candidate : Fin S.length)
    (fits : (largePrefixItems S).get ⟨d.val, d.property.1⟩ +
      S.get optSecond.val + S.get optThird.val ≤ 1) :
    S.get optSecond.val + S.get optThird.val < S.get greedySecond.val + S.get candidate :=
  optimal_companions_lt_rejected_sum p.starts (allLarge S) ⟨d.val, d.property.1⟩
    greedySecond.val p.last greedySecond.property (congrArg Prod.fst slot) (congrArg Prod.snd slot)
    p.terminal p.lastOutside (p.deficit_greedy_short d) (p.last_size_le candidate) fits

/-- Every residual C-piece fits beside a deficit anchor and so is no larger
than that bin's second greedy item. -/
theorem residual_size_le_deficit_second {d : p.Deficit} {greedySecond : NonLargePosition S}
    (slot : smallGreedySlot greedySecond = (d.val, 1)) (candidate : ResidualPosition S)
    (candidateSmall : S.get candidate.val.val ≤ 1 / 3) :
    S.get candidate.val.val ≤ S.get greedySecond.val := by
  exact residual_size_le_fitting_greedy_second p.starts (allLarge S) p.sorted
    ⟨d.val, d.property.1⟩ greedySecond.val candidate.val.val candidate.val.property
    (congrArg Prod.fst slot) (congrArg Prod.snd slot) (Nat.le_of_not_gt candidate.property)
    (by linarith [p.deficit_anchor_space d])

/-- The tight-gap subcase in Case II. With a candidate that fits beside the
greedy second within two fifths, an uncharged indirect terminal is E-sized. -/
theorem uncharged_deficit_terminal_lt_fifth {d : p.Deficit}
    {greedySecond head terminal : NonLargePosition S} (candidate : Fin S.length)
    (headThird : p.smallOptimalSlot head = (d.val, 2))
    (greedySecondAt : smallGreedySlot greedySecond = (d.val, 1))
    (smallGap : S.get greedySecond.val + S.get candidate ≤ 2 / 5)
    (terminalOutside : (largePrefixItems S).length ≤ (smallGreedySlot terminal).1)
    (uncharged : terminal ∉ p.thirdSlotTerminals)
    (path : Relation.ReflTransGen p.points head terminal) : S.get terminal.val < 1 / 5 := by
  obtain ⟨_, _, ordered, fits⟩ := p.optimal_second_and_fit_of_third ⟨d.val, d.property.1⟩
    head headThird
  have smaller := p.deficit_companion_sum_lt_rejected greedySecondAt candidate fits
  exact (p.uncharged_terminal_size_le terminalOutside uncharged path).trans_lt
    (optimal_top_lt_fifth_of_companion_sum ordered smaller smallGap)

private theorem uncharged_deficit_companions_bound {d : p.Deficit}
    {greedySecond optThird direct indirect : NonLargePosition S}
    (greedySecondAt : smallGreedySlot greedySecond = (d.val, 1))
    (optThirdAt : p.smallOptimalSlot optThird = (d.val, 2))
    (directOutside : (largePrefixItems S).length ≤ (smallGreedySlot direct).1)
    (indirectOutside : (largePrefixItems S).length ≤ (smallGreedySlot indirect).1)
    (directUncharged : direct ∉ p.thirdSlotTerminals) (indirectUncharged : indirect ∉ p.thirdSlotTerminals)
    (directPath : Relation.ReflTransGen p.points greedySecond direct)
    (indirectPath : Relation.ReflTransGen p.points optThird indirect) :
    ∃ optSecond : NonLargePosition S, S.get direct.val ≤ S.get optSecond.val ∧
      S.get indirect.val ≤ S.get optThird.val ∧
      (largePrefixItems S).get ⟨d.val, d.property.1⟩ +
        S.get optSecond.val + S.get optThird.val ≤ 1 := by
  obtain ⟨optSecond, optSecondAt, _, fits⟩ := p.optimal_second_and_fit_of_third
    ⟨d.val, d.property.1⟩ optThird optThirdAt
  have hasFirst : greedySecond ≠ direct := by
    intro same
    exact Nat.not_lt_of_ge directOutside (same ▸ ((congrArg Prod.fst greedySecondAt).symm ▸ d.property.1))
  obtain ⟨next, arrow, path⟩ := directPath.cases_head.resolve_left hasFirst
  have sameNext : next = optSecond := p.smallOptimalSlot_injective
    (arrow.2.symm.trans (greedySecondAt.trans optSecondAt.symm))
  exact ⟨optSecond, p.uncharged_terminal_size_le directOutside directUncharged (sameNext ▸ path),
    p.uncharged_terminal_size_le indirectOutside indirectUncharged indirectPath, fits⟩

/-- The second discount in saturated CCCD uses the two terminal items of the
same deficit bin. Their combined size is below the rejected pair. -/
theorem uncharged_deficit_terminal_sum_lt_rejected {d : p.Deficit}
    {greedySecond optThird direct indirect : NonLargePosition S} (candidate : Fin S.length)
    (greedySecondAt : smallGreedySlot greedySecond = (d.val, 1))
    (optThirdAt : p.smallOptimalSlot optThird = (d.val, 2))
    (directOutside : (largePrefixItems S).length ≤ (smallGreedySlot direct).1)
    (indirectOutside : (largePrefixItems S).length ≤ (smallGreedySlot indirect).1)
    (directUncharged : direct ∉ p.thirdSlotTerminals) (indirectUncharged : indirect ∉ p.thirdSlotTerminals)
    (directPath : Relation.ReflTransGen p.points greedySecond direct)
    (indirectPath : Relation.ReflTransGen p.points optThird indirect) :
    S.get direct.val + S.get indirect.val < S.get greedySecond.val + S.get candidate := by
  obtain ⟨_, directSize, indirectSize, fits⟩ := p.uncharged_deficit_companions_bound greedySecondAt
    optThirdAt directOutside indirectOutside directUncharged indirectUncharged directPath indirectPath
  exact (add_le_add directSize indirectSize).trans_lt
    (p.deficit_companion_sum_lt_rejected greedySecondAt candidate fits)

/-- In BBC the retained B terminal forces either the direct companion or
the indirect companion of the C owner into a lighter size class. -/
theorem uncharged_BBC_companions_demoted {d : p.Deficit}
    {greedySecond optThird direct indirect : NonLargePosition S} (residualB : ResidualPosition S)
    (residualSmallB : (1 / 3 : ℝ) < S.get residualB.val.val ∧ S.get residualB.val.val < 5 / 12)
    (greedySecondSmall : S.get greedySecond.val ≤ 1 / 3)
    (greedySecondAt : smallGreedySlot greedySecond = (d.val, 1))
    (optThirdAt : p.smallOptimalSlot optThird = (d.val, 2))
    (directOutside : (largePrefixItems S).length ≤ (smallGreedySlot direct).1)
    (indirectOutside : (largePrefixItems S).length ≤ (smallGreedySlot indirect).1)
    (directUncharged : direct ∉ p.thirdSlotTerminals) (indirectUncharged : indirect ∉ p.thirdSlotTerminals)
    (directPath : Relation.ReflTransGen p.points greedySecond direct)
    (indirectPath : Relation.ReflTransGen p.points optThird indirect) :
    S.get direct.val ≤ 1 / 4 ∨ S.get indirect.val ≤ 1 / 5 := by
  obtain ⟨_, directSize, indirectSize, fits⟩ := p.uncharged_deficit_companions_bound greedySecondAt
    optThirdAt directOutside indirectOutside directUncharged indirectUncharged directPath indirectPath
  have gap := greedy_gap_lt_larger_residual p.starts (allLarge S) p.sorted ⟨d.val, d.property.1⟩
    greedySecond.val residualB.val.val residualB.val.property (congrArg Prod.fst greedySecondAt)
    (congrArg Prod.snd greedySecondAt) (Nat.le_of_not_gt residualB.property)
    (greedySecondSmall.trans_lt residualSmallB.1)
  rcases optimal_companion_demotion_of_BBC_gap (gap.trans residualSmallB.2) fits with demote | demote
  · exact Or.inl (directSize.trans demote)
  · exact Or.inr (indirectSize.trans demote)

private theorem optimal_third_lt_fifth_of_residual_B {j : Fin (largePrefixItems S).length}
    (optThird greedySecond residualB : NonLargePosition S)
    (optimalThird : p.smallOptimalSlot optThird = (j.val, 2))
    (greedySecondAt : smallGreedySlot greedySecond = (j.val, 1))
    (residualOutside : (largePrefixItems S).length ≤ (smallGreedySlot residualB).1)
    (smallB : (1 / 3 : ℝ) < S.get residualB.val ∧ S.get residualB.val ≤ 2 / 5)
    (secondSmall : S.get greedySecond.val ≤ 1 / 3) : S.get optThird.val < 1 / 5 := by
  obtain ⟨_, _, ordered, fits⟩ := p.optimal_second_and_fit_of_third j optThird optimalThird
  exact optimal_top_lt_fifth_of_small_residual_B p.starts (allLarge S) p.sorted j
    greedySecond.val residualB.val residualB.property (congrArg Prod.fst greedySecondAt)
    (congrArg Prod.snd greedySecondAt) residualOutside smallB secondSmall ordered fits

include p in
private theorem exists_small_greedy_second_of_third {j : Fin (largePrefixItems S).length}
    (third : NonLargePosition S) (thirdAt : smallGreedySlot third = (j.val, 2)) :
    ∃ second : NonLargePosition S, smallGreedySlot second = (j.val, 1) ∧ S.get second.val ≤ 1 / 3 := by
  have thirdBin : binOf ffChoice S third.val = j.val := congrArg Prod.fst thirdAt
  have before : (contents S third.val.val j.val).length = 2 := by
    have slot : slotOf ffChoice S third.val = 2 := congrArg Prod.snd thirdAt
    simpa only [slotOf, contents, thirdBin] using slot
  have next : (contents S (third.val.val + 1) j.val).length = 3 := by
    rw [contents_succ, if_pos thirdBin.symm]
    simp [before]
  have enough : 3 ≤ (contents S S.length j.val).length := next ▸
    (contents_prefix S (b := j.val) (Nat.succ_le_of_lt third.val.isLt)).length_le
  obtain ⟨second, slot⟩ := p.nonLarge_at_greedy_slot j.val 1 (by decide) (by omega)
  refine ⟨second, slot, le_of_not_gt fun secondB => ?_⟩
  have short := greedy_large_bin_short_of_B_second p.starts (allLarge S) p.valid p.threshold j
    second.val second.property (congrArg Prod.fst slot) (congrArg Prod.snd slot) secondB
  omega

/-- Claim 5.9.20 for a chain headed at the optimal top of a deficit bin
whose second greedy item is at most one third. A small residual B-piece
forces the terminal item to be E-sized. -/
theorem terminal_lt_fifth_of_small_residual_B
    (residualB head terminal : NonLargePosition S)
    (residualOutside : (largePrefixItems S).length ≤ (smallGreedySlot residualB).1)
    (smallB : (1 / 3 : ℝ) < S.get residualB.val ∧ S.get residualB.val ≤ 2 / 5)
    (j : Fin (largePrefixItems S).length) (greedySecond : NonLargePosition S)
    (headThird : p.smallOptimalSlot head = (j.val, 2))
    (secondAt : smallGreedySlot greedySecond = (j.val, 1))
    (secondSmall : S.get greedySecond.val ≤ 1 / 3)
    (terminalOutside : (largePrefixItems S).length ≤ (smallGreedySlot terminal).1)
    (path : Relation.ReflTransGen (slotPoints smallGreedySlot p.smallOptimalSlot (isLargeBin S))
      head terminal) : S.get terminal.val < 1 / 5 := by
  rcases chain_second_suffix smallGreedySlot p.smallOptimalSlot (largePrefixItems S).length
    p.optimal_small_slot_eligible path with after | ⟨witness, inLarge, atThird, reached, after⟩
  · exact (p.second_suffix_size_le terminalOutside after).trans_lt
      (p.optimal_third_lt_fifth_of_residual_B head greedySecond residualB headThird secondAt
        residualOutside smallB secondSmall)
  · obtain ⟨previous, _, arrow⟩ := Relation.TransGen.tail'_iff.mp reached
    let witnessBin : Fin (largePrefixItems S).length := ⟨(p.smallOptimalSlot witness).1, inLarge⟩
    have witnessAt : p.smallOptimalSlot witness = (witnessBin.val, 2) := Prod.ext rfl atThird
    obtain ⟨second, binSlot, small⟩ := p.exists_small_greedy_second_of_third previous
      (arrow.2.trans witnessAt)
    exact (p.second_suffix_size_le terminalOutside after).trans_lt
      (p.optimal_third_lt_fifth_of_residual_B witness second residualB witnessAt binSlot
        residualOutside smallB small)

end BinPacking.Decreasing.AlignedPacking

end

/- small-only/OrdinaryGeometry.lean -/
section

set_option autoImplicit false

namespace BinPacking.Decreasing.AlignedPacking

open PieceChains

variable {S : List ℝ} (p : AlignedPacking S)

private theorem ordinary_greedySlot_of_parent (item : NonLargePosition S) (d : p.Deficit)
    (parent : p.predecessor d = .inl (ordinaryOwner item)) :
    smallGreedySlot item = (d.val, 1) := by
  let incoming := deficitIncoming smallGreedySlot p.smallOptimalSlot (isLargeBin S) p.deficit_second_occupied d
  suffices same : incoming = item from same ▸ deficitIncoming_slot smallGreedySlot
    p.smallOptimalSlot (isLargeBin S) p.deficit_second_occupied d
  change p.origin incoming = .inl (ordinaryOwner item) at parent
  unfold AlignedPacking.origin slotOrigin at parent
  split at parent
  · cases parent
  · split at parent
    next inside =>
      exact ((Nat.not_lt_of_ge item.property) ((congrArg Fin.val (Sum.inl.inj parent)) ▸ inside)).elim
    next outside =>
      exact Subtype.ext (Sum.inl.inj parent)

/-- An ordinary owner of an indirect terminal first reaches a deficit bin as
its second greedy item. This holds even if that terminal is charged through
a second deficit bin. -/
theorem ordinary_first_deficit_of_indirect (item : NonLargePosition S)
    {indirect : ResidualPosition S} (mem : indirect ∈ p.ordinaryIndirectPositions item) :
    ∃ d : p.Deficit, p.predecessor d = .inl (ordinaryOwner item) ∧
      smallGreedySlot item = (d.val, 1) := by
  have positive : 0 < (ownedDeficits p.predecessor (ordinaryOwner item)).card :=
    (Finset.card_pos.mpr ⟨indirect, mem⟩).trans_le (p.card_ordinaryIndirectPositions_le_ownedDeficits item)
  obtain ⟨d, hd⟩ := Finset.card_pos.mp positive
  rcases (responsible_iff_parent_or_grandparent p.predecessor p.predecessor_noThree _ d).mp
    ((mem_ownedDeficits _ _ _).mp hd) with parent | ⟨first, _, parent⟩
  all_goals exact ⟨_, parent, p.ordinary_greedySlot_of_parent item _ parent⟩

/-- An ordinary owner with indirect credit points to the optimal occupant
of a deficit bin's second slot. That occupant lies below `7/22`. -/
theorem ordinary_first_arrow_of_indirect (item : NonLargePosition S)
    {indirect : ResidualPosition S} (hIndirect : indirect ∈ p.ordinaryIndirectPositions item) :
    ∃ (d : p.Deficit) (second : NonLargePosition S), smallGreedySlot item = (d.val, 1) ∧
      p.smallOptimalSlot second = (d.val, 1) ∧ p.points item second ∧
      S.get second.val < (7 / 22 : ℝ) := by
  obtain ⟨d, _, greedySlot⟩ := p.ordinary_first_deficit_of_indirect item hIndirect
  obtain ⟨third, thirdAt⟩ := d.property.2.1
  obtain ⟨second, secondAt, _, fits⟩ :=
    p.optimal_second_and_fit_of_third ⟨d.val, d.property.1⟩ third thirdAt
  exact ⟨d, second, greedySlot, secondAt,
    ⟨(congrArg Prod.fst secondAt).symm ▸ d.property.1, greedySlot.trans secondAt.symm⟩,
    deficit_second_size_lt_seven_div_twenty_two
      (allLarge S _ (List.get_mem _ ⟨d.val, d.property.1⟩))
      (p.threshold _ (List.get_mem S third.val)) fits⟩

/-- The direct terminal's chain continues from the optimal second occupant
of the first deficit bin reached by its ordinary owner. -/
theorem ordinary_direct_first_second_of_indirect (item : NonLargePosition S)
    {direct indirect : ResidualPosition S} (hDirect : direct ∈ p.ordinaryDirectPositions item)
    (hIndirect : indirect ∈ p.ordinaryIndirectPositions item) :
    ∃ (d : p.Deficit) (second : NonLargePosition S), p.smallOptimalSlot second = (d.val, 1) ∧
      p.points item second ∧ Relation.ReflTransGen p.points second direct.val ∧
      S.get second.val < (7 / 22 : ℝ) := by
  obtain ⟨d, second, greedySlot, secondAt, firstArrow, small⟩ :=
    p.ordinary_first_arrow_of_indirect item hIndirect
  have different : item ≠ direct.val := fun same =>
    direct.property ((congrArg Prod.fst (same ▸ greedySlot)).symm ▸ d.property.1)
  obtain ⟨next, arrow, rest⟩ :=
    (p.ordinaryDirectPosition_path item direct hDirect).cases_head.resolve_left different
  have same := p.smallOptimalSlot_injective (arrow.2.symm.trans firstArrow.2)
  exact ⟨d, second, secondAt, firstArrow, same ▸ rest, small⟩

/-- Claim 5.9.17. A direct terminal is bounded by its owner's size or one
quarter, whichever is larger. -/
theorem ordinary_direct_le_max_owner_quarter (item : NonLargePosition S)
    {direct : ResidualPosition S} (mem : direct ∈ p.ordinaryDirectPositions item) :
    S.get direct.val.val ≤ max (S.get item.val) (1 / 4) :=
  p.terminal_size_le_max_head_quarter (Nat.le_of_not_gt direct.property)
    (p.ordinaryDirectPosition_path item direct mem)

/-- An uncharged direct terminal is no larger than its owner. -/
theorem ordinary_direct_le_owner_of_uncharged (item : NonLargePosition S)
    {direct : ResidualPosition S} (mem : direct ∈ p.ordinaryDirectPositions item)
    (uncharged : direct.val ∉ p.thirdSlotTerminals) : S.get direct.val.val ≤ S.get item.val :=
  p.uncharged_terminal_size_le (Nat.le_of_not_gt direct.property) uncharged
    (p.ordinaryDirectPosition_path item direct mem)

/-- Claim 5.9.18. An ordinary owner with an indirect terminal cannot have a
B-sized direct terminal. -/
theorem ordinary_direct_lt_third_of_indirect (item : NonLargePosition S)
    {direct indirect : ResidualPosition S} (hDirect : direct ∈ p.ordinaryDirectPositions item)
    (hIndirect : indirect ∈ p.ordinaryIndirectPositions item) : S.get direct.val.val < (1 / 3 : ℝ) := by
  obtain ⟨_, second, _, _, path, small⟩ := p.ordinary_direct_first_second_of_indirect item hDirect hIndirect
  refine (p.terminal_size_le_max_head_quarter (Nat.le_of_not_gt direct.property) path).trans_lt ?_
  exact max_lt (small.trans (by norm_num)) (by norm_num)

/-- An ordinary owner with any indirect terminal is at least as large as each
residual C- or D-piece, since it fills the second greedy slot of a deficit. -/
theorem residual_size_le_ordinary_of_indirect (item : NonLargePosition S)
    {indirect : ResidualPosition S} (hIndirect : indirect ∈ p.ordinaryIndirectPositions item)
    (candidate : ResidualPosition S) (small : S.get candidate.val.val ≤ 1 / 3) :
    S.get candidate.val.val ≤ S.get item.val := by
  obtain ⟨d, _, slot⟩ := p.ordinary_first_deficit_of_indirect item hIndirect
  exact p.residual_size_le_deficit_second (d := d) slot candidate small

/-- A residual item of size at most one third rules out indirect terminals
for any smaller ordinary owner. -/
theorem ordinary_indirect_empty_of_smaller_than_residual (item : NonLargePosition S)
    (candidate : ResidualPosition S) (small : S.get candidate.val.val ≤ 1 / 3)
    (smaller : S.get item.val < S.get candidate.val.val) :
    p.ordinaryIndirectPositions item = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun _ hIndirect => ?_
  exact (not_lt_of_ge (p.residual_size_le_ordinary_of_indirect item hIndirect candidate small)) smaller

/-- In either case of the weight argument, an E-piece has no indirect terminals. -/
theorem ordinary_indirect_empty_of_residualCD (item : NonLargePosition S)
    (candidate : ResidualPosition S) (fifth : (1 / 5 : ℝ) < S.get candidate.val.val)
    (third : S.get candidate.val.val ≤ 1 / 3) (small : S.get item.val ≤ 1 / 5) :
    p.ordinaryIndirectPositions item = ∅ :=
  p.ordinary_indirect_empty_of_smaller_than_residual item candidate third (small.trans_lt fifth)

/-- In Case I, a residual C-piece rules out indirect terminals for D- and E-owners. -/
theorem ordinary_indirect_empty_of_residualC (item : NonLargePosition S)
    (candidate : ResidualPosition S) (quarter : (1 / 4 : ℝ) < S.get candidate.val.val)
    (third : S.get candidate.val.val ≤ 1 / 3) (small : S.get item.val ≤ 1 / 4) :
    p.ordinaryIndirectPositions item = ∅ :=
  p.ordinary_indirect_empty_of_smaller_than_residual item candidate third (small.trans_lt quarter)

end BinPacking.Decreasing.AlignedPacking

end

/- assembly/BinWeight.lean -/
section

namespace BinPacking.Decreasing

/-- The weight from the all-singletons partition is a valid upper bound. -/
theorem weight_le_singleton_sum (pieces : List ℝ) : W pieces ≤ (pieces.map w1).sum := by
  calc
    W pieces ≤ w12 (sortDesc pieces) id := Finset.inf'_le _ (by simp [partitions])
    _ = ((sortDesc pieces).map w1).sum := by simp [w12]
    _ = _ := ((List.mergeSort_perm _ _).map w1).sum_eq

/-- The two-item bin may use the paper's discounted pair weight. -/
theorem weight_pair_le (x y : ℝ) (hxy : y ≤ x) : W [x, y] ≤ w2 x y := by
  have hsorted : sortDesc [x, y] = [x, y] := by
    simp [sortDesc, List.mergeSort, hxy]
  let swap : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0
  have hswap : swap ∈ partitions 2 := by decide
  calc
    W [x, y] = (partitions 2).inf' ⟨id, by simp [partitions]⟩ (w12 [x, y]) :=
      congrArg (fun S : List ℝ =>
        (partitions S.length).inf' ⟨id, by simp [partitions]⟩ (w12 S)) hsorted
    _ ≤ w12 [x, y] swap := Finset.inf'_le _ hswap
    _ = w2 x y := by
      simp [w12, Fin.sum_univ_two, swap]

/-- Demoting neither item within the bound for its original size preserves a
discount when the first direct piece retains the original piece number. -/
theorem weight_pair_le_of_preserved_relation
    (x y directX directY : ℝ)
    (hrel : ObeysRelation x y)
    (hsame : pieceNum directX = pieceNum x)
    (hnum : 0 ≤ (pieceNum x : ℝ))
    (hleft : directX ≤ x)
    (hright : directY ≤ y)
    (horder : directY ≤ directX) :
    W [directX, directY] ≤
      w1 directX + ((pieceNum x : ℝ) - 1) / (pieceNum x : ℝ) * w1 directY := by
  have hrel' : ObeysRelation directX directY := by
    change (pieceNum directX : ℝ) * directX + directY ≤ 1
    rw [hsame]
    exact (add_le_add (mul_le_mul_of_nonneg_left hleft hnum) hright).trans hrel
  simpa only [w2, if_pos hrel', hsame] using weight_pair_le directX directY horder

theorem w1_le_inverse_of_le {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 0 < k)
    (hle : x ≤ 1 / (k : ℝ)) : w1 x ≤ 1 / (k : ℝ) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hdiv : (k : ℝ) ≤ 1 / x := (le_div_iff₀ hx).2 (by
    simpa only [mul_comm] using (le_div_iff₀ hk').1 hle)
  have hfloor : (k : ℤ) ≤ pieceNum x := Int.le_floor.mpr (by exact_mod_cast hdiv)
  have hcast : (k : ℝ) ≤ (pieceNum x : ℝ) := by exact_mod_cast hfloor
  simpa only [w1, one_div] using
    (inv_le_inv₀ (a := (pieceNum x : ℝ)) (b := (k : ℝ)) (by linarith) hk').mpr hcast

private theorem weight_le_length_quarter (pieces : List ℝ)
    (hpieces : ∀ x ∈ pieces, 0 < x ∧ x ≤ 1 / 4) :
    W pieces ≤ (pieces.length : ℝ) / 4 := by
  have hsingleton : W pieces ≤ w12 (sortDesc pieces) id :=
    Finset.inf'_le _ (by simp [partitions])
  simp only [w12, id, eq_self, if_true] at hsingleton
  refine hsingleton.trans ?_
  calc
    _ ≤ ∑ _i : Fin (sortDesc pieces).length, (1 / 4 : ℝ) := by
      apply Finset.sum_le_sum
      exact fun i _ =>
        let h := hpieces _ (List.mem_mergeSort.mp (List.get_mem (sortDesc pieces) i))
        w1_le_inverse_of_le h.1 (k := 4) (by decide) (by simpa using h.2)
    _ = (pieces.length : ℝ) / 4 := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      simp [sortDesc, div_eq_mul_inv]

/-- Johnson's Claim 5.9.21 for a bin containing an item larger than one half.
The four credit cases give enough weight for pieces of size at most one quarter. -/
theorem large_bin_responsibility_bound (pieces : List ℝ) (credit₁ credit₂ : ℝ)
    (hpieces : ∀ x ∈ pieces, 0 < x ∧ x ≤ 1 / 4)
    (hcredit₂ : 0 ≤ credit₂)
    (hcases :
      (pieces.length = 0 ∧ 0 ≤ credit₁) ∨
      (pieces.length = 1 ∧ 4 / 3 ≤ credit₁) ∨
      (pieces.length = 2 ∧ 7 / 3 ≤ credit₁) ∨
      (pieces.length = 3 ∧ 4 ≤ credit₁)) :
    W pieces + (credit₁ + credit₂) ≤ 11 / 9 * (credit₁ + credit₂) := by
  have hw := weight_le_length_quarter pieces hpieces
  rcases hcases with ⟨hlen, hc⟩ | ⟨hlen, hc⟩ | ⟨hlen, hc⟩ | ⟨hlen, hc⟩ <;>
    rw [hlen] at hw <;> linarith

/-- Johnson's Claim 5.9.22. Singleton estimates suffice when their total, after
subtracting the collaboration credit, is at most `11/9`. -/
theorem nonLarge_bin_bound_of_singleton_costs {n : ℕ} (pieces : Fin n → List ℝ)
    (credit allowance : Fin n → ℝ)
    (hpiece : ∀ i, ((pieces i).map w1).sum - 2 / 9 * credit i ≤ allowance i)
    (hbudget : ∑ i, allowance i ≤ 11 / 9) :
    W (List.ofFn pieces).flatten + ∑ i, credit i ≤ 11 / 9 * (1 + ∑ i, credit i) := by
  have hweight := weight_le_singleton_sum (List.ofFn pieces).flatten
  rw [List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn, List.sum_ofFn] at hweight
  simp only [Function.comp_apply] at hweight
  have htotal := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpiece i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at htotal
  linarith [hweight, htotal.trans hbudget]

end BinPacking.Decreasing

end

/- OrdinaryDirectWeights.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

open PieceChains

noncomputable section

variable {S : List ℝ} (p : AlignedPacking S)

def HasResidualC (S : List ℝ) : Prop :=
  ∃ r : ResidualPosition S, (1 / 4 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3

include p in
theorem ordinary_size_le_half (i : NonLargePosition S) : S.get i.val ≤ 1 / 2 :=
  le_of_not_gt fun large => (Nat.not_lt_of_ge i.property)
    ((largeItem_iff_lt_filter_length p.sorted i.val).mp large)

theorem residual_size_le_quarter_of_le_third (noC : ¬HasResidualC S) (r : ResidualPosition S)
    (small : residualSize r ≤ 1 / 3) : residualSize r ≤ 1 / 4 :=
  le_of_not_gt fun large => noC ⟨r, large, small⟩

/-- The sole direct terminal, when the ordinary owner's chain reaches the residual input. -/
def ordinaryDirect (item : NonLargePosition S) : Option (ResidualPosition S) := by
  classical
  exact if occupied : (p.ordinaryDirectPositions item).Nonempty then some occupied.choose else none

theorem ordinaryDirect_eq_some_iff (item : NonLargePosition S) (r : ResidualPosition S) :
    p.ordinaryDirect item = some r ↔ r ∈ p.ordinaryDirectPositions item := by
  classical
  by_cases occupied : (p.ordinaryDirectPositions item).Nonempty
  · rw [ordinaryDirect, dif_pos occupied, Option.some.injEq]
    exact ⟨fun equal => equal ▸ occupied.choose_spec, fun mem =>
      Finset.card_le_one_iff.mp (p.card_ordinaryDirectPositions_le_one item) occupied.choose_spec mem⟩
  · rw [ordinaryDirect, dif_neg occupied]
    constructor
    · intro equal
      cases equal
    · exact fun mem => (occupied ⟨r, mem⟩).elim

def ordinaryDirectWeight (item : NonLargePosition S) : ℝ :=
  ((p.ordinaryDirect item).map (fun r => w1 (residualSize r))).getD 0

def ordinaryIndirectWeight (item : NonLargePosition S) : ℝ :=
  ∑ r ∈ p.ordinaryIndirectPositions item, w1 (residualSize r)

theorem ordinaryDirectWeight_eq_sum (item : NonLargePosition S) :
    p.ordinaryDirectWeight item = ∑ r ∈ p.ordinaryDirectPositions item, w1 (residualSize r) := by
  classical
  cases observed : p.ordinaryDirect item with
  | none =>
    have empty : p.ordinaryDirectPositions item = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro r mem
      have impossible := observed.symm.trans ((p.ordinaryDirect_eq_some_iff item r).mpr mem)
      cases impossible)
    simp [ordinaryDirectWeight, observed, empty]
  | some r =>
    have present := (p.ordinaryDirect_eq_some_iff item r).mp observed
    have singleton : p.ordinaryDirectPositions item = {r} := by
      ext x
      simp only [Finset.mem_singleton]
      exact ⟨fun mem => Finset.card_le_one_iff.mp (p.card_ordinaryDirectPositions_le_one item)
        mem present, fun equal => equal.symm ▸ present⟩
    simp [ordinaryDirectWeight, observed, singleton]

theorem ordinaryDirectWeight_le_of_size_le (item : NonLargePosition S) (k : ℕ) (positive : 0 < k)
    (bounds : ∀ r ∈ p.ordinaryDirectPositions item, residualSize r ≤ 1 / (k : ℝ)) :
    p.ordinaryDirectWeight item ≤ 1 / (k : ℝ) := by
  cases observed : p.ordinaryDirect item with
  | none =>
    simp only [ordinaryDirectWeight, observed, Option.map_none, Option.getD_none]
    positivity
  | some r =>
    simpa only [ordinaryDirectWeight, observed, Option.map_some, Option.getD_some, residualSize] using
      w1_le_inverse_of_le (p.valid _ (List.get_mem S r.val.val)).1 positive
        (bounds r ((p.ordinaryDirect_eq_some_iff item r).mp observed))

theorem direct_size_le_max_of_mem (item : NonLargePosition S) (r : ResidualPosition S)
    (mem : r ∈ p.ordinaryDirectPositions item) : residualSize r ≤ max (S.get item.val) (1 / 4) :=
  p.terminal_size_le_max_head_quarter (Nat.le_of_not_gt r.property)
    (p.ordinaryDirectPosition_path item r mem)

theorem direct_size_le_of_uncharged (item : NonLargePosition S) (r : ResidualPosition S)
    (mem : r ∈ p.ordinaryDirectPositions item) (uncharged : r.val ∉ p.thirdSlotTerminals) :
    residualSize r ≤ S.get item.val :=
  p.uncharged_terminal_size_le (Nat.le_of_not_gt r.property) uncharged
    (p.ordinaryDirectPosition_path item r mem)

theorem indirect_size_le_quarter (r : ResidualPosition S) (indirect : r.val ∈ p.indirectTerminals) :
    residualSize r ≤ 1 / 4 := by
  classical
  obtain ⟨head, deficit, slot, path⟩ := (Finset.mem_filter.mp indirect).2.2
  exact (p.terminal_size_le_max_head_quarter (Nat.le_of_not_gt r.property) path).trans
    (max_le (p.optimal_third_lt_quarter head deficit.1 slot).le le_rfl)

theorem ordinaryIndirectWeight_le_count (item : NonLargePosition S) (k : ℕ) (positive : 0 < k)
    (bounds : ∀ r ∈ p.ordinaryIndirectPositions item, residualSize r ≤ 1 / (k : ℝ)) :
    p.ordinaryIndirectWeight item ≤ ((p.ordinaryIndirectPositions item).card : ℝ) / k := by
  calc
    _ ≤ ∑ _r ∈ p.ordinaryIndirectPositions item, (1 / (k : ℝ)) := Finset.sum_le_sum fun r mem =>
      w1_le_inverse_of_le (p.valid _ (List.get_mem S r.val.val)).1 positive (bounds r mem)
    _ = _ := by simp [div_eq_mul_inv, nsmul_eq_mul]

theorem ordinaryIndirectWeight_le_quarter (item : NonLargePosition S) :
    p.ordinaryIndirectWeight item ≤ ((p.ordinaryIndirectPositions item).card : ℝ) / 4 := by
  simpa using p.ordinaryIndirectWeight_le_count item 4 (by decide) (fun r mem => by
    simpa using p.indirect_size_le_quarter r ((p.mem_ordinaryIndirectPositions_iff item r).mp mem).2)

end

end BinPacking.Decreasing.AlignedPacking

end

/- chains/OrdinaryPromotion.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

noncomputable section

variable {S : List ℝ} (p : AlignedPacking S)

/-- Residual chains assigned to this ordinary item and charged for a later optimal third slot. -/
def ordinaryPromotionPositions (item : NonLargePosition S) : Finset (ResidualPosition S) := by
  classical
  exact p.residualPositions.toFinset.filter fun r =>
    p.owner r = ordinaryOwner item ∧ r.val ∈ p.thirdSlotTerminals

theorem mem_ordinaryPromotionPositions_iff (item : NonLargePosition S) (r : ResidualPosition S) :
    r ∈ p.ordinaryPromotionPositions item ↔
      p.owner r = ordinaryOwner item ∧ r.val ∈ p.thirdSlotTerminals := by
  simp [ordinaryPromotionPositions, p.mem_residualPositions]

end

end BinPacking.Decreasing.AlignedPacking

end

/- OrdinaryWeights.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

noncomputable section

variable {S : List ℝ} (p : AlignedPacking S)

def ordinaryWeights (item : NonLargePosition S) : ResponsibilityWeights where
  direct := p.ordinaryDirectWeight item
  indirect := p.ordinaryIndirectWeight item
  extra := (2 / 3 : ℝ) * (p.ordinaryPromotionPositions item).card
  count := (p.ordinaryIndirectPositions item).card

theorem ordinary_extra_nonneg (item : NonLargePosition S) : 0 ≤ (p.ordinaryWeights item).extra := by
  unfold ordinaryWeights
  positivity

theorem ordinary_extra_discrete (item : NonLargePosition S) :
    (p.ordinaryWeights item).extra = 0 ∨ (2 / 3 : ℝ) ≤ (p.ordinaryWeights item).extra := by
  let charged := (p.ordinaryPromotionPositions item).card
  rcases Nat.eq_zero_or_pos charged with zero | positive
  · exact .inl (by change (2 / 3 : ℝ) * charged = 0; simp [zero])
  · right
    have count : (1 : ℝ) ≤ (charged : ℝ) := by exact_mod_cast positive
    change (2 / 3 : ℝ) ≤ (2 / 3 : ℝ) * charged
    linarith

theorem ordinary_extra_ge_of_mem (item : NonLargePosition S) (r : ResidualPosition S)
    (owns : p.owner r = ordinaryOwner item) (charged : r.val ∈ p.thirdSlotTerminals) :
    (2 / 3 : ℝ) ≤ (p.ordinaryWeights item).extra := by
  have count : (1 : ℝ) ≤ ((p.ordinaryPromotionPositions item).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨r, (p.mem_ordinaryPromotionPositions_iff item r).mpr ⟨owns, charged⟩⟩
  change (2 / 3 : ℝ) ≤ (2 / 3 : ℝ) * (p.ordinaryPromotionPositions item).card
  linarith

theorem direct_size_le_of_extra_eq_zero (item : NonLargePosition S) (r : ResidualPosition S)
    (mem : r ∈ p.ordinaryDirectPositions item) (zero : (p.ordinaryWeights item).extra = 0) :
    residualSize r ≤ S.get item.val := by
  apply p.direct_size_le_of_uncharged item r mem
  intro promoted
  have positive := p.ordinary_extra_ge_of_mem item r
    ((p.mem_ordinaryDirectPositions_iff item r).mp mem).1 promoted
  linarith

theorem ordinary_direct_le_half (item : NonLargePosition S) : (p.ordinaryWeights item).direct ≤ 1 / 2 := by
  change p.ordinaryDirectWeight item ≤ 1 / 2
  simpa using p.ordinaryDirectWeight_le_of_size_le item 2 (by decide) (fun r _ => by
    simpa [residualSize] using p.ordinary_size_le_half r.val)

theorem ordinary_direct_le_third (item : NonLargePosition S) (small : S.get item.val ≤ 1 / 3) :
    (p.ordinaryWeights item).direct ≤ 1 / 3 := by
  change p.ordinaryDirectWeight item ≤ 1 / 3
  simpa using p.ordinaryDirectWeight_le_of_size_le item 3 (by decide) (fun r mem => by
    have bound := (p.direct_size_le_max_of_mem item r mem).trans (max_le small (by norm_num))
    simpa using bound)

theorem ordinary_direct_le_quarter_of_noC (item : NonLargePosition S) (noC : ¬HasResidualC S)
    (small : S.get item.val ≤ 1 / 3) : (p.ordinaryWeights item).direct ≤ 1 / 4 := by
  change p.ordinaryDirectWeight item ≤ 1 / 4
  simpa using p.ordinaryDirectWeight_le_of_size_le item 4 (by decide) (fun r mem => by
    have bound := (p.direct_size_le_max_of_mem item r mem).trans (max_le small (by norm_num))
    simpa using residual_size_le_quarter_of_le_third noC r bound)

theorem ordinary_direct_le_quarter (item : NonLargePosition S) (small : S.get item.val ≤ 1 / 4) :
    (p.ordinaryWeights item).direct ≤ 1 / 4 := by
  change p.ordinaryDirectWeight item ≤ 1 / 4
  simpa using p.ordinaryDirectWeight_le_of_size_le item 4 (by decide) (fun r mem => by
    simpa using (p.direct_size_le_max_of_mem item r mem).trans (max_le small le_rfl))

theorem ordinary_direct_le_fifth_or_charged (item : NonLargePosition S) (small : S.get item.val ≤ 1 / 5) :
    (p.ordinaryWeights item).direct ≤ 1 / 5 ∨ (2 / 3 : ℝ) ≤ (p.ordinaryWeights item).extra := by
  rcases p.ordinary_extra_discrete item with zero | charged
  · left
    change p.ordinaryDirectWeight item ≤ 1 / 5
    simpa using p.ordinaryDirectWeight_le_of_size_le item 5 (by decide) (fun r mem => by
      simpa using (p.direct_size_le_of_extra_eq_zero item r mem zero).trans small)
  · exact Or.inr charged

end

end BinPacking.Decreasing.AlignedPacking

end

/- OrdinaryAdmissibility.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

noncomputable section

variable {S : List ℝ} (p : AlignedPacking S)

theorem direct_size_lt_third_of_count_pos (item : NonLargePosition S) (r : ResidualPosition S)
    (direct : r ∈ p.ordinaryDirectPositions item) (count : 0 < (p.ordinaryWeights item).count) :
    residualSize r < 1 / 3 := by
  change 0 < (p.ordinaryIndirectPositions item).card at count
  obtain ⟨indirect, mem⟩ := Finset.card_pos.mp count
  exact p.ordinary_direct_lt_third_of_indirect item direct mem

theorem ordinary_direct_le_third_of_count_pos (item : NonLargePosition S)
    (count : 0 < (p.ordinaryWeights item).count) : (p.ordinaryWeights item).direct ≤ 1 / 3 := by
  change p.ordinaryDirectWeight item ≤ 1 / 3
  simpa using p.ordinaryDirectWeight_le_of_size_le item 3 (by decide) (fun r mem => by
    simpa using (p.direct_size_lt_third_of_count_pos item r mem count).le)

theorem ordinary_direct_le_quarter_of_count_pos (item : NonLargePosition S) (noC : ¬HasResidualC S)
    (count : 0 < (p.ordinaryWeights item).count) : (p.ordinaryWeights item).direct ≤ 1 / 4 := by
  change p.ordinaryDirectWeight item ≤ 1 / 4
  simpa using p.ordinaryDirectWeight_le_of_size_le item 4 (by decide) (fun r mem => by
    simpa using residual_size_le_quarter_of_le_third noC r
      (p.direct_size_lt_third_of_count_pos item r mem count).le)

/-- The singleton responsibility bounds, instantiated on the actual ordinary owner. -/
theorem ordinaryWeights_admissible (item : NonLargePosition S) (hasC : Bool) (kind : SmallPieceClass)
    (case_iff : hasC = true ↔ HasResidualC S)
    (residualCD : ∃ r : ResidualPosition S, (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3)
    (interval : match kind with
      | .B => 1 / 3 < S.get item.val ∧ S.get item.val ≤ 1 / 2
      | .C => 1 / 4 < S.get item.val ∧ S.get item.val ≤ 1 / 3
      | .D => 1 / 5 < S.get item.val ∧ S.get item.val ≤ 1 / 4
      | .E => 2 / 11 < S.get item.val ∧ S.get item.val ≤ 1 / 5) :
    (p.ordinaryWeights item).Admissible hasC kind := by
  have noC (h : hasC = false) : ¬HasResidualC S := fun existsC => by
    have yes := case_iff.mpr existsC
    rw [h] at yes
    contradiction
  refine ⟨?_, p.ordinaryIndirectWeight_le_quarter item, ?_, p.ordinary_extra_nonneg item, ?_⟩
  · cases kind with
    | B =>
      by_cases zero : (p.ordinaryWeights item).count = 0
      · simpa only [directWeightLimit, if_pos zero] using p.ordinary_direct_le_half item
      · have positive := Nat.pos_of_ne_zero zero
        cases h : hasC
        · simpa [directWeightLimit, zero] using p.ordinary_direct_le_quarter_of_count_pos item (noC h) positive
        · simpa [directWeightLimit, zero] using p.ordinary_direct_le_third_of_count_pos item positive
    | C =>
      cases h : hasC
      · exact p.ordinary_direct_le_quarter_of_noC item (noC h) interval.2
      · exact p.ordinary_direct_le_third item interval.2
    | D => exact p.ordinary_direct_le_quarter item interval.2
    | E => exact p.ordinary_direct_le_quarter item (interval.2.trans (by norm_num))
  · change (p.ordinaryIndirectPositions item).card ≤ _
    cases kind with
    | B =>
      cases h : hasC
      · simpa only [indirectCountLimit, if_false, Bool.false_eq_true, if_pos interval.1] using
          p.card_ordinaryIndirectPositions_le item
      · obtain ⟨r, lower, upper⟩ := case_iff.mp h
        exact p.card_ordinaryIndirectPositions_le_of_residualC item r lower upper
    | C =>
      simpa only [indirectCountLimit, if_neg (not_lt_of_ge interval.2)] using
        p.card_ordinaryIndirectPositions_le item
    | D =>
      cases h : hasC
      · have nonB : ¬(1 / 3 : ℝ) < S.get item.val := not_lt_of_ge (interval.2.trans (by norm_num))
        simpa only [indirectCountLimit, Bool.false_eq_true, if_false, if_neg nonB] using
          p.card_ordinaryIndirectPositions_le item
      · obtain ⟨r, lower, upper⟩ := case_iff.mp h
        simp [indirectCountLimit, p.ordinary_indirect_empty_of_residualC item r lower upper interval.2]
    | E =>
      obtain ⟨r, lower, upper⟩ := residualCD
      simp [indirectCountLimit, p.ordinary_indirect_empty_of_residualCD item r lower upper interval.2]
  · intro isE
    subst kind
    exact p.ordinary_direct_le_fifth_or_charged item interval.2

end

end BinPacking.Decreasing.AlignedPacking

end

/- chains/OrdinaryRegrouping.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

open PieceChains

noncomputable section

variable {S : List ℝ} (p : AlignedPacking S)

private theorem nonLarge_of_assigned_outside (bin : Fin (optBins S))
    (outside : ¬isLargeBin S bin.val) (i : Fin S.length) (assigned : p.assign i = bin) :
    (largePrefixItems S).length ≤ i.val := by
  by_contra! inside
  have aligned := p.aligned i ((largeItem_iff_lt_filter_length p.sorted i).mpr inside)
  exact outside ((congrArg Fin.val assigned).symm.trans aligned ▸ inside)

/-- The indexed owners in an optimal non-A bin, in optimal slot order. -/
def ordinaryOwners (bin : Fin (optBins S)) (outside : ¬isLargeBin S bin.val) :
    List (NonLargePosition S) :=
  (assignmentPositions p.assign bin).pmap Subtype.mk
    (fun i mem => p.nonLarge_of_assigned_outside bin outside i ((mem_assignmentPositions _ _ _).mp mem))

theorem ordinaryOwners_map_val (bin : Fin (optBins S)) (outside : ¬isLargeBin S bin.val) :
    (p.ordinaryOwners bin outside).map Subtype.val = assignmentPositions p.assign bin := by
  simp [ordinaryOwners, List.map_pmap, List.pmap_eq_map]

theorem ordinaryOwners_nodup (bin : Fin (optBins S)) (outside : ¬isLargeBin S bin.val) :
    (p.ordinaryOwners bin outside).Nodup := by
  apply List.Nodup.of_map Subtype.val
  rw [p.ordinaryOwners_map_val]
  exact (List.nodup_finRange _).filter _

theorem mem_ordinaryOwners_iff (bin : Fin (optBins S)) (outside : ¬isLargeBin S bin.val)
    (item : NonLargePosition S) : item ∈ p.ordinaryOwners bin outside ↔ p.assign item.val = bin := by
  constructor
  · exact fun mem => (mem_assignmentPositions p.assign bin _).mp
      (p.ordinaryOwners_map_val bin outside ▸ List.mem_map_of_mem mem)
  · intro assigned
    have mapped : item.val ∈ (p.ordinaryOwners bin outside).map Subtype.val :=
      (p.ordinaryOwners_map_val bin outside).symm ▸ (mem_assignmentPositions p.assign bin _).mpr assigned
    obtain ⟨other, mem, same⟩ := List.mem_map.mp mapped
    exact (Subtype.ext same : other = item) ▸ mem

def ordinaryOwnerPositions (item : NonLargePosition S) : List (ResidualPosition S) :=
  ownerGroup p.owner p.residualPositions (ordinaryOwner item)

def ordinaryOwnerPieces (item : NonLargePosition S) : List ℝ :=
  (p.ordinaryOwnerPositions item).map residualSize

theorem responsiblePositions_perm_ordinaryOwners (bin : Fin (optBins S))
    (outside : ¬isLargeBin S bin.val) :
    (p.responsiblePositions bin).Perm
      (((p.ordinaryOwners bin outside).map p.ordinaryOwnerPositions).flatten) := by
  let owners := assignmentPositions p.assign bin
  have permutation := flatten_ownerGroups_perm p.owner owners (p.responsiblePositions bin)
    ((List.nodup_finRange _).filter _) (fun r mem => (mem_assignmentPositions _ _ _).mpr
      ((p.mem_responsiblePositions_iff _ _).mp mem))
  have sameGroup : ∀ i ∈ owners, ownerGroup p.owner (p.responsiblePositions bin) i =
      ownerGroup p.owner p.residualPositions i := by
    intro i inOwners
    unfold responsiblePositions ownerGroup
    rw [List.filter_filter]
    refine List.filter_congr (fun r _ => ?_)
    by_cases assigned : p.owner r = i
    · have routed : p.responsibilityBin r = bin :=
        (congrArg p.assign assigned).trans ((mem_assignmentPositions _ _ _).mp inOwners)
      simp [assigned, routed]
    · simp [assigned]
  rw [List.map_congr_left sameGroup] at permutation
  have mapGroups :
      (owners.map (ownerGroup p.owner p.residualPositions)).flatten =
        ((p.ordinaryOwners bin outside).map p.ordinaryOwnerPositions).flatten := by
    simp [owners, ← p.ordinaryOwners_map_val bin outside, ordinaryOwnerPositions, ordinaryOwner]
  exact (mapGroups ▸ permutation).symm

theorem responsiblePieces_perm_ordinaryOwners (bin : Fin (optBins S))
    (outside : ¬isLargeBin S bin.val) :
    (p.responsiblePieces bin).Perm
      (((p.ordinaryOwners bin outside).map p.ordinaryOwnerPieces).flatten) := by
  change (p.responsiblePieces bin).Perm
    (((p.ordinaryOwners bin outside).map
      (fun item => (p.ordinaryOwnerPositions item).map residualSize)).flatten)
  simpa only [responsiblePieces, List.map_flatten, List.map_map,
    Function.comp_def] using (p.responsiblePositions_perm_ordinaryOwners bin outside).map residualSize

private theorem routedCredit_eq_sum_ordinary (bin : Fin (optBins S)) (outside : ¬isLargeBin S bin.val)
    (charged : Finset (NonLargePosition S))
    (residual : ∀ item : ↥charged, ¬isLargeBin S (smallGreedySlot item.val).1)
    (counted : NonLargePosition S → Finset (ResidualPosition S))
    (mem_counted : ∀ item r, r ∈ counted item ↔ p.owner r = ordinaryOwner item ∧ r.val ∈ charged)
    (amount : ℝ) :
    routedCredit (fun item : ↥charged => p.responsibilityBin ⟨item.val, residual item⟩)
      (fun _ => amount) bin =
      ∑ item ∈ (p.ordinaryOwners bin outside).toFinset, amount * (counted item).card := by
  classical
  let owners := (p.ordinaryOwners bin outside).toFinset
  let index : NonLargePosition S ↪ Fin S.length := Function.Embedding.subtype _
  let active := p.residualPositions.toFinset.filter fun r => r.val ∈ charged
  let inBin := active.filter fun r => p.responsibilityBin r = bin
  let _ : DecidablePred (fun item : ↥charged =>
      p.responsibilityBin ⟨item.val, residual item⟩ = bin) := Classical.decPred _
  have activeMem (r : ResidualPosition S) : r ∈ active ↔ r.val ∈ charged := by
    simp [active, p.mem_residualPositions]
  have counts : (∑ item ∈ owners, (counted item).card) = inBin.card := by
    have eligibleOwner (r : ResidualPosition S) :
        p.owner r ∈ owners.map index ↔ p.responsibilityBin r = bin := by
      constructor
      · intro eligible
        obtain ⟨item, member, same⟩ := Finset.mem_map.mp eligible
        exact (congrArg p.assign (show item.val = p.owner r from same)).symm.trans
          ((p.mem_ordinaryOwners_iff bin outside item).mp (List.mem_toFinset.mp member))
      · intro assigned
        let item : NonLargePosition S := ⟨p.owner r,
          p.nonLarge_of_assigned_outside bin outside _ assigned⟩
        exact Finset.mem_map.mpr ⟨item, List.mem_toFinset.mpr
          ((p.mem_ordinaryOwners_iff bin outside item).mpr assigned), rfl⟩
    have filtered : active.filter (fun r => p.owner r ∈ owners.map index) = inBin := by
      ext r
      simp only [Finset.mem_filter, eligibleOwner, inBin]
    have fibers := Finset.sum_card_fiberwise_eq_card_filter active (owners.map index) p.owner
    rw [Finset.sum_map, filtered] at fibers
    refine (Finset.sum_congr rfl (fun item _ => congrArg Finset.card ?_)).trans fibers
    ext r
    change r ∈ counted item ↔ r ∈ active.filter (fun r => p.owner r = index item)
    exact (mem_counted item r).trans (and_comm.trans
      ((and_congr (activeMem r) (Iff.rfl : p.owner r = index item ↔ _)).symm.trans
        (@Finset.mem_filter _ (fun r => p.owner r = index item) _ active r).symm))
  have chargedCount :
      (Finset.univ.filter (fun item : ↥charged =>
        p.responsibilityBin ⟨item.val, residual item⟩ = bin)).card = inBin.card := by
    let tag (item : ↥charged) : ResidualPosition S := ⟨item.val, residual item⟩
    refine Finset.card_bij (fun item _ => tag item) ?_ ?_ ?_
    · intro item mem
      exact Finset.mem_filter.mpr ⟨(activeMem _).mpr item.property, (Finset.mem_filter.mp mem).2⟩
    · intro a _ b _ same
      exact Subtype.ext (congrArg (fun r : ResidualPosition S => r.val) same)
    · intro r mem
      have constraints := Finset.mem_filter.mp mem
      let item : ↥charged := ⟨r.val, (activeMem r).mp constraints.1⟩
      have tagEq : tag item = r := Subtype.ext rfl
      exact ⟨item, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (congrArg p.responsibilityBin tagEq).trans constraints.2⟩, tagEq⟩
  unfold routedCredit
  rw [Finset.sum_const, nsmul_eq_mul]
  change (↑(Finset.univ.filter (fun item : ↥charged =>
      p.responsibilityBin ⟨item.val, residual item⟩ = bin)).card : ℝ) * amount =
    ∑ item ∈ owners, amount * ↑(counted item).card
  rw [chargedCount, ← counts, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun item _ => mul_comm _ _)

private theorem routed_anchorCredit_eq_zero_of_nonA (bin : Fin (optBins S))
    (outside : ¬isLargeBin S bin.val) :
    routedCredit p.anchorRoute (fun anchor => anchorCredit
      (IsDeficit smallGreedySlot p.smallOptimalSlot (· ∈ largeBins S))
      p.optimalHasB anchor.val) bin = 0 := by
  classical
  let _ : DecidablePred (fun anchor : ↥(largeBins S) => p.anchorRoute anchor = bin) :=
    Classical.decPred _
  unfold routedCredit
  refine Finset.sum_eq_zero (fun anchor member => ?_)
  have label : (p.anchorRoute anchor).val = anchor.val :=
    p.anchor_bin_index ⟨anchor.val, Finset.mem_range.mp anchor.property⟩
  have same := congrArg Fin.val (Finset.mem_filter.mp member).2
  exact (outside ((label.symm.trans same) ▸ Finset.mem_range.mp anchor.property)).elim

/-- Both credits of a non-A optimal bin are the charges to its ordinary owners. -/
theorem credit_eq_sum_ordinaryOwners (bin : Fin (optBins S)) (outside : ¬isLargeBin S bin.val) :
    p.credit bin = ((p.ordinaryOwners bin outside).map fun item =>
      ((p.ordinaryIndirectPositions item).card : ℝ) +
      (2 / 3 : ℝ) * (p.ordinaryPromotionPositions item).card).sum := by
  classical
  unfold credit firstCredit secondCredit
  rw [p.routed_anchorCredit_eq_zero_of_nonA bin outside, zero_add]
  unfold indirectRoute thirdSlotRoute
  rw [p.routedCredit_eq_sum_ordinary bin outside p.indirectTerminals p.indirectTerminals_outside
    p.ordinaryIndirectPositions p.mem_ordinaryIndirectPositions_iff 1]
  rw [p.routedCredit_eq_sum_ordinary bin outside p.thirdSlotTerminals p.thirdSlotTerminals_outside
    p.ordinaryPromotionPositions p.mem_ordinaryPromotionPositions_iff (2 / 3)]
  rw [← List.sum_toFinset _ (p.ordinaryOwners_nodup bin outside), Finset.sum_add_distrib]
  simp

end

end BinPacking.Decreasing.AlignedPacking

end

/- assembly/Responsibility.lean -/
section

namespace BinPacking.Decreasing

/-- Johnson's responsibility accounting, with the unused collaboration credit retained.
The weights count the pieces assigned to each optimal bin. -/
theorem ffd_le_with_credit_slack
    (L residual : List ℝ) (aBins : ℕ)
    (pieces : Fin (optBins L) → List ℝ)
    (nonLarge credit : Fin (optBins L) → ℝ)
    (hffd : (FFD L : ℝ) - aBins - 4 ≤ W residual)
    (hcover : W residual ≤ ∑ i, W (pieces i))
    (hcount : ∑ i, nonLarge i = (optBins L : ℝ) - aBins)
    (hbin : ∀ i, W (pieces i) + credit i ≤ 11 / 9 * (nonLarge i + credit i)) :
    (FFD L : ℝ) ≤ 11 / 9 * (optBins L : ℝ) - 2 / 9 * (aBins - ∑ i, credit i) + 4 := by
  have htotal := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbin i)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, hcount] at htotal
  linarith [hffd.trans hcover, htotal]

/-- The desired first-fit bound follows when the collaboration credit is limited by
the number of bins containing an item larger than one half. -/
theorem ffd_le_of_responsibility
    (L residual : List ℝ) (aBins : ℕ)
    (pieces : Fin (optBins L) → List ℝ)
    (nonLarge credit : Fin (optBins L) → ℝ)
    (hffd : (FFD L : ℝ) - aBins - 4 ≤ W residual)
    (hcover : W residual ≤ ∑ i, W (pieces i))
    (hcount : ∑ i, nonLarge i = (optBins L : ℝ) - aBins)
    (hbin : ∀ i, W (pieces i) + credit i ≤ 11 / 9 * (nonLarge i + credit i))
    (hcredit : ∑ i, credit i ≤ aBins) :
    (FFD L : ℝ) ≤ 11 / 9 * (optBins L : ℝ) + 4 := by
  linarith [ffd_le_with_credit_slack L residual aBins pieces nonLarge credit hffd hcover hcount hbin]

/-- The sorting in the definition of `W` makes weight independent of input order. -/
theorem weight_perm {L R : List ℝ} (h : L.Perm R) : W L = W R := by
  have hsort : (sortDesc L).Perm (sortDesc R) :=
    (List.mergeSort_perm _ _).trans (h.trans (List.mergeSort_perm _ _).symm)
  have hpair (X : List ℝ) : (sortDesc X).Pairwise (fun a b => b ≤ a) := by
    simpa only [sortDesc, decide_eq_true_eq] using
      List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
        (fun a b c => by simpa using (fun (h₁ : b ≤ a) (h₂ : c ≤ b) => le_trans h₂ h₁))
        (fun a b => by simpa using le_total b a) X
  have heq := hsort.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => le_antisymm h₂ h₁)
    (hpair L) (hpair R)
  exact congrArg (fun S : List ℝ =>
    (partitions S.length).inf' ⟨id, by simp [partitions]⟩ (w12 S)) heq

/-- The grouped pieces may be presented in any order. -/
theorem weight_le_sum_of_perm {n : ℕ} {residual : List ℝ} (pieces : Fin n → List ℝ)
    (hperm : residual.Perm (List.ofFn pieces).flatten)
    (hsub : W (List.ofFn pieces).flatten ≤ ((List.ofFn pieces).map W).sum) :
    W residual ≤ ∑ i, W (pieces i) := by
  rw [weight_perm hperm]
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using hsub

end BinPacking.Decreasing

end

/- Definitions/Def_BinPacking_SmallItems_Model.lean -/
section

namespace BinPacking.SmallItems

/-- The standing hypothesis of the paper (p. 300): `L = (a₁, …, aₙ)` is a list of real numbers
in `(0, 1]`. Lists are read left to right and may repeat values. -/
def IsList (L : List ℝ) : Prop := ∀ a ∈ L, 0 < a ∧ a ≤ 1

/-- `L*` (p. 300): the minimum number `b` of unit bins such that the items of `L` can be assigned
to bins `0, …, b - 1` (a map `Fin L.length → Fin b`) with every bin sum at most `1`.
`sInf` on `ℕ` is `0` on the empty set; for a list satisfying `IsList` the set is nonempty
(`b = L.length` works), so `IsList` is assumed wherever `optBins` is used. -/
noncomputable def optBins (L : List ℝ) : ℕ :=
  sInf {b : ℕ | ∃ f : Fin L.length → Fin b, ∀ j : Fin b,
    ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i ≤ 1}

/-- Place item `a` into bin number `j` (0-based) of the current list of nonempty bins; if `j` is
not the index of an existing bin, open a new bin `[a]` at the end. Each bin records its contents
in placement order. -/
def placeAt (bins : List (List ℝ)) (j : ℕ) (a : ℝ) : List (List ℝ) :=
  if j < bins.length then bins.mapIdx (fun i B => if i = j then B ++ [a] else B)
  else bins ++ [[a]]

/-- First-fit choice (Algorithm 1, p. 300): the least index of a nonempty bin whose level
`β` satisfies `β ≤ 1 - a`, i.e. `β + a ≤ 1`; `bins.length` (a new bin) if there is none. -/
noncomputable def ffChoice (bins : List (List ℝ)) (a : ℝ) : ℕ :=
  bins.findIdx (fun B => decide (B.sum + a ≤ 1))

/-- The first-fit run on `L`: the items are placed in list order, starting from no bins.
The result is the list of nonempty bins `B₁, B₂, …` in index order. -/
noncomputable def ffPack (L : List ℝ) : List (List ℝ) :=
  L.foldl (fun bins a => placeAt bins (ffChoice bins a) a) []

/-- `FF(L)` (p. 301): the number of bins used by first-fit on `L`. -/
noncomputable def FF (L : List ℝ) : ℕ := (ffPack L).length

/-- History of the first-fit run: the (0-based) index of the bin into which item number `i`
(0-based, the paper's `a_{i+1}`) is placed. It is first-fit's choice on the bins produced by the
first `i` items. Bins are never reordered, so it is also the item's bin in the final packing. -/
noncomputable def ffBinOf (L : List ℝ) (i : Fin L.length) : ℕ :=
  ffChoice (ffPack (L.take i)) (L.get i)

/-- The list `L` arranged into nonincreasing order (the first step of Algorithm 3, p. 300). -/
noncomputable def sortDesc (L : List ℝ) : List ℝ :=
  L.mergeSort (fun a b => decide (b ≤ a))

/-- The first-fit decreasing packing of `L` (Algorithm 3, p. 300): first-fit applied to the
nonincreasing rearrangement of `L`. -/
noncomputable def ffdPack (L : List ℝ) : List (List ℝ) := ffPack (sortDesc L)

/-- `FFD(L)` (p. 301): the number of bins used by first-fit decreasing on `L`. -/
noncomputable def FFD (L : List ℝ) : ℕ := FF (sortDesc L)

end BinPacking.SmallItems

end

/- Definitions/Def_BinPacking_SmallItems_Weight.lean -/
section

namespace BinPacking.SmallItems

open Classical

/-- `x` is a `k`-piece (p. 316) if `x ∈ (1/(k + 1), 1/k]`. (For `k = 0` no real is a `0`-piece,
since `1/0 = 0` in Lean.) -/
def IsPiece (k : ℕ) (x : ℝ) : Prop := 1 / ((k : ℝ) + 1) < x ∧ x ≤ 1 / (k : ℝ)

/-- `w₁(x) = ⌊1/x⌋⁻¹` (p. 316). For `x ∈ (0, 1]` the integer `⌊1/x⌋` is the unique `k` with `x` a
`k`-piece, so `w₁(x) = 1/k`. -/
noncomputable def w1 (x : ℝ) : ℝ := ((⌊1 / x⌋₊ : ℕ) : ℝ)⁻¹

/-- `(x, y)` obeys relation `k` (p. 317) if `x` is a `k`-piece and `kx + y ≤ 1`. -/
def ObeysRelation (k : ℕ) (x y : ℝ) : Prop := IsPiece k x ∧ (k : ℝ) * x + y ≤ 1

/-- `w₂(x, y)` (p. 317): `w₁(x) + ((k − 1)/k) w₁(y)` if `(x, y)` obeys relation `k`, where `k` is
the piece type of `x`, and `w₁(x) + w₁(y)` otherwise. The relation uses the `k` of the first
(larger) element `x`; for `x ∈ (0, 1]` that `k` is `⌊1/x⌋`. -/
noncomputable def w2 (x y : ℝ) : ℝ :=
  if ObeysRelation ⌊1 / x⌋₊ x y then
    w1 x + (((⌊1 / x⌋₊ : ℕ) : ℝ) - 1) / ((⌊1 / x⌋₊ : ℕ) : ℝ) * w1 y
  else w1 x + w1 y

/-- The partitions of the positions `0, …, n - 1` into one- and two-element sets, encoded as the
involutions `σ` of `Fin n` (`σ * σ = 1`): the fixed points are the one-element sets and the
pairs `{i, σ i}` with `i ≠ σ i` the two-element sets. The set is finite and contains `σ = 1`. -/
noncomputable def pairings (n : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => σ * σ = 1)

/-- `w₁₂(π)` (p. 316) for a partition `π` (an involution `σ`) of the positions of a list `S`:
`Σ_{x ∈ π(1)} w₁(x) + Σ_{(x,y) ∈ π(2)} w₂(x, y)`, where `π(1)` are the fixed points and `π(2)`
the pairs `(S_i, S_{σ i})` with `i < σ i` (the paper's `index(x) < index(y)`). -/
noncomputable def w12 (S : List ℝ) (σ : Equiv.Perm (Fin S.length)) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => σ i = i), w1 (S.get i)) +
    ∑ i ∈ Finset.univ.filter (fun i => i < σ i), w2 (S.get i) (S.get (σ i))

/-- The weight `W(X) = min_π w₁₂(π)` (pp. 315–316), `π` ranging over all partitions of `X` into
one- and two-element sets. The elements are indexed in nonincreasing order (the paper's `L` is in
decreasing order), so each pair is oriented (larger, smaller); for equal values the orientation
does not affect `w₂`, and `W` depends only on the multiset `X`. The minimum is over the finite
nonempty set `pairings`, so it is attained. -/
noncomputable def W (X : List ℝ) : ℝ :=
  (pairings (sortDesc X).length).inf' ⟨1, by simp [pairings]⟩ (w12 (sortDesc X))

/-- The largest element of a bin (`0` for an empty bin; every bin of a packing is nonempty). -/
def binMax (B : List ℝ) : ℝ := B.foldr max 0

/-- A `k`-bin (p. 316): a bin whose largest element is a `k`-piece. -/
def IsKBin (k : ℕ) (B : List ℝ) : Prop := IsPiece k (binMax B)

/-- The final FFD bin (in `ffdPack L`) holding position `i` of the sorted list `sortDesc L`. -/
noncomputable def ffdBin (L : List ℝ) (i : Fin (sortDesc L).length) : List ℝ :=
  (ffdPack L).getD (ffBinOf (sortDesc L) i) []

/-- BASIC (p. 316): the positions `i` of the sorted list `sortDesc L` such that, for some `k`,
the item is a `k`-piece and lies in a `k`-bin of the FFD packing of `L`. -/
noncomputable def basic (L : List ℝ) : Finset (Fin (sortDesc L).length) :=
  Finset.univ.filter (fun i => ∃ k : ℕ, IsPiece k ((sortDesc L).get i) ∧ IsKBin k (ffdBin L i))

/-- SURPLUS `= L − BASIC` (p. 317), as positions of the sorted list. -/
noncomputable def surplus (L : List ℝ) : Finset (Fin (sortDesc L).length) :=
  Finset.univ \ basic L

end BinPacking.SmallItems

end

/- small-only/AcceptedWeights.lean -/
section

set_option autoImplicit false


namespace FFBAux_ffb69a58
open BinPacking.SmallItems

open Classical in
noncomputable def gw (b x : ℝ) : ℝ := if ∃ k : ℕ, IsPiece k x ∧ IsPiece k b then w1 x else 0

noncomputable def hw (b : ℝ) (B : List ℝ) : ℝ := (B.map (gw b)).sum

lemma w1_nonneg (x : ℝ) : 0 ≤ w1 x := by unfold w1; positivity

lemma gw_nonneg (b x : ℝ) : 0 ≤ gw b x := by
  unfold gw; split_ifs
  · exact w1_nonneg x
  · exact le_refl 0

lemma hw_append (b : ℝ) (B : List ℝ) (y : ℝ) : hw b (B ++ [y]) = hw b B + gw b y := by
  simp [hw]

lemma piece_pos {k : ℕ} {x : ℝ} (h : IsPiece k x) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨h1, h2⟩ := h
    simp at h1 h2
    linarith
  · exact hk

lemma floor_eq_of_piece {k : ℕ} {x : ℝ} (h : IsPiece k x) : ⌊1 / x⌋₊ = k := by
  have hk := piece_pos h
  obtain ⟨h1, h2⟩ := h
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hx : 0 < x := lt_trans (by positivity) h1
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [le_div_iff₀ hx]
    have := (le_div_iff₀ hk').mp h2
    nlinarith
  · rw [div_lt_iff₀ hx]
    have := (div_lt_iff₀ (by positivity : (0:ℝ) < k+1)).mp h1
    nlinarith

lemma piece_of_floor {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : IsPiece ⌊1 / x⌋₊ x := by
  have h1x : (1:ℝ) ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
  have hk1 : 1 ≤ ⌊1 / x⌋₊ := Nat.le_floor (by simpa using h1x)
  have hk' : (0:ℝ) < (⌊1 / x⌋₊ : ℝ) := by exact_mod_cast hk1
  have hfl : ((⌊1 / x⌋₊ : ℕ) : ℝ) ≤ 1 / x := Nat.floor_le (by positivity)
  have hlt : 1 / x < ((⌊1 / x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  constructor
  · rw [div_lt_iff₀ (by positivity)]
    have := (div_lt_iff₀ hx).mp hlt
    nlinarith
  · rw [le_div_iff₀ hk']
    have := (le_div_iff₀ hx).mp hfl
    nlinarith

lemma foldr_max_eq (a : ℝ) (ha : 0 ≤ a) (B : List ℝ) :
    B.foldr max a = max (B.foldr max 0) a := by
  induction B with
  | nil => simp [ha]
  | cons b B ih => simp only [List.foldr_cons, ih, max_assoc]

lemma le_binMax {x : ℝ} {B : List ℝ} (h : x ∈ B) : x ≤ binMax B := by
  induction B with
  | nil => simp at h
  | cons b B ih =>
    simp only [binMax, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma binMax_mem {B : List ℝ} (hne : B ≠ []) (hpos : ∀ x ∈ B, 0 ≤ x) : binMax B ∈ B := by
  induction B with
  | nil => exact absurd rfl hne
  | cons b B ih =>
    simp only [binMax, List.foldr_cons] at ih ⊢
    by_cases hB : B = []
    · subst hB
      simp [max_eq_left (hpos b (by simp))]
    · rcases max_choice b (B.foldr max 0) with h | h
      · rw [h]; simp
      · rw [h]
        exact List.mem_cons_of_mem _ (ih hB (fun x hx => hpos x (List.mem_cons_of_mem _ hx)))

lemma binMax_append {B : List ℝ} {y : ℝ} (hy : 0 ≤ y) (hle : y ≤ binMax B) :
    binMax (B ++ [y]) = binMax B := by
  unfold binMax
  rw [List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_max_eq _ (le_max_right _ _)]
  unfold binMax at hle
  rw [max_eq_left hy, max_eq_left hle]

lemma binMax_single {y : ℝ} (hy : 0 ≤ y) : binMax [y] = y := by simp [binMax, hy]

lemma getD_lt {α : Type} (P : List α) (j : ℕ) (d : α) (hj : j < P.length) : P.getD j d = P[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl

lemma getD_ge {α : Type} (P : List α) (j : ℕ) (d : α) (hj : P.length ≤ j) : P.getD j d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]; rfl

lemma placeAt_lt {P : List (List ℝ)} {c : ℕ} {y : ℝ} (hc : c < P.length) :
    (placeAt P c y).length = P.length ∧
    ∀ j, (placeAt P c y).getD j [] = if j = c then P.getD j [] ++ [y] else P.getD j [] := by
  refine ⟨by simp [placeAt, hc], fun j => ?_⟩
  simp only [placeAt, hc, if_true]
  rcases lt_or_ge j P.length with hj | hj
  · rw [getD_lt _ _ _ (by simpa using hj), getD_lt _ _ _ hj, List.getElem_mapIdx]
  · rw [getD_ge _ _ _ (by simpa using hj), getD_ge _ _ _ hj]
    have : j ≠ c := by omega
    simp [this]

lemma placeAt_eq {P : List (List ℝ)} {y : ℝ} :
    placeAt P P.length y = P ++ [[y]] := by simp [placeAt]

lemma getD_app_lt (P : List (List ℝ)) (y : ℝ) (j : ℕ) (hj : j < P.length) :
    (P ++ [[y]]).getD j [] = P.getD j [] := by
  rw [getD_lt _ _ _ (by simp; omega), getD_lt _ _ _ hj, List.getElem_append_left hj]

lemma getD_app_eq (P : List (List ℝ)) (y : ℝ) :
    (P ++ [[y]]).getD P.length [] = [y] := by
  rw [getD_lt _ _ _ (by simp)]
  simp

lemma getD_app_gt (P : List (List ℝ)) (y : ℝ) (j : ℕ) (hj : P.length < j) :
    (P ++ [[y]]).getD j [] = [] := by
  rw [getD_ge _ _ _ (by simp; omega)]

lemma sum_placeAt (P : List (List ℝ)) (c : ℕ) (y : ℝ) (hc : c ≤ P.length) (f : ℕ → ℝ → ℝ) :
    ∑ j ∈ Finset.range (placeAt P c y).length, (((placeAt P c y).getD j []).map (f j)).sum =
      ∑ j ∈ Finset.range P.length, ((P.getD j []).map (f j)).sum + f c y := by
  rcases lt_or_eq_of_le hc with hc | rfl
  · obtain ⟨hl, hg⟩ := placeAt_lt (y := y) hc
    rw [hl]
    have : ∀ j ∈ Finset.range P.length, (((placeAt P c y).getD j []).map (f j)).sum =
        ((P.getD j []).map (f j)).sum + (if j = c then f j y else 0) := by
      intro j _
      rw [hg j]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [hc]
  · rw [placeAt_eq]
    simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [getD_app_lt _ _ _ hj]
    · rw [getD_app_eq]
      simp

lemma ffPack_succ (S : List ℝ) (t : ℕ) (ht : t < S.length) :
    ffPack (S.take (t+1)) =
      placeAt (ffPack (S.take t)) (ffChoice (ffPack (S.take t)) S[t]) S[t] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some]
  unfold ffPack
  rw [List.foldl_append]
  rfl

lemma ffChoice_le (P : List (List ℝ)) (a : ℝ) : ffChoice P a ≤ P.length := by
  unfold ffChoice; exact List.findIdx_le_length

lemma ffChoice_eq (P : List (List ℝ)) (a : ℝ) (h : ffChoice P a = P.length) :
    ∀ B ∈ P, 1 < B.sum + a := by
  unfold ffChoice at h
  have := List.findIdx_eq_length.mp h
  intro B hB
  have h2 := this B hB
  simp at h2
  linarith

lemma identity (S : List ℝ) (Pf : List (List ℝ)) (t : ℕ) (ht : t ≤ S.length) :
    ∑ j ∈ Finset.range (ffPack (S.take t)).length,
        (((ffPack (S.take t)).getD j []).map (gw (binMax (Pf.getD j [])))).sum =
      ∑ i ∈ Finset.range t, (if h : i < S.length then
          gw (binMax (Pf.getD (ffBinOf S ⟨i, h⟩) [])) S[i] else 0) := by
  induction t with
  | zero => simp [ffPack]
  | succ t ih =>
    have ht' : t < S.length := by omega
    rw [ffPack_succ S t ht', sum_placeAt _ _ _ (ffChoice_le _ _) _, ih (by omega),
      Finset.sum_range_succ, dif_pos ht']
    rfl

structure Inv (S : List ℝ) (t : ℕ) (P : List (List ℝ)) : Prop where
  ne : ∀ j < P.length, P.getD j [] ≠ []
  src : ∀ j, ∀ x ∈ P.getD j [], ∃ i, i < t ∧ ∃ hi : i < S.length, S[i] = x
  full : ∀ j < P.length, 1 ≤ hw (binMax (P.getD j [])) (P.getD j []) ∨
    ∀ j', j < j' → j' < P.length → ⌊1 / binMax (P.getD j' [])⌋₊ ≠ ⌊1 / binMax (P.getD j [])⌋₊

lemma key {B : List ℝ} {y : ℝ} (hne : B ≠ []) (hy : 0 < y) (hy2 : y ≤ 1/2)
    (hge : ∀ x ∈ B, y ≤ x) (hle1 : ∀ x ∈ B, x ≤ 1)
    (htype : ⌊1 / binMax B⌋₊ = ⌊1 / y⌋₊) (hsum : 1 < B.sum + y) :
    1 ≤ hw (binMax B) B := by
  have hpy : IsPiece ⌊1 / y⌋₊ y := piece_of_floor hy (by linarith)
  have hk1 : 1 ≤ ⌊1 / y⌋₊ := piece_pos hpy
  have hkR : (0:ℝ) < (⌊1 / y⌋₊ : ℝ) := by exact_mod_cast hk1
  have hbmem : binMax B ∈ B := binMax_mem hne (fun x hx => le_trans hy.le (hge x hx))
  have hb0 : 0 < binMax B := lt_of_lt_of_le hy (hge _ hbmem)
  have hpb : IsPiece ⌊1 / y⌋₊ (binMax B) := by
    rw [← htype]; exact piece_of_floor hb0 (hle1 _ hbmem)
  have hpx : ∀ x ∈ B, IsPiece ⌊1 / y⌋₊ x := fun x hx =>
    ⟨lt_of_lt_of_le hpy.1 (hge x hx), le_trans (le_binMax hx) hpb.2⟩
  have hg : ∀ x ∈ B, gw (binMax B) x = ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹ := by
    intro x hx
    unfold gw
    rw [if_pos ⟨_, hpx x hx, hpb⟩]
    unfold w1
    rw [floor_eq_of_piece (hpx x hx)]
  have hhw : hw (binMax B) B = B.length * ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹ := by
    unfold hw
    rw [List.map_congr_left hg]
    simp
  have hsumle : B.sum ≤ B.length * ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹ := by
    have := List.sum_le_card_nsmul B (((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹)
      (fun x hx => by have := (hpx x hx).2; simpa [one_div] using this)
    simpa [nsmul_eq_mul] using this
  have hyk : y ≤ ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹ := by simpa [one_div] using hpy.2
  have h1 : ((⌊1 / y⌋₊ : ℝ) - 1) < B.length := by
    have h0 : 1 - ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹ < B.length * ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹ := by linarith
    have h2 : (1 - ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹) * (⌊1 / y⌋₊ : ℝ) = (⌊1 / y⌋₊ : ℝ) - 1 := by
      field_simp
    have h3 : (B.length * ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹) * (⌊1 / y⌋₊ : ℝ) = B.length := by
      field_simp
    have := mul_lt_mul_of_pos_right h0 hkR
    rw [h2, h3] at this
    exact this
  have h4 : ⌊1 / y⌋₊ ≤ B.length := by
    have h5 : ((⌊1 / y⌋₊ : ℕ) : ℝ) < ((B.length + 1 : ℕ) : ℝ) := by push_cast; linarith
    have : ⌊1 / y⌋₊ < B.length + 1 := by exact_mod_cast h5
    omega
  rw [hhw]
  calc (1:ℝ) = (⌊1 / y⌋₊ : ℝ) * ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹ := by field_simp
    _ ≤ B.length * ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹ := by gcongr

lemma inv_step (S : List ℝ) (hs : S.Pairwise (fun a b => b ≤ a))
    (hr : ∀ x ∈ S, 0 < x ∧ x ≤ 1/2)
    (t : ℕ) (ht : t < S.length) (P : List (List ℝ)) (hI : Inv S t P) :
    Inv S (t+1) (placeAt P (ffChoice P S[t]) S[t]) := by
  have hyr := hr S[t] (List.getElem_mem ht)
  have hge : ∀ j, ∀ x ∈ P.getD j [], S[t] ≤ x ∧ 0 < x ∧ x ≤ 1/2 := by
    intro j x hx
    obtain ⟨i, hit, hi, rfl⟩ := hI.src j x hx
    exact ⟨List.pairwise_iff_getElem.mp hs i t hi ht hit, hr _ (List.getElem_mem hi)⟩
  have hcle : ffChoice P S[t] ≤ P.length := ffChoice_le _ _
  rcases lt_or_eq_of_le hcle with hlt | heq
  · obtain ⟨hl, hg⟩ := placeAt_lt (y := S[t]) hlt
    have hbm : ∀ j, binMax ((placeAt P (ffChoice P S[t]) S[t]).getD j []) =
        binMax (P.getD j []) := by
      intro j
      rw [hg j]
      split_ifs with hjc
      · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hI.ne j (hjc ▸ hlt))
        exact binMax_append hyr.1.le (le_trans (hge j x hx).1 (le_binMax hx))
      · rfl
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [hl] at hj
      rw [hg j]
      split_ifs
      · simp
      · exact hI.ne j hj
    · intro j x hx
      rw [hg j] at hx
      split_ifs at hx
      · rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨i, hit, hi, he⟩ := hI.src j x hx
          exact ⟨i, by omega, hi, he⟩
        · simp at hx
          exact ⟨t, by omega, ht, hx.symm⟩
      · obtain ⟨i, hit, hi, he⟩ := hI.src j x hx
        exact ⟨i, by omega, hi, he⟩
    · intro j hj
      rw [hl] at hj
      simp only [hbm, hl]
      rcases hI.full j hj with h | h
      · left
        rw [hg j]
        split_ifs with hjc
        · rw [hw_append]
          linarith [gw_nonneg (binMax (P.getD j [])) S[t]]
        · exact h
      · right; exact h
  · have hP : placeAt P (ffChoice P S[t]) S[t] = P ++ [[S[t]]] := by
      rw [heq]; exact placeAt_eq
    have hnofit := ffChoice_eq P S[t] heq
    rw [hP]
    have hlen : (P ++ [[S[t]]]).length = P.length + 1 := by simp
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [hlen] at hj
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj | rfl
      · rw [getD_app_lt _ _ _ hj]; exact hI.ne j hj
      · rw [getD_app_eq]; simp
    · intro j x hx
      rcases lt_trichotomy j P.length with hj | rfl | hj
      · rw [getD_app_lt _ _ _ hj] at hx
        obtain ⟨i, hit, hi, he⟩ := hI.src j x hx
        exact ⟨i, by omega, hi, he⟩
      · rw [getD_app_eq] at hx
        simp at hx
        exact ⟨t, by omega, ht, hx.symm⟩
      · rw [getD_app_gt _ _ _ hj] at hx
        simp at hx
    · intro j hj
      rw [hlen] at hj
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj | rfl
      · rw [getD_app_lt _ _ _ hj]
        rcases hI.full j hj with h | h
        · left; exact h
        · by_cases htyp : ⌊1 / binMax (P.getD j [])⌋₊ = ⌊1 / S[t]⌋₊
          · left
            have hmem : P.getD j [] ∈ P := by rw [getD_lt _ _ _ hj]; exact List.getElem_mem hj
            exact key (hI.ne j hj) hyr.1 hyr.2 (fun x hx => (hge j x hx).1)
              (fun x hx => by linarith [(hge j x hx).2.2]) htyp (hnofit _ hmem)
          · right
            intro j' hjj' hj'
            rw [hlen] at hj'
            rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj') with hj' | rfl
            · rw [getD_app_lt _ _ _ hj']; exact h j' hjj' hj'
            · rw [getD_app_eq, binMax_single hyr.1.le]
              exact fun e => htyp e.symm
      · right
        intro j' hjj' hj'
        omega

lemma inv_all (S : List ℝ) (hs : S.Pairwise (fun a b => b ≤ a))
    (hr : ∀ x ∈ S, 0 < x ∧ x ≤ 1/2) :
    ∀ t, t ≤ S.length → Inv S t (ffPack (S.take t))
  | 0, _ => by
    refine ⟨?_, ?_, ?_⟩
    · intro j hj; simp [ffPack] at hj
    · intro j x hx; simp [ffPack] at hx
    · intro j hj; simp [ffPack] at hj
  | t+1, ht => by
    rw [ffPack_succ S t (by omega)]
    exact inv_step S hs hr t (by omega) _ (inv_all S hs hr t (by omega))

lemma final_bound (N : ℕ) (hN0 : 0 < N) (S : List ℝ)
    (hr : ∀ x ∈ S, 1/(N:ℝ) < x ∧ x ≤ 1/2) (P : List (List ℝ))
    (hI : Inv S S.length P) :
    (P.length : ℝ) - ∑ j ∈ Finset.Icc 2 (N - 1), ((j : ℝ) - 1) / (j : ℝ) ≤
      ∑ j ∈ Finset.range P.length, ((P.getD j []).map (gw (binMax (P.getD j [])))).sum := by
  have hbin : ∀ j < P.length, binMax (P.getD j []) ∈ P.getD j [] ∧
      1/(N:ℝ) < binMax (P.getD j []) ∧ binMax (P.getD j []) ≤ 1/2 := by
    intro j hj
    have hsrc : ∀ x ∈ P.getD j [], 1/(N:ℝ) < x ∧ x ≤ 1/2 := by
      intro x hx
      obtain ⟨i, _, hi, rfl⟩ := hI.src j x hx
      exact hr _ (List.getElem_mem hi)
    have hm := binMax_mem (hI.ne j hj)
      (fun x hx => le_of_lt (lt_of_le_of_lt (by positivity) (hsrc x hx).1))
    exact ⟨hm, hsrc _ hm⟩
  have hNR : (0:ℝ) < N := by exact_mod_cast hN0
  have hτ : ∀ j < P.length, ⌊1 / binMax (P.getD j [])⌋₊ ∈ Finset.Icc 2 (N - 1) := by
    intro j hj
    obtain ⟨_, h1, h2⟩ := hbin j hj
    have hb : 0 < binMax (P.getD j []) := lt_of_le_of_lt (by positivity) h1
    rw [Finset.mem_Icc]
    constructor
    · apply Nat.le_floor
      rw [le_div_iff₀ hb]
      push_cast
      linarith
    · have : ⌊1 / binMax (P.getD j [])⌋₊ < N := by
        rw [Nat.floor_lt (by positivity)]
        rw [div_lt_iff₀ hb]
        have := (div_lt_iff₀ hNR).mp h1
        nlinarith
      omega
  have hlow : ∀ j < P.length,
      ((⌊1 / binMax (P.getD j [])⌋₊ : ℕ) : ℝ)⁻¹ ≤ hw (binMax (P.getD j [])) (P.getD j []) := by
    intro j hj
    obtain ⟨hm, h1, h2⟩ := hbin j hj
    have hb : 0 < binMax (P.getD j []) := lt_of_le_of_lt (by positivity) h1
    have hpb := piece_of_floor hb (by linarith)
    have hgw : gw (binMax (P.getD j [])) (binMax (P.getD j [])) =
        ((⌊1 / binMax (P.getD j [])⌋₊ : ℕ) : ℝ)⁻¹ := by
      unfold gw
      rw [if_pos ⟨_, hpb, hpb⟩]
      rfl
    rw [← hgw]
    unfold hw
    exact List.single_le_sum (fun x hx => by
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
      exact gw_nonneg _ _) _ (List.mem_map_of_mem hm)
  classical
  set τ : ℕ → ℕ := fun j => ⌊1 / binMax (P.getD j [])⌋₊ with hτdef
  set Last := (Finset.range P.length).filter
    (fun j => ∀ j', j < j' → j' < P.length → τ j' ≠ τ j) with hLast
  have hper : ∀ j ∈ Finset.range P.length,
      (1:ℝ) - (if j ∈ Last then ((τ j : ℝ) - 1) / (τ j : ℝ) else 0) ≤
        ((P.getD j []).map (gw (binMax (P.getD j [])))).sum := by
    intro j hj
    have hj' : j < P.length := Finset.mem_range.mp hj
    have hτj := Finset.mem_Icc.mp (hτ j hj')
    have hτpos : (0:ℝ) < (τ j : ℝ) := by
      have : 2 ≤ τ j := hτj.1
      have : (2:ℝ) ≤ (τ j : ℝ) := by exact_mod_cast this
      linarith
    split_ifs with hL
    · have := hlow j hj'
      have e : (1:ℝ) - ((τ j : ℝ) - 1) / (τ j : ℝ) = ((τ j : ℕ) : ℝ)⁻¹ := by
        field_simp
        ring
      rw [e]
      exact this
    · rcases hI.full j hj' with h | h
      · simp only [sub_zero]; exact h
      · exact absurd (Finset.mem_filter.mpr ⟨hj, h⟩) hL
  have hsum1 := Finset.sum_le_sum hper
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter] at hsum1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum1
  have hfilt : (Finset.range P.length).filter (fun j => j ∈ Last) = Last := by
    ext j; simp [hLast]
  rw [hfilt] at hsum1
  have hinj : Set.InjOn τ Last := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, hLast, Finset.mem_range] at ha hb
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab.symm (ha.2 b h hb.1)
    · exact h
    · exact absurd hab (hb.2 a h ha.1)
  have himg : ∑ j ∈ Last, ((τ j : ℝ) - 1) / (τ j : ℝ) =
      ∑ k ∈ Last.image τ, ((k : ℝ) - 1) / (k : ℝ) := (Finset.sum_image (f := fun k : ℕ => ((k:ℝ) - 1) / (k:ℝ)) hinj).symm
  have hsub : Last.image τ ⊆ Finset.Icc 2 (N - 1) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact hτ j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  have hle : ∑ k ∈ Last.image τ, ((k : ℝ) - 1) / (k : ℝ) ≤
      ∑ k ∈ Finset.Icc 2 (N - 1), ((k : ℝ) - 1) / (k : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro k hk _
    have : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have h2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast this
    apply div_nonneg <;> linarith
  linarith

end FFBAux_ffb69a58

open FFBAux_ffb69a58 in
open BinPacking.SmallItems in
theorem ffb_basic_weight_ge (N : ℕ) (hN : 4 ≤ N) (L : List ℝ) (hL : IsList L)
    (hrange : ∀ a ∈ L, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2) :
    ∑ i ∈ basic L, w1 ((sortDesc L).get i) ≥
      (FFD L : ℝ) - ∑ j ∈ Finset.Icc 2 (N - 1), ((j : ℝ) - 1) / (j : ℝ) := by
  have hN0 : 0 < N := by omega
  have hperm : (sortDesc L).Perm L := List.mergeSort_perm _ _
  have hs : (sortDesc L).Pairwise (fun a b => b ≤ a) := by
    have := List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
      (fun a b c h1 h2 => by simp at h1 h2 ⊢; linarith)
      (fun a b => by simp; exact le_total b a) L
    exact this.imp (fun h => by simpa using h)
  have hrS : ∀ x ∈ sortDesc L, 1/(N:ℝ) < x ∧ x ≤ 1/2 :=
    fun x hx => hrange x (hperm.mem_iff.mp hx)
  have hr2 : ∀ x ∈ sortDesc L, 0 < x ∧ x ≤ 1/2 := fun x hx =>
    ⟨lt_of_le_of_lt (by positivity) (hrS x hx).1, (hrS x hx).2⟩
  have hI := inv_all (sortDesc L) hs hr2 (sortDesc L).length le_rfl
  rw [List.take_length] at hI
  have hid := identity (sortDesc L) (ffPack (sortDesc L)) (sortDesc L).length le_rfl
  rw [List.take_length] at hid
  have hfin := final_bound N hN0 (sortDesc L) hrS (ffPack (sortDesc L)) hI
  have hlhs : ∑ i ∈ basic L, w1 ((sortDesc L).get i) =
      ∑ i ∈ Finset.range (sortDesc L).length, (if h : i < (sortDesc L).length then
          gw (binMax ((ffPack (sortDesc L)).getD (ffBinOf (sortDesc L) ⟨i, h⟩) []))
            (sortDesc L)[i] else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if h : i < (sortDesc L).length then
          gw (binMax ((ffPack (sortDesc L)).getD (ffBinOf (sortDesc L) ⟨i, h⟩) []))
            (sortDesc L)[i] else 0)]
    unfold basic
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rw [dif_pos i.isLt]
    unfold gw ffdBin ffdPack IsKBin
    simp only [Fin.eta, List.get_eq_getElem]
  have hFFD : (FFD L : ℝ) = ((ffPack (sortDesc L)).length : ℝ) := rfl
  rw [ge_iff_le, hlhs, ← hid, hFFD]
  exact hfin



namespace C4Aux_998ce8a1
open BinPacking.SmallItems

lemma getD_lt {α : Type} (P : List α) (j : ℕ) (d : α) (hj : j < P.length) : P.getD j d = P[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl

lemma getD_ge {α : Type} (P : List α) (j : ℕ) (d : α) (hj : P.length ≤ j) : P.getD j d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]; rfl

lemma getD_placeAt {P : List (List ℝ)} {c : ℕ} {y : ℝ} (hc : c ≤ P.length) (b : ℕ) :
    (placeAt P c y).getD b [] = if b = c then P.getD b [] ++ [y] else P.getD b [] := by
  rcases lt_or_eq_of_le hc with hc | rfl
  · simp only [placeAt, hc, if_true]
    rcases lt_or_ge b P.length with hb | hb
    · rw [getD_lt _ _ _ (by simpa using hb), getD_lt _ _ _ hb, List.getElem_mapIdx]
    · rw [getD_ge _ _ _ (by simpa using hb), getD_ge _ _ _ hb]
      have : b ≠ c := by omega
      simp [this]
  · simp only [placeAt, lt_irrefl, if_false]
    rcases lt_trichotomy b P.length with hb | hb | hb
    · rw [getD_lt _ _ _ (by simp; omega), getD_lt _ _ _ hb, List.getElem_append_left hb]
      simp [Nat.ne_of_lt hb]
    · subst hb
      rw [getD_lt _ _ _ (by simp), getD_ge _ _ _ le_rfl]
      simp
    · rw [getD_ge _ _ _ (by simp; omega), getD_ge _ _ _ (by omega)]
      simp [Nat.ne_of_gt hb]

lemma ffPack_succ (S : List ℝ) (t : ℕ) (ht : t < S.length) :
    ffPack (S.take (t+1)) =
      placeAt (ffPack (S.take t)) (ffChoice (ffPack (S.take t)) S[t]) S[t] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some]
  unfold ffPack
  rw [List.foldl_append]
  rfl

lemma ffChoice_le (P : List (List ℝ)) (a : ℝ) : ffChoice P a ≤ P.length := by
  unfold ffChoice; exact List.findIdx_le_length

lemma ffChoice_fits (P : List (List ℝ)) (a : ℝ) (h : ffChoice P a < P.length) :
    (P.getD (ffChoice P a) []).sum + a ≤ 1 := by
  unfold ffChoice at h ⊢
  rw [getD_lt _ _ _ h]
  exact of_decide_eq_true (List.findIdx_getElem (w := h))

/-- Bin `b` of the partial packing collects exactly the items whose recorded bin is `b`. -/
lemma binsum (S : List ℝ) (b : ℕ) (t : ℕ) (ht : t ≤ S.length) :
    ∑ i ∈ Finset.range t, (if h : i < S.length then
        (if ffBinOf S ⟨i, h⟩ = b then S[i] else 0) else 0) =
      ((ffPack (S.take t)).getD b []).sum := by
  induction t with
  | zero => simp [ffPack]
  | succ t ih =>
    have ht' : t < S.length := by omega
    rw [Finset.sum_range_succ, ih (by omega), dif_pos ht', ffPack_succ S t ht',
      getD_placeAt (ffChoice_le _ _)]
    have hbin : ffBinOf S ⟨t, ht'⟩ = ffChoice (ffPack (S.take t)) S[t] := rfl
    rw [hbin]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp

/-- Every bin of a first-fit packing has sum at most `1`. -/
lemma bin_le_one (S : List ℝ) (hS : ∀ a ∈ S, a ≤ 1) (t : ℕ) (ht : t ≤ S.length) (b : ℕ) :
    ((ffPack (S.take t)).getD b []).sum ≤ 1 := by
  induction t generalizing b with
  | zero => simp [ffPack]
  | succ t ih =>
    have ht' : t < S.length := by omega
    rw [ffPack_succ S t ht', getD_placeAt (ffChoice_le _ _)]
    split_ifs with hb
    · rw [List.sum_append, List.sum_singleton]
      rcases lt_or_eq_of_le (ffChoice_le (ffPack (S.take t)) S[t]) with hc | hc
      · rw [hb]; exact ffChoice_fits _ _ hc
      · rw [hb, hc, getD_ge _ _ _ le_rfl]
        simpa using hS _ (List.getElem_mem ht')
    · exact ih (by omega) b

lemma fin_binsum_le (S : List ℝ) (hS : ∀ a ∈ S, a ≤ 1) (b : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin S.length => ffBinOf S i = b), S.get i ≤ 1 := by
  rw [Finset.sum_filter]
  have h := binsum S b S.length le_rfl
  rw [List.take_length] at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  have e : ∀ i : Fin S.length, (if ffBinOf S i = b then S.get i else 0) =
      (if h : (i : ℕ) < S.length then
        (if ffBinOf S ⟨i, h⟩ = b then S[(i : ℕ)] else 0) else 0) := by
    intro i
    rw [dif_pos i.isLt]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => e i), h]
  have := bin_le_one S hS S.length le_rfl b
  rwa [List.take_length] at this

lemma piece_pos {k : ℕ} {x : ℝ} (h : IsPiece k x) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨h1, h2⟩ := h
    simp at h1 h2
    linarith
  · exact hk

lemma floor_eq_of_piece {k : ℕ} {x : ℝ} (h : IsPiece k x) : ⌊1 / x⌋₊ = k := by
  have hk := piece_pos h
  obtain ⟨h1, h2⟩ := h
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hx : 0 < x := lt_trans (by positivity) h1
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [le_div_iff₀ hx]
    have := (le_div_iff₀ hk').mp h2
    nlinarith
  · rw [div_lt_iff₀ hx]
    have := (div_lt_iff₀ (by positivity : (0:ℝ) < k+1)).mp h1
    nlinarith

lemma piece_of_floor {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : IsPiece ⌊1 / x⌋₊ x := by
  have h1x : (1:ℝ) ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
  have hk1 : 1 ≤ ⌊1 / x⌋₊ := Nat.le_floor (by simpa using h1x)
  have hk' : (0:ℝ) < (⌊1 / x⌋₊ : ℝ) := by exact_mod_cast hk1
  have hfl : ((⌊1 / x⌋₊ : ℕ) : ℝ) ≤ 1 / x := Nat.floor_le (by positivity)
  have hlt : 1 / x < ((⌊1 / x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  constructor
  · rw [div_lt_iff₀ (by positivity)]
    have := (div_lt_iff₀ hx).mp hlt
    nlinarith
  · rw [le_div_iff₀ hk']
    have := (le_div_iff₀ hx).mp hfl
    nlinarith

lemma le_binMax {x : ℝ} {B : List ℝ} (h : x ∈ B) : x ≤ binMax B := by
  induction B with
  | nil => simp at h
  | cons b B ih =>
    simp only [binMax, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma binMax_mem {B : List ℝ} (hne : B ≠ []) (hpos : ∀ x ∈ B, 0 ≤ x) : binMax B ∈ B := by
  induction B with
  | nil => exact absurd rfl hne
  | cons b B ih =>
    simp only [binMax, List.foldr_cons] at ih ⊢
    by_cases hB : B = []
    · subst hB
      simp [max_eq_left (hpos b (by simp))]
    · rcases max_choice b (B.foldr max 0) with h | h
      · rw [h]; simp
      · rw [h]
        exact List.mem_cons_of_mem _ (ih hB (fun x hx => hpos x (List.mem_cons_of_mem _ hx)))


/-! ### Stage 1: FFD structure facts -/

lemma bin_mem (S : List ℝ) (t : ℕ) (ht : t ≤ S.length) (b : ℕ) (x : ℝ) :
    x ∈ (ffPack (S.take t)).getD b [] ↔
      ∃ p : Fin S.length, (p : ℕ) < t ∧ ffBinOf S p = b ∧ S.get p = x := by
  induction t with
  | zero => simp [ffPack]
  | succ t ih =>
    have ht' : t < S.length := by omega
    rw [ffPack_succ S t ht', getD_placeAt (ffChoice_le _ _)]
    have hbin : ffBinOf S ⟨t, ht'⟩ = ffChoice (ffPack (S.take t)) S[t] := rfl
    split_ifs with hb
    · rw [List.mem_append, ih (by omega), List.mem_singleton]
      constructor
      · rintro (⟨p, hp, hpb, hpx⟩ | hx)
        · exact ⟨p, by omega, hpb, hpx⟩
        · exact ⟨⟨t, ht'⟩, by simp, by rw [hbin, hb], by simp [hx]⟩
      · rintro ⟨p, hp, hpb, hpx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | hp
        · exact Or.inl ⟨p, hp, hpb, hpx⟩
        · right
          have : p = ⟨t, ht'⟩ := Fin.ext hp
          subst this
          rw [← hpx]; simp
    · rw [ih (by omega)]
      constructor
      · rintro ⟨p, hp, hpb, hpx⟩; exact ⟨p, by omega, hpb, hpx⟩
      · rintro ⟨p, hp, hpb, hpx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | hp
        · exact ⟨p, hp, hpb, hpx⟩
        · exfalso
          have : p = ⟨t, ht'⟩ := Fin.ext hp
          subst this
          exact hb (by rw [← hpb, hbin])

lemma binsum_fin (S : List ℝ) (b : ℕ) (t : ℕ) (ht : t ≤ S.length) :
    ((ffPack (S.take t)).getD b []).sum =
      ∑ p ∈ Finset.univ.filter (fun p : Fin S.length => (p : ℕ) < t ∧ ffBinOf S p = b), S.get p := by
  induction t with
  | zero => simp [ffPack]
  | succ t ih =>
    have ht' : t < S.length := by omega
    rw [ffPack_succ S t ht', getD_placeAt (ffChoice_le _ _)]
    have hbin : ffBinOf S ⟨t, ht'⟩ = ffChoice (ffPack (S.take t)) S[t] := rfl
    split_ifs with hb
    · rw [List.sum_append, List.sum_singleton, ih (by omega)]
      have hset : Finset.univ.filter (fun p : Fin S.length => (p : ℕ) < t + 1 ∧ ffBinOf S p = b) =
          insert ⟨t, ht'⟩ (Finset.univ.filter (fun p : Fin S.length => (p : ℕ) < t ∧ ffBinOf S p = b)) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨hp, hpb⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | hp
          · exact Or.inr ⟨hp, hpb⟩
          · exact Or.inl (Fin.ext hp)
        · rintro (rfl | ⟨hp, hpb⟩)
          · exact ⟨by simp, by rw [hbin, hb]⟩
          · exact ⟨by omega, hpb⟩
      rw [hset, Finset.sum_insert (by simp), add_comm]
      simp
    · rw [ih (by omega)]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hp, hpb⟩; exact ⟨by omega, hpb⟩
      · rintro ⟨hp, hpb⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | hp
        · exact ⟨hp, hpb⟩
        · exfalso
          have : p = ⟨t, ht'⟩ := Fin.ext hp
          subst this
          exact hb (by rw [← hpb, hbin])

/-- First fit skipped bin `b` for item `j`: the level of `b` at that time plus `S j` exceeds `1`. -/
lemma skip_sum (S : List ℝ) (j : Fin S.length) (b : ℕ) (hb : b < ffBinOf S j) :
    1 < (∑ p ∈ Finset.univ.filter (fun p : Fin S.length => p < j ∧ ffBinOf S p = b), S.get p)
      + S.get j := by
  have hbl : b < (ffPack (S.take j)).length := lt_of_lt_of_le hb (ffChoice_le _ _)
  have h1 : 1 < ((ffPack (S.take j)).getD b []).sum + S.get j := by
    have hb' : b < ffChoice (ffPack (S.take j)) (S.get j) := hb
    unfold ffChoice at hb'
    rw [getD_lt _ _ _ hbl]
    have h := List.not_of_lt_findIdx hb'
    simp only [decide_eq_false_iff_not, not_le] at h
    exact h
  rw [binsum_fin S b j (le_of_lt j.isLt)] at h1
  have e : Finset.univ.filter (fun p : Fin S.length => (p : ℕ) < (j : ℕ) ∧ ffBinOf S p = b) =
      Finset.univ.filter (fun p : Fin S.length => p < j ∧ ffBinOf S p = b) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Iff.rfl
  rwa [e] at h1

lemma exists_before (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) (j : Fin S.length) (b : ℕ)
    (hb : b < ffBinOf S j) : ∃ p : Fin S.length, p < j ∧ ffBinOf S p = b := by
  have h := skip_sum S j b hb
  have hj := (hS _ (List.get_mem S j)).2
  by_contra hne
  push Not at hne
  have : Finset.univ.filter (fun p : Fin S.length => p < j ∧ ffBinOf S p = b) = ∅ := by
    ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    exact fun ⟨h1, h2⟩ => hne p h1 h2
  rw [this, Finset.sum_empty] at h
  linarith

noncomputable def ty (x : ℝ) : ℕ := ⌊1 / x⌋₊

lemma ty_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : ty y ≤ ty x := by
  unfold ty; exact Nat.floor_le_floor (one_div_le_one_div_of_le hx hxy)

lemma mul_ty_le {x : ℝ} (hx : 0 < x) : x * (ty x : ℝ) ≤ 1 := by
  unfold ty
  have := Nat.floor_le (le_of_lt (one_div_pos.mpr hx))
  have h2 : x * (⌊1 / x⌋₊ : ℝ) ≤ x * (1 / x) := mul_le_mul_of_nonneg_left this hx.le
  rwa [mul_one_div_cancel hx.ne'] at h2

lemma lt_mul_ty_succ {x : ℝ} (hx : 0 < x) : 1 < x * ((ty x : ℝ) + 1) := by
  unfold ty
  have := Nat.lt_floor_add_one (1 / x)
  have h2 : x * (1 / x) < x * ((⌊1 / x⌋₊ : ℝ) + 1) := mul_lt_mul_of_pos_left this hx
  rwa [mul_one_div_cancel hx.ne'] at h2

lemma one_le_ty {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : 1 ≤ ty x := by
  unfold ty
  exact Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hx]; linarith)

lemma get_anti (S : List ℝ) (hs : S.Pairwise (fun a b => b ≤ a)) {p q : Fin S.length}
    (hpq : p ≤ q) : S.get q ≤ S.get p := by
  rcases lt_or_eq_of_le hpq with h | rfl
  · exact List.pairwise_iff_get.mp hs p q h
  · exact le_rfl

lemma lt_of_get_lt (S : List ℝ) (hs : S.Pairwise (fun a b => b ≤ a)) {p q : Fin S.length}
    (h : S.get p < S.get q) : q < p := by
  by_contra hc
  push Not at hc
  exact absurd (get_anti S hs hc) (not_le.mpr h)

/-- Basic in the bin-local sense: no item of the same bin has a smaller type. -/
def isB (S : List ℝ) (i : Fin S.length) : Prop :=
  ∀ p : Fin S.length, ffBinOf S p = ffBinOf S i → ty (S.get i) ≤ ty (S.get p)

lemma isB_same_type (S : List ℝ) {i i' : Fin S.length} (hi : isB S i) (hi' : isB S i')
    (h : ffBinOf S i = ffBinOf S i') : ty (S.get i) = ty (S.get i') :=
  le_antisymm (hi i' h.symm) (hi' i h)

/-- Bins holding basic items of a smaller type come first. -/
lemma bin_lt_of_ty_lt (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) {i j : Fin S.length} (hi : isB S i) (hj : isB S j)
    (hij : ty (S.get i) < ty (S.get j)) : ffBinOf S i < ffBinOf S j := by
  by_contra hc
  push Not at hc
  rcases lt_or_eq_of_le hc with hlt | heq
  · obtain ⟨p, hpi, hpb⟩ := exists_before S hS i (ffBinOf S j) hlt
    have h1 : ty (S.get p) ≤ ty (S.get i) :=
      ty_anti (hS _ (List.get_mem S i)).1 (get_anti S hs hpi.le)
    have h2 := hj p hpb
    omega
  · have := hj i heq.symm
    omega

lemma card_le_of_bin (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) (b c : ℕ)
    (A : Finset (Fin S.length))
    (hA : ∀ p ∈ A, ffBinOf S p = b ∧ 1 / ((c : ℝ) + 1) < S.get p) : A.card ≤ c := by
  have hsub : A ⊆ Finset.univ.filter (fun i : Fin S.length => ffBinOf S i = b) := by
    intro p hp; simp [(hA p hp).1]
  have hsum1 : ∑ p ∈ A, S.get p ≤ 1 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
    · intro p _ _; exact (hS _ (List.get_mem S p)).1.le
    · exact fin_binsum_le S (fun a ha => (hS a ha).2) b
  rcases A.eq_empty_or_nonempty with hE | hne
  · rw [hE]; simp
  have hlow : ∑ _p ∈ A, 1 / ((c : ℝ) + 1) < ∑ p ∈ A, S.get p :=
    Finset.sum_lt_sum_of_nonempty hne (fun p hp => (hA p hp).2)
  rw [Finset.sum_const, nsmul_eq_mul] at hlow
  have hc1 : (0 : ℝ) < (c : ℝ) + 1 := by positivity
  have h := lt_of_lt_of_le hlow hsum1
  rw [mul_one_div, div_lt_one hc1] at h
  have : A.card < c + 1 := by exact_mod_cast h
  omega

/-- Basic items of a later bin of the same type are no larger. -/
lemma later_basic_le (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) {i p : Fin S.length} (hi : isB S i)
    (hty : ty (S.get p) = ty (S.get i)) (hbin : ffBinOf S i < ffBinOf S p) :
    S.get p ≤ S.get i := by
  by_contra hc
  push Not at hc
  have hpi : p < i := lt_of_get_lt S hs hc
  set τ := ty (S.get i) with hτ
  have hxi := (hS _ (List.get_mem S i)).1
  have hxp := (hS _ (List.get_mem S p)).1
  have hτ1 : 1 ≤ τ := one_le_ty hxi (hS _ (List.get_mem S i)).2
  have hτpos : (0 : ℝ) < τ := by exact_mod_cast hτ1
  set R := Finset.univ.filter (fun r : Fin S.length => r < p ∧ ffBinOf S r = ffBinOf S i) with hR
  have hskip := skip_sum S p (ffBinOf S i) hbin
  -- each item of R has size ≤ 1/τ
  have hRle : ∀ r ∈ R, S.get r * τ ≤ 1 := by
    intro r hr
    rw [hR, Finset.mem_filter] at hr
    have h1 := hi r hr.2.2
    have hxr := (hS _ (List.get_mem S r)).1
    have h2 := mul_ty_le hxr
    have h3 : (τ : ℝ) ≤ (ty (S.get r) : ℝ) := by exact_mod_cast h1
    nlinarith
  have hple : S.get p * τ ≤ 1 := by rw [← hty]; exact mul_ty_le hxp
  have hsumR : (∑ r ∈ R, S.get r) * τ ≤ R.card := by
    rw [Finset.sum_mul]
    calc ∑ r ∈ R, S.get r * τ ≤ ∑ _r ∈ R, (1 : ℝ) := Finset.sum_le_sum hRle
      _ = R.card := by simp
  have hcard : τ ≤ R.card := by
    have : (τ : ℝ) < R.card + 1 := by nlinarith
    have : τ < R.card + 1 := by exact_mod_cast this
    omega
  -- R ∪ {i} lies in bin i, all items > 1/(τ+1)
  have hlow_i : 1 / ((τ : ℝ) + 1) < S.get i := by
    have := lt_mul_ty_succ hxi
    rw [div_lt_iff₀ (by positivity)]; linarith
  have hA : ∀ r ∈ insert i R, ffBinOf S r = ffBinOf S i ∧ 1 / ((τ : ℝ) + 1) < S.get r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact ⟨rfl, hlow_i⟩
    · rw [hR, Finset.mem_filter] at hr
      refine ⟨hr.2.2, lt_of_lt_of_le hlow_i (le_trans hc.le (get_anti S hs hr.2.1.le))⟩
  have hiR : i ∉ R := by
    rw [hR, Finset.mem_filter]; intro h; exact absurd (lt_trans h.2.1 hpi) (lt_irrefl _)
  have := card_le_of_bin S hS (ffBinOf S i) τ (insert i R) hA
  rw [Finset.card_insert_of_notMem hiR] at this
  omega

lemma ty_lt_of_rel (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) {i j : Fin S.length}
    (hrel : (ty (S.get i) : ℝ) * S.get i + S.get j ≤ 1) : ty (S.get i) < ty (S.get j) := by
  have hxi := (hS _ (List.get_mem S i)).1
  have hxj := (hS _ (List.get_mem S j)).1
  have h1 := lt_mul_ty_succ hxi
  have h2 := mul_ty_le hxj
  by_contra hc
  push Not at hc
  have h3 : (ty (S.get j) : ℝ) ≤ ty (S.get i) := by exact_mod_cast hc
  -- S j < 1/(τ+1) and S j * ty j ≤ 1 contradict ty j ≤ τ only via S j > 1/(ty j + 1)
  have h4 := lt_mul_ty_succ hxj
  have h5 : S.get j * ((ty (S.get i) : ℝ) + 1) < 1 := by nlinarith
  nlinarith

/-- (G*) If `i` is basic, a later bin holds a basic item `i'` of the same type, and `j` is basic with
`τ x_i + x_j ≤ 1`, then that later bin contains a non-basic item placed before `j`. -/
lemma gstar (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) {i i' j : Fin S.length} (hi : isB S i) (hi' : isB S i')
    (hj : isB S j) (hty : ty (S.get i') = ty (S.get i)) (hbin : ffBinOf S i < ffBinOf S i')
    (hrel : (ty (S.get i) : ℝ) * S.get i + S.get j ≤ 1) :
    ∃ f : Fin S.length, f < j ∧ ffBinOf S f = ffBinOf S i' ∧ ¬ isB S f := by
  have htj := ty_lt_of_rel S hS hrel
  have hb : ffBinOf S i' < ffBinOf S j := bin_lt_of_ty_lt S hS hs hi' hj (by rw [hty]; exact htj)
  have hskip := skip_sum S j (ffBinOf S i') hb
  by_contra hne
  push Not at hne
  set R := Finset.univ.filter (fun r : Fin S.length => r < j ∧ ffBinOf S r = ffBinOf S i') with hR
  set τ := ty (S.get i)
  have hxi := (hS _ (List.get_mem S i)).1
  have hRB : ∀ r ∈ R, isB S r ∧ ty (S.get r) = τ ∧ S.get r ≤ S.get i := by
    intro r hr
    rw [hR, Finset.mem_filter] at hr
    have hrB := hne r hr.2.1 hr.2.2
    have hrt : ty (S.get r) = τ := by rw [isB_same_type S hrB hi' hr.2.2, hty]
    exact ⟨hrB, hrt, later_basic_le S hS hs hi hrt (by rw [hr.2.2]; exact hbin)⟩
  have hcard : R.card ≤ τ := by
    apply card_le_of_bin S hS (ffBinOf S i') τ R
    intro r hr
    have hr' := hr
    rw [hR, Finset.mem_filter] at hr'
    refine ⟨hr'.2.2, ?_⟩
    have := lt_mul_ty_succ (hS _ (List.get_mem S r)).1
    rw [(hRB r hr).2.1] at this
    rw [div_lt_iff₀ (by positivity)]; linarith
  have hsum : ∑ r ∈ R, S.get r ≤ τ * S.get i := by
    calc ∑ r ∈ R, S.get r ≤ ∑ _r ∈ R, S.get i := Finset.sum_le_sum (fun r hr => (hRB r hr).2.2)
      _ = R.card * S.get i := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ τ * S.get i := by
          apply mul_le_mul_of_nonneg_right _ hxi.le
          exact_mod_cast hcard
  linarith

/-! ### Stage 2a: the cover `pc` (definitions and structural facts) -/

noncomputable def wt (S : List ℝ) (i : Fin S.length) : ℝ := w1 (S.get i)

lemma wt_eq (S : List ℝ) (i : Fin S.length) : wt S i = ((ty (S.get i) : ℕ) : ℝ)⁻¹ := rfl

lemma wt_nonneg (S : List ℝ) (i : Fin S.length) : 0 ≤ wt S i := by
  rw [wt_eq]; positivity

lemma wt_le_one (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) (i : Fin S.length) : wt S i ≤ 1 := by
  rw [wt_eq]
  have h := one_le_ty (hS _ (List.get_mem S i)).1 (hS _ (List.get_mem S i)).2
  have h' : (1 : ℝ) ≤ (ty (S.get i) : ℝ) := by exact_mod_cast h
  exact inv_le_one_of_one_le₀ h'

lemma wt_anti (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) {p q : Fin S.length}
    (h : S.get q ≤ S.get p) : wt S q ≤ wt S p := by
  rw [wt_eq, wt_eq]
  have h1 := ty_anti (hS _ (List.get_mem S q)).1 h
  have h2 := one_le_ty (hS _ (List.get_mem S p)).1 (hS _ (List.get_mem S p)).2
  have h1' : (ty (S.get p) : ℝ) ≤ (ty (S.get q) : ℝ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) < (ty (S.get p) : ℝ) := by exact_mod_cast h2
  exact inv_anti₀ h2' h1'

def Ed (S : List ℝ) (i j : Fin S.length) : Prop :=
  i < j ∧ (ty (S.get i) : ℝ) * S.get i + S.get j ≤ 1

def lastB (S : List ℝ) (i : Fin S.length) : Prop :=
  isB S i ∧ ∀ i' : Fin S.length, isB S i' → ty (S.get i') = ty (S.get i) →
    ffBinOf S i' ≤ ffBinOf S i

open Classical in
noncomputable def tok (S : List ℝ) (N : ℕ) (i : Fin S.length) : ℝ :=
  if ty (S.get i) + 2 ≤ N then wt S i / ((ty (S.get i) : ℝ) + 1) else 0

lemma tok_nonneg (S : List ℝ) (N : ℕ) (i : Fin S.length) : 0 ≤ tok S N i := by
  unfold tok; split_ifs
  · exact div_nonneg (wt_nonneg S i) (by positivity)
  · exact le_rfl

noncomputable def mx {ι : Type} (s : Finset ι) (f : ι → ℝ) : ℝ := s.fold max 0 f

lemma le_mx {ι : Type} {s : Finset ι} {f : ι → ℝ} {j : ι} (hj : j ∈ s) : f j ≤ mx s f := by
  unfold mx; exact (Finset.le_fold_max _).mpr (Or.inr ⟨j, hj, le_rfl⟩)

lemma mx_nonneg {ι : Type} (s : Finset ι) (f : ι → ℝ) : 0 ≤ mx s f := by
  unfold mx; exact (Finset.le_fold_max _).mpr (Or.inl le_rfl)

lemma mx_le {ι : Type} {s : Finset ι} {f : ι → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j ∈ s, f j ≤ c) : mx s f ≤ c := by
  unfold mx; exact (Finset.fold_max_le _).mpr ⟨hc, h⟩

lemma mx_pos {ι : Type} {s : Finset ι} {f : ι → ℝ} (h : 0 < mx s f) :
    ∃ j ∈ s, mx s f ≤ f j := by
  have := (Finset.le_fold_max (s := s) (b := 0) (f := f) (mx s f)).mp le_rfl
  rcases this with h0 | h1
  · exact absurd h0 (not_le.mpr h)
  · exact h1

open Classical in
noncomputable def Fop (S : List ℝ) (N : ℕ) (g : Fin S.length → ℝ) (i : Fin S.length) : ℝ :=
  if lastB S i then tok S N i
  else if isB S i then
    mx (Finset.univ.filter (fun j => isB S j ∧ Ed S i j)) (fun j => wt S i * wt S j - g j)
  else 0

noncomputable def pb (S : List ℝ) (N : ℕ) : Fin S.length → ℝ :=
  (Fop S N)^[S.length] (fun _ => 0)

lemma Fop_local (S : List ℝ) (N : ℕ) (g g' : Fin S.length → ℝ) (i : Fin S.length)
    (h : ∀ j, i < j → g j = g' j) : Fop S N g i = Fop S N g' i := by
  unfold Fop
  split_ifs
  · rfl
  · unfold mx
    apply Finset.fold_congr
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [h j hj.2.1]
  · rfl

lemma iter_stable (S : List ℝ) (N : ℕ) : ∀ (k : ℕ) (i : Fin S.length), S.length - i = k →
    ∀ m, k ≤ m → (Fop S N)^[m] (fun _ => 0) i = (Fop S N)^[m + 1] (fun _ => 0) i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hik m hm
    have hk1 : 1 ≤ k := by have := i.isLt; omega
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    apply Fop_local
    intro j hij
    have hj : S.length - j < k := by
      have := j.isLt; have : (i : ℕ) < j := hij; omega
    exact ih (S.length - j) hj j rfl m' (by have : (i : ℕ) < j := hij; omega)

lemma pb_fix (S : List ℝ) (N : ℕ) (i : Fin S.length) : pb S N i = Fop S N (pb S N) i := by
  unfold pb
  rw [← Function.iterate_succ_apply' (Fop S N)]
  exact iter_stable S N (S.length - i) i rfl S.length (by omega)

lemma pb_lastB (S : List ℝ) (N : ℕ) {i : Fin S.length} (h : lastB S i) : pb S N i = tok S N i := by
  rw [pb_fix]; unfold Fop; rw [if_pos h]

open Classical in
lemma pb_BN (S : List ℝ) (N : ℕ) {i : Fin S.length} (hb : isB S i) (hl : ¬ lastB S i) :
    pb S N i = mx (Finset.univ.filter (fun j => isB S j ∧ Ed S i j))
      (fun j => wt S i * wt S j - pb S N j) := by
  rw [pb_fix]; unfold Fop; rw [if_neg hl, if_pos hb]

lemma pb_nonneg (S : List ℝ) (N : ℕ) (i : Fin S.length) : 0 ≤ pb S N i := by
  rw [pb_fix]; unfold Fop
  split_ifs
  · exact tok_nonneg S N i
  · exact mx_nonneg _ _
  · exact le_rfl

def firstSur (S : List ℝ) (f : Fin S.length) : Prop :=
  ¬ isB S f ∧ ∀ g : Fin S.length, ¬ isB S g → ffBinOf S g = ffBinOf S f → f ≤ g

def nbOK (S : List ℝ) (i : Fin S.length) (b : ℕ) : Prop :=
  (∃ i' : Fin S.length, isB S i' ∧ ty (S.get i') = ty (S.get i) ∧ ffBinOf S i' = b) ∧
    ffBinOf S i < b ∧
    ∀ i' : Fin S.length, isB S i' → ty (S.get i') = ty (S.get i) → ffBinOf S i < ffBinOf S i' →
      b ≤ ffBinOf S i'

lemma nb_exists (S : List ℝ) {i : Fin S.length} (hb : isB S i) (hl : ¬ lastB S i) :
    ∃ b, nbOK S i b := by
  have hex : ∃ b, ∃ i' : Fin S.length, isB S i' ∧ ty (S.get i') = ty (S.get i) ∧
      ffBinOf S i' = b ∧ ffBinOf S i < b := by
    unfold lastB at hl
    push Not at hl
    obtain ⟨i', h1, h2, h3⟩ := hl hb
    exact ⟨_, i', h1, h2, rfl, h3⟩
  classical
  refine ⟨Nat.find hex, ?_, ?_, ?_⟩
  · obtain ⟨i', h1, h2, h3, -⟩ := Nat.find_spec hex
    exact ⟨i', h1, h2, h3⟩
  · obtain ⟨i', -, -, h3, h4⟩ := Nat.find_spec hex
    exact h4
  · intro i' h1 h2 h3
    exact Nat.find_min' hex ⟨i', h1, h2, rfl, h3⟩

lemma nb_unique (S : List ℝ) {i : Fin S.length} {b b' : ℕ} (h : nbOK S i b) (h' : nbOK S i b') :
    b = b' := by
  obtain ⟨⟨i1, h11, h12, h13⟩, h14, h15⟩ := h
  obtain ⟨⟨i2, h21, h22, h23⟩, h24, h25⟩ := h'
  apply le_antisymm
  · have := h15 i2 h21 h22 (by rw [h23]; exact h24); rwa [h23] at this
  · have := h25 i1 h11 h12 (by rw [h13]; exact h14); rwa [h13] at this

lemma firstSur_unique (S : List ℝ) {f f' : Fin S.length} (h : firstSur S f) (h' : firstSur S f')
    (hb : ffBinOf S f = ffBinOf S f') : f = f' :=
  le_antisymm (h.2 f' h'.1 hb.symm) (h'.2 f h.1 hb)

lemma firstSur_exists (S : List ℝ) {g0 : Fin S.length} (hg0 : ¬ isB S g0) :
    ∃ f : Fin S.length, firstSur S f ∧ ffBinOf S f = ffBinOf S g0 ∧ f ≤ g0 := by
  classical
  set T := Finset.univ.filter (fun g : Fin S.length => ¬ isB S g ∧ ffBinOf S g = ffBinOf S g0)
  have hT : T.Nonempty := ⟨g0, by simp [T, hg0]⟩
  obtain ⟨hmem, hmin⟩ := (Finset.min'_mem T hT), (fun g hg => Finset.min'_le T g hg)
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  refine ⟨T.min' hT, ⟨hmem.1, ?_⟩, hmem.2, hmin g0 (by simp [T, hg0])⟩
  intro g hg hgb
  exact hmin g (by simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hg, by rw [hgb, hmem.2]⟩)

lemma target_after (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) {i j : Fin S.length} (hb : isB S i) (hl : ¬ lastB S i)
    (hj : isB S j) (he : Ed S i j) :
    ∃ f : Fin S.length, firstSur S f ∧ nbOK S i (ffBinOf S f) ∧ f < j := by
  obtain ⟨b, hnb⟩ := nb_exists S hb hl
  obtain ⟨⟨i', h1, h2, h3⟩, h4, h5⟩ := hnb
  obtain ⟨f0, hf0j, hf0b, hf0B⟩ := gstar S hS hs hb h1 hj h2 (by rw [h3]; exact h4) he.2
  obtain ⟨f, hf, hfb, hff0⟩ := firstSur_exists S hf0B
  refine ⟨f, hf, ?_, lt_of_le_of_lt hff0 hf0j⟩
  rw [hfb, hf0b, h3]
  exact ⟨⟨i', h1, h2, h3⟩, h4, h5⟩

lemma target_lt (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) {i j f : Fin S.length} (hb : isB S i) (hl : ¬ lastB S i)
    (hj : isB S j) (he : Ed S i j) (hf : firstSur S f) (hnb : nbOK S i (ffBinOf S f)) : f < j := by
  obtain ⟨f', hf', hnb', hlt⟩ := target_after S hS hs hb hl hj he
  have hbb := nb_unique S hnb hnb'
  rw [firstSur_unique S hf hf' hbb]
  exact hlt

open Classical in
noncomputable def fib (S : List ℝ) (f : Fin S.length) : Finset (Fin S.length) :=
  Finset.univ.filter (fun i => isB S i ∧ ¬ lastB S i ∧ firstSur S f ∧ nbOK S i (ffBinOf S f))

lemma mem_fib (S : List ℝ) {f i : Fin S.length} :
    i ∈ fib S f ↔ isB S i ∧ ¬ lastB S i ∧ firstSur S f ∧ nbOK S i (ffBinOf S f) := by
  unfold fib; simp

lemma fib_same (S : List ℝ) {f i1 i2 : Fin S.length} (h1 : i1 ∈ fib S f) (h2 : i2 ∈ fib S f) :
    ty (S.get i1) = ty (S.get i2) ∧ ffBinOf S i1 = ffBinOf S i2 := by
  rw [mem_fib] at h1 h2
  obtain ⟨hb1, -, -, ⟨a1, ha1, ht1, hbn1⟩, hlt1, hmin1⟩ := h1
  obtain ⟨hb2, -, -, ⟨a2, ha2, ht2, hbn2⟩, hlt2, hmin2⟩ := h2
  have hty : ty (S.get i1) = ty (S.get i2) := by
    rw [← ht1, ← ht2]; exact isB_same_type S ha1 ha2 (by rw [hbn1, hbn2])
  refine ⟨hty, ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hmin1 i2 hb2 hty.symm h; omega
  · have := hmin2 i1 hb1 hty h; omega

lemma fib_card (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) {f i0 : Fin S.length}
    (h0 : i0 ∈ fib S f) : (fib S f).card ≤ ty (S.get i0) := by
  apply card_le_of_bin S hS (ffBinOf S i0) (ty (S.get i0))
  intro i hi
  obtain ⟨hty, hbin⟩ := fib_same S hi h0
  refine ⟨hbin, ?_⟩
  have := lt_mul_ty_succ (hS _ (List.get_mem S i)).1
  rw [hty] at this
  rw [div_lt_iff₀ (by positivity)]; linarith

lemma pb_le_fib (S : List ℝ) (N : ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) {f i : Fin S.length} (hi : i ∈ fib S f) :
    pb S N i ≤ wt S i * wt S f := by
  have hi' := (mem_fib S).mp hi
  rw [pb_BN S N hi'.1 hi'.2.1]
  apply mx_le (mul_nonneg (wt_nonneg S i) (wt_nonneg S f))
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  have hfj := target_lt S hS hs hi'.1 hi'.2.1 hj.1 hj.2 hi'.2.2.1 hi'.2.2.2
  have hw : wt S j ≤ wt S f := wt_anti S hS (get_anti S hs hfj.le)
  have := pb_nonneg S N j
  have := mul_le_mul_of_nonneg_left hw (wt_nonneg S i)
  linarith

open Classical in
noncomputable def pc (S : List ℝ) (N : ℕ) (i : Fin S.length) : ℝ :=
  if isB S i then pb S N i else wt S i - ∑ i' ∈ fib S i, pb S N i'

lemma fib_sum_le (S : List ℝ) (N : ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) (f : Fin S.length) :
    ∑ i' ∈ fib S f, pb S N i' ≤ wt S f := by
  rcases (fib S f).eq_empty_or_nonempty with hE | ⟨i0, h0⟩
  · rw [hE, Finset.sum_empty]; exact wt_nonneg S f
  · have hc := fib_card S hS h0
    have hτ := one_le_ty (hS _ (List.get_mem S i0)).1 (hS _ (List.get_mem S i0)).2
    have hτ' : (0 : ℝ) < (ty (S.get i0) : ℝ) := by exact_mod_cast hτ
    calc ∑ i' ∈ fib S f, pb S N i' ≤ ∑ _i' ∈ fib S f, wt S i0 * wt S f := by
          apply Finset.sum_le_sum
          intro i hi
          have := pb_le_fib S N hS hs hi
          rwa [wt_eq S i, (fib_same S hi h0).1, ← wt_eq] at this
      _ = (fib S f).card * (wt S i0 * wt S f) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (ty (S.get i0) : ℝ) * (wt S i0 * wt S f) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (wt_nonneg S i0) (wt_nonneg S f))
          exact_mod_cast hc
      _ = wt S f := by rw [wt_eq S i0]; field_simp

lemma pc_nonneg (S : List ℝ) (N : ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) (i : Fin S.length) : 0 ≤ pc S N i := by
  unfold pc; split_ifs
  · exact pb_nonneg S N i
  · linarith [fib_sum_le S N hS hs i]

/-! ### Stage 2b: every relation edge is covered -/

lemma ty_lt_N (S : List ℝ) (N : ℕ) (hN : 1 ≤ N) (hNS : ∀ a ∈ S, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2)
    (i : Fin S.length) : ty (S.get i) < N := by
  have hx := (hNS _ (List.get_mem S i)).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hxpos : 0 < S.get i := lt_trans (by positivity) hx
  unfold ty
  rw [Nat.floor_lt (by positivity)]
  exact (one_div_lt hxpos hN0).mpr hx

lemma two_le_ty (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1 / 2) (i : Fin S.length) :
    2 ≤ ty (S.get i) := by
  have hx := hS _ (List.get_mem S i)
  unfold ty
  exact Nat.le_floor (by rw [le_div_iff₀ hx.1]; push_cast; linarith [hx.2])

lemma wt_mul_ty (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) (i : Fin S.length) :
    (ty (S.get i) : ℝ) * wt S i = 1 := by
  rw [wt_eq]
  have h := one_le_ty (hS _ (List.get_mem S i)).1 (hS _ (List.get_mem S i)).2
  have h' : (ty (S.get i) : ℝ) ≠ 0 := by positivity
  field_simp

lemma wt_le_of_ty_ge (S : List ℝ) {i : Fin S.length} {t : ℕ} (h : t + 1 ≤ ty (S.get i)) :
    wt S i ≤ 1 / ((t : ℝ) + 1) := by
  rw [wt_eq, one_div]
  have h' : (t : ℝ) + 1 ≤ (ty (S.get i) : ℝ) := by exact_mod_cast h
  exact inv_anti₀ (by positivity) h'

lemma wt_eq_of_ty (S : List ℝ) {i j : Fin S.length} (h : ty (S.get i) = ty (S.get j)) :
    wt S i = wt S j := by rw [wt_eq, wt_eq, h]

open Classical in
/-- Edges whose first element is basic. -/
lemma edge_basic (S : List ℝ) (N : ℕ) (hN : 1 ≤ N) (hNS : ∀ a ∈ S, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2)
    (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) (hs : S.Pairwise (fun a b => b ≤ a))
    {i j : Fin S.length} (hi : isB S i) (he : Ed S i j) :
    wt S i * wt S j ≤ pc S N i + pc S N j := by
  have hpcj := pc_nonneg S N hS hs j
  have htij := ty_lt_of_rel S hS he.2
  have hpci : pc S N i = pb S N i := by unfold pc; rw [if_pos hi]
  by_cases hl : lastB S i
  · -- E1
    rw [hpci, pb_lastB S N hl]
    have hjN := ty_lt_N S N hN hNS j
    have hle : ty (S.get i) + 2 ≤ N := by omega
    unfold tok; rw [if_pos hle]
    have hwj := wt_le_of_ty_ge S (t := ty (S.get i)) htij
    have : wt S i * wt S j ≤ wt S i / ((ty (S.get i) : ℝ) + 1) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hwj (wt_nonneg S i)
    linarith
  · rw [hpci, pb_BN S N hi hl]
    by_cases hj : isB S j
    · -- E2
      have hpcj' : pc S N j = pb S N j := by unfold pc; rw [if_pos hj]
      have := le_mx (f := fun j => wt S i * wt S j - pb S N j)
        (s := Finset.univ.filter (fun j => isB S j ∧ Ed S i j)) (j := j)
        (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hj, he⟩)
      linarith
    · -- E3
      have hpcj' : pc S N j = wt S j - ∑ i' ∈ fib S j, pb S N i' := by unfold pc; rw [if_neg hj]
      rw [hpcj']
      set M := mx (Finset.univ.filter (fun j => isB S j ∧ Ed S i j))
        (fun j => wt S i * wt S j - pb S N j) with hM
      have hM0 : 0 ≤ M := mx_nonneg _ _
      have hwi1 := wt_le_one S hS i
      have hwj0 := wt_nonneg S j
      set P := (fib S j).filter (fun i' => 0 < pb S N i') with hP
      have hsumP : ∑ i' ∈ fib S j, pb S N i' = ∑ i' ∈ P, pb S N i' := by
        rw [hP, Finset.sum_filter_of_ne]
        intro x _ hx
        exact lt_of_le_of_ne (pb_nonneg S N x) (Ne.symm hx)
      rcases P.eq_empty_or_nonempty with hPe | hPne
      · rw [hsumP, hPe, Finset.sum_empty]
        have : wt S i * wt S j ≤ wt S j := by nlinarith
        linarith
      -- choose maximisers
      have hu : ∀ i' ∈ P, ∃ u : Fin S.length, (isB S u ∧ Ed S i' u) ∧
          pb S N i' ≤ wt S i' * wt S u - pb S N u := by
        intro i' hi'
        rw [hP, Finset.mem_filter] at hi'
        have hi'f := (mem_fib S).mp hi'.1
        have hpos := hi'.2
        rw [pb_BN S N hi'f.1 hi'f.2.1] at hpos ⊢
        obtain ⟨u, hu1, hu2⟩ := mx_pos hpos
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu1
        exact ⟨u, hu1, hu2⟩
      choose! u hu1 hu2 using hu
      obtain ⟨istar, hstarP, hmax⟩ := Finset.exists_max_image P (fun i' => wt S (u i')) hPne
      have hstar_fib : istar ∈ fib S j := (Finset.mem_filter.mp hstarP).1
      have hsf := (mem_fib S).mp hstar_fib
      set us := u istar with hus
      have husB := (hu1 istar hstarP).1
      have hjus : j < us := target_lt S hS hs hsf.1 hsf.2.1 husB (hu1 istar hstarP).2 hsf.2.2.1 hsf.2.2.2
      -- the sum over P
      have hterm : ∀ i' ∈ P, pb S N i' ≤ wt S i' * wt S us - (if i' = istar then pb S N us else 0) := by
        intro i' hi'
        have h1 := hu2 i' hi'
        have h2 := hmax i' hi'
        have h3 := mul_le_mul_of_nonneg_left h2 (wt_nonneg S i')
        split_ifs with h
        · subst h; simpa [hus] using h1
        · have := pb_nonneg S N (u i'); linarith
      have hsum1 : ∑ i' ∈ P, pb S N i' ≤
          ∑ i' ∈ P, wt S i' * wt S us - pb S N us := by
        calc ∑ i' ∈ P, pb S N i'
            ≤ ∑ i' ∈ P, (wt S i' * wt S us - (if i' = istar then pb S N us else 0)) :=
              Finset.sum_le_sum hterm
          _ = ∑ i' ∈ P, wt S i' * wt S us - pb S N us := by
              rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' P istar, if_pos hstarP]
      have hsum2 : ∑ i' ∈ P, wt S i' * wt S us ≤ wt S us := by
        have hcard : P.card ≤ ty (S.get istar) :=
          le_trans (Finset.card_filter_le _ _) (fib_card S hS hstar_fib)
        calc ∑ i' ∈ P, wt S i' * wt S us = ∑ _i' ∈ P, wt S istar * wt S us := by
              apply Finset.sum_congr rfl
              intro i' hi'
              rw [wt_eq_of_ty S (fib_same S (Finset.mem_filter.mp hi').1 hstar_fib).1]
          _ = P.card * (wt S istar * wt S us) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (ty (S.get istar) : ℝ) * (wt S istar * wt S us) := by
              apply mul_le_mul_of_nonneg_right _ (mul_nonneg (wt_nonneg S _) (wt_nonneg S _))
              exact_mod_cast hcard
          _ = wt S us := by rw [← mul_assoc, wt_mul_ty S hS istar, one_mul]
      -- the edge (i, us)
      have hxus : S.get us ≤ S.get j := get_anti S hs hjus.le
      have heus : Ed S i us := ⟨lt_trans he.1 hjus, by linarith [he.2]⟩
      have hMus : wt S i * wt S us - pb S N us ≤ M :=
        le_mx (f := fun j => wt S i * wt S j - pb S N j)
          (s := Finset.univ.filter (fun j => isB S j ∧ Ed S i j)) (j := us)
          (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨husB, heus⟩)
      have hwus : wt S us ≤ wt S j := wt_anti S hS hxus
      rw [hsumP]
      have : wt S i * wt S j ≤ M + (wt S j - (wt S us - pb S N us)) := by
        nlinarith [mul_le_mul_of_nonneg_left hwus (sub_nonneg.mpr hwi1)]
      linarith

open Classical in
/-- Edges whose first element is surplus. -/
lemma edge_surplus (S : List ℝ) (N : ℕ) (hN : 1 ≤ N) (hNS : ∀ a ∈ S, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2)
    (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) (hs : S.Pairwise (fun a b => b ≤ a))
    {i j : Fin S.length} (hi : ¬ isB S i) (he : Ed S i j) :
    wt S i * wt S j ≤ pc S N i + pc S N j := by
  have hpci : pc S N i = wt S i - ∑ i' ∈ fib S i, pb S N i' := by unfold pc; rw [if_neg hi]
  have hpci0 := pc_nonneg S N hS hs i
  have hpcj0 := pc_nonneg S N hS hs j
  have hwi1 := wt_le_one S hS i
  have hwj1 := wt_le_one S hS j
  have hwi0 := wt_nonneg S i
  have hwj0 := wt_nonneg S j
  rcases (fib S i).eq_empty_or_nonempty with hE | ⟨i0, h0⟩
  · rw [hpci, hE, Finset.sum_empty]; nlinarith
  by_cases hjE : ¬ isB S j ∧ fib S j = ∅
  · have : pc S N j = wt S j := by
      unfold pc; rw [if_neg hjE.1, hjE.2, Finset.sum_empty, sub_zero]
    rw [this]; nlinarith
  set t := ty (S.get i) with ht
  set a := wt S i * wt S j - pc S N j with ha
  by_cases ha0 : a ≤ 0
  · linarith
  push Not at ha0
  have hxi := (hS _ (List.get_mem S i)).1
  have hxj := (hS _ (List.get_mem S j)).1
  have htij := ty_lt_of_rel S hS he.2
  have hwj := wt_le_of_ty_ge S (t := t) htij
  have hwit : (t : ℝ) * wt S i = 1 := wt_mul_ty S hS i
  have ht1 : (1 : ℝ) ≤ t := by
    have := one_le_ty hxi (hS _ (List.get_mem S i)).2; exact_mod_cast this
  set c := ty (S.get i0) with hc
  have hc1 : (1 : ℝ) ≤ c := by
    have := one_le_ty (hS _ (List.get_mem S i0)).1 (hS _ (List.get_mem S i0)).2; exact_mod_cast this
  have hwc : (c : ℝ) * wt S i0 = 1 := wt_mul_ty S hS i0
  have hw0 := wt_nonneg S i0
  -- x_j < 1/(t+1)
  have hxj_lt : S.get j * ((t : ℝ) + 1) < 1 := by
    have h1 := lt_mul_ty_succ hxi
    have h2 := he.2
    nlinarith
  set B := max (wt S i0 / ((t : ℝ) + 1)) (wt S i0 * wt S i - a) with hB
  have hB0 : 0 ≤ B := le_trans (div_nonneg hw0 (by positivity)) (le_max_left _ _)
  have hterm : ∀ i' ∈ fib S i, pb S N i' ≤ B := by
    intro i' hi'
    have hi'f := (mem_fib S).mp hi'
    have hwi' : wt S i' = wt S i0 := wt_eq_of_ty S (fib_same S hi' h0).1
    rw [pb_BN S N hi'f.1 hi'f.2.1]
    apply mx_le hB0
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hiu : i < u := target_lt S hS hs hi'f.1 hi'f.2.1 hu.1 hu.2 hi'f.2.2.1 hi'f.2.2.2
    have hxu : S.get u ≤ S.get i := get_anti S hs hiu.le
    have htu : t ≤ ty (S.get u) := ty_anti (hS _ (List.get_mem S u)).1 hxu
    have hpbu := pb_nonneg S N u
    rw [hwi']
    rcases lt_or_eq_of_le htu with hlt | heq
    · have hwu := wt_le_of_ty_ge S (t := t) hlt
      have : wt S i0 * wt S u ≤ wt S i0 / ((t : ℝ) + 1) := by
        rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hwu hw0
      linarith [le_max_left (wt S i0 / ((t : ℝ) + 1)) (wt S i0 * wt S i - a)]
    · -- same type as i: the edge (u, j) is covered by `edge_basic`
      have hwu : wt S u = wt S i := wt_eq_of_ty S heq.symm
      have hxu_low := lt_mul_ty_succ (hS _ (List.get_mem S u)).1
      rw [← heq] at hxu_low
      have huj : u < j := lt_of_get_lt S hs (by nlinarith)
      have heuj : Ed S u j := ⟨huj, by
        rw [← heq]
        have : (t : ℝ) * S.get u ≤ (t : ℝ) * S.get i := mul_le_mul_of_nonneg_left hxu (by positivity)
        linarith [he.2]⟩
      have hcov := edge_basic S N hN hNS hS hs hu.1 heuj
      have hpcu : pc S N u = pb S N u := by unfold pc; rw [if_pos hu.1]
      rw [hpcu, hwu] at hcov
      rw [hwu]
      linarith [le_max_right (wt S i0 / ((t : ℝ) + 1)) (wt S i0 * wt S i - a)]
  have hsum : ∑ i' ∈ fib S i, pb S N i' ≤ c * B := by
    calc ∑ i' ∈ fib S i, pb S N i' ≤ ∑ _i' ∈ fib S i, B := Finset.sum_le_sum hterm
      _ = (fib S i).card * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ c * B := by
          apply mul_le_mul_of_nonneg_right _ hB0
          exact_mod_cast fib_card S hS h0
  have hgoal : a ≤ pc S N i := by
    rw [hpci]
    rcases max_cases (wt S i0 / ((t : ℝ) + 1)) (wt S i0 * wt S i - a) with ⟨hBe, -⟩ | ⟨hBe, -⟩
    · rw [← hB] at hBe
      rw [hBe] at hsum
      have e1 : (c : ℝ) * (wt S i0 / ((t : ℝ) + 1)) = 1 / ((t : ℝ) + 1) := by
        rw [← mul_div_assoc, hwc]
      rw [e1] at hsum
      -- a ≤ wt i * wt j ≤ wt i/(t+1) = wt i - 1/(t+1)
      have h1 : a ≤ wt S i * (1 / ((t : ℝ) + 1)) := by
        have := mul_le_mul_of_nonneg_left hwj hwi0; linarith
      have h2 : wt S i * (1 / ((t : ℝ) + 1)) = wt S i - 1 / ((t : ℝ) + 1) := by
        have ht0 : (t : ℝ) ≠ 0 := by positivity
        have hwi : wt S i = 1 / (t : ℝ) := by field_simp; linarith
        rw [hwi]; field_simp; ring
      linarith
    · rw [← hB] at hBe
      rw [hBe] at hsum
      have e1 : (c : ℝ) * (wt S i0 * wt S i - a) = wt S i - c * a := by
        rw [mul_sub, ← mul_assoc, hwc, one_mul]
      rw [e1] at hsum
      nlinarith
  linarith

lemma edge_cov (S : List ℝ) (N : ℕ) (hN : 1 ≤ N) (hNS : ∀ a ∈ S, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2)
    (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) (hs : S.Pairwise (fun a b => b ≤ a))
    {i j : Fin S.length} (he : Ed S i j) :
    wt S i * wt S j ≤ pc S N i + pc S N j := by
  by_cases hi : isB S i
  · exact edge_basic S N hN hNS hS hs hi he
  · exact edge_surplus S N hN hNS hS hs hi he

/-! ### Stage 2c: total weight of the cover -/

open Classical in
lemma fib_count (S : List ℝ) (N : ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) (i : Fin S.length) :
    ∑ f : Fin S.length, (if i ∈ fib S f then pb S N i else 0) =
      if isB S i ∧ ¬ lastB S i then pb S N i else 0 := by
  by_cases hBN : isB S i ∧ ¬ lastB S i
  · rw [if_pos hBN]
    rcases eq_or_lt_of_le (pb_nonneg S N i) with h0 | hpos
    · rw [← h0]; simp
    · have hpos' := hpos
      rw [pb_BN S N hBN.1 hBN.2] at hpos'
      obtain ⟨j, hj, -⟩ := mx_pos hpos'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨f, hf, hnb, -⟩ := target_after S hS hs hBN.1 hBN.2 hj.1 hj.2
      have hif : i ∈ fib S f := (mem_fib S).mpr ⟨hBN.1, hBN.2, hf, hnb⟩
      rw [Finset.sum_eq_single f]
      · rw [if_pos hif]
      · intro f' _ hf'
        rw [if_neg]
        intro hif'
        have h' := (mem_fib S).mp hif'
        exact hf' (firstSur_unique S h'.2.2.1 hf (nb_unique S h'.2.2.2 hnb))
      · intro h; exact absurd (Finset.mem_univ f) h
  · rw [if_neg hBN]
    apply Finset.sum_eq_zero
    intro f _
    rw [if_neg]
    intro hif
    have h' := (mem_fib S).mp hif
    exact hBN ⟨h'.1, h'.2.1⟩

open Classical in
lemma sum_fib (S : List ℝ) (N : ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) :
    ∑ f : Fin S.length, ∑ i ∈ fib S f, pb S N i =
      ∑ i : Fin S.length, (if isB S i ∧ ¬ lastB S i then pb S N i else 0) := by
  have h : ∀ f : Fin S.length, ∑ i ∈ fib S f, pb S N i =
      ∑ i : Fin S.length, (if i ∈ fib S f then pb S N i else 0) := by
    intro f
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_congr rfl (fun f _ => h f), Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => fib_count S N hS hs i)

open Classical in
lemma pc_total (S : List ℝ) (N : ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) :
    ∑ i, pc S N i = ∑ i, (if lastB S i then tok S N i else 0) +
      ∑ i, (if isB S i then 0 else wt S i) := by
  have hfibB : ∀ f, isB S f → fib S f = ∅ := by
    intro f hf
    ext i
    simp only [Finset.notMem_empty, iff_false]
    intro hi
    exact ((mem_fib S).mp hi).2.2.1.1 hf
  have e1 : ∀ i, pc S N i = (if lastB S i then tok S N i else 0) + (if isB S i then 0 else wt S i)
      + (if isB S i ∧ ¬ lastB S i then pb S N i else 0) - ∑ i' ∈ fib S i, pb S N i' := by
    intro i
    unfold pc
    by_cases hb : isB S i
    · rw [hfibB i hb, Finset.sum_empty, if_pos hb, if_pos hb]
      by_cases hl : lastB S i
      · rw [if_pos hl, if_neg (fun h => h.2 hl), pb_lastB S N hl]; ring
      · rw [if_neg hl, if_pos ⟨hb, hl⟩]; ring
    · have hl : ¬ lastB S i := fun h => hb h.1
      rw [if_neg hb, if_neg hb, if_neg hl, if_neg (fun h => hb h.1)]; ring
  rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, sum_fib S N hS hs]
  ring

open Classical in
lemma tok_total (S : List ℝ) (N : ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hS2 : ∀ a ∈ S, 0 < a ∧ a ≤ 1 / 2) :
    ∑ i, (if lastB S i then tok S N i else 0) ≤ ∑ j ∈ Finset.Icc 3 (N - 1), 1 / (j : ℝ) := by
  rw [← Finset.sum_filter]
  set T := Finset.univ.filter (fun i => lastB S i) with hTdef
  have hT : ∑ i ∈ T, tok S N i = ∑ i ∈ T.filter (fun i => ty (S.get i) + 2 ≤ N), tok S N i := by
    rw [Finset.sum_filter (fun i => ty (S.get i) + 2 ≤ N) (fun i => tok S N i)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : ty (S.get i) + 2 ≤ N
    · rw [if_pos h]
    · rw [if_neg h]; unfold tok; rw [if_neg h]
  rw [hT]
  set T' := T.filter (fun i => ty (S.get i) + 2 ≤ N) with hT'
  have hmaps : ∀ i ∈ T', ty (S.get i) ∈ Finset.Icc 2 (N - 2) := by
    intro i hi
    simp only [hT', hTdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact Finset.mem_Icc.mpr ⟨two_le_ty S hS2 i, by omega⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ k ∈ Finset.Icc 2 (N - 2),
      ∑ i ∈ T'.filter (fun i => ty (S.get i) = k), tok S N i ≤ 1 / ((k : ℝ) + 1) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    set Fk := T'.filter (fun i => ty (S.get i) = k) with hFk
    have hmemF : ∀ i ∈ Fk, lastB S i ∧ ty (S.get i) + 2 ≤ N ∧ ty (S.get i) = k := by
      intro i hi
      simp only [hFk, hT', hTdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨hi.1.1, hi.1.2, hi.2⟩
    have hterm : ∀ i ∈ Fk, tok S N i = 1 / (k : ℝ) / ((k : ℝ) + 1) := by
      intro i hi
      obtain ⟨-, h2, h3⟩ := hmemF i hi
      unfold tok
      rw [if_pos h2, wt_eq, h3, one_div]
    have hcard : Fk.card ≤ k := by
      rcases Fk.eq_empty_or_nonempty with hE | ⟨i0, hi0⟩
      · rw [hE]; simp
      · apply card_le_of_bin S hS (ffBinOf S i0) k
        intro i hi
        obtain ⟨hl, -, hik⟩ := hmemF i hi
        obtain ⟨hl0, -, hi0k⟩ := hmemF i0 hi0
        refine ⟨le_antisymm (hl0.2 i hl.1 (by rw [hik, hi0k]))
          (hl.2 i0 hl0.1 (by rw [hik, hi0k])), ?_⟩
        have := lt_mul_ty_succ (hS _ (List.get_mem S i)).1
        rw [hik] at this
        rw [div_lt_iff₀ (by positivity)]; linarith
    calc ∑ i ∈ Fk, tok S N i = ∑ _i ∈ Fk, 1 / (k : ℝ) / ((k : ℝ) + 1) := Finset.sum_congr rfl hterm
      _ = Fk.card * (1 / (k : ℝ) / ((k : ℝ) + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ k * (1 / (k : ℝ) / ((k : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard); positivity
      _ = 1 / ((k : ℝ) + 1) := by field_simp
  refine le_trans (Finset.sum_le_sum hfiber) (le_of_eq ?_)
  refine Finset.sum_nbij' (fun k => k + 1) (fun j => j - 1) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
  · intro k _; simp
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro k _; push_cast; ring

/-! ### Stage 2d: assembly -/

open Classical in
lemma basic_iff (L : List ℝ) (hS : ∀ a ∈ sortDesc L, 0 < a ∧ a ≤ 1)
    (i : Fin (sortDesc L).length) : i ∈ basic L ↔ isB (sortDesc L) i := by
  have hmem : ∀ x, x ∈ (ffPack (sortDesc L)).getD (ffBinOf (sortDesc L) i) [] ↔
      ∃ p : Fin (sortDesc L).length, ffBinOf (sortDesc L) p = ffBinOf (sortDesc L) i ∧
        (sortDesc L).get p = x := by
    intro x
    have h := bin_mem (sortDesc L) (sortDesc L).length le_rfl (ffBinOf (sortDesc L) i) x
    rw [List.take_length] at h
    rw [h]
    constructor
    · rintro ⟨p, -, h1, h2⟩; exact ⟨p, h1, h2⟩
    · rintro ⟨p, h1, h2⟩; exact ⟨p, p.isLt, h1, h2⟩
  have hiB : (sortDesc L).get i ∈ (ffPack (sortDesc L)).getD (ffBinOf (sortDesc L) i) [] :=
    (hmem _).mpr ⟨i, rfl, rfl⟩
  have hne : (ffPack (sortDesc L)).getD (ffBinOf (sortDesc L) i) [] ≠ [] := by
    intro h; rw [h] at hiB; simp at hiB
  have hpos : ∀ x ∈ (ffPack (sortDesc L)).getD (ffBinOf (sortDesc L) i) [], 0 ≤ x := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := (hmem x).mp hx
    exact (hS _ (List.get_mem _ p)).1.le
  obtain ⟨g, hg1, hg2⟩ := (hmem _).mp (binMax_mem hne hpos)
  have hmaxle : ∀ p : Fin (sortDesc L).length, ffBinOf (sortDesc L) p = ffBinOf (sortDesc L) i →
      (sortDesc L).get p ≤ (sortDesc L).get g := by
    intro p hp
    rw [hg2]; exact le_binMax ((hmem _).mpr ⟨p, hp, rfl⟩)
  unfold basic
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  unfold ffdBin ffdPack IsKBin
  constructor
  · rintro ⟨k, hk1, hk2⟩ p hp
    rw [← hg2] at hk2
    have e1 : ty ((sortDesc L).get i) = k := floor_eq_of_piece hk1
    have e2 : ty ((sortDesc L).get g) = k := floor_eq_of_piece hk2
    have := ty_anti (hS _ (List.get_mem _ p)).1 (hmaxle p hp)
    omega
  · intro h
    refine ⟨ty ((sortDesc L).get i), piece_of_floor (hS _ (List.get_mem _ i)).1
      (hS _ (List.get_mem _ i)).2, ?_⟩
    rw [← hg2]
    have h1 : ty ((sortDesc L).get i) ≤ ty ((sortDesc L).get g) := h g hg1
    have h2 : ty ((sortDesc L).get g) ≤ ty ((sortDesc L).get i) :=
      ty_anti (hS _ (List.get_mem _ i)).1 (hmaxle i rfl)
    have e : ty ((sortDesc L).get i) = ty ((sortDesc L).get g) := le_antisymm h1 h2
    rw [e]
    exact piece_of_floor (hS _ (List.get_mem _ g)).1 (hS _ (List.get_mem _ g)).2

/-- The piece type `k` is positive whenever `x` obeys relation `k` with something. -/
lemma rel_k_pos {k : ℕ} {x y : ℝ} (h : ObeysRelation k x y) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    obtain ⟨⟨h1, h2⟩, _⟩ := h
    simp at h1 h2
    linarith
  · exact hk

open Classical in
lemma w2_eq (x y : ℝ) :
    w2 x y = w1 x + w1 y -
      (if ObeysRelation ⌊1 / x⌋₊ x y then w1 y / (⌊1 / x⌋₊ : ℝ) else 0) := by
  unfold w2
  split_ifs with h
  · have hk : (1 : ℝ) ≤ (⌊1 / x⌋₊ : ℝ) := by exact_mod_cast rel_k_pos h
    field_simp
    ring
  · ring

open Classical in
/-- (ID): `w₁₂` equals the total `w₁` weight minus the relation-pair losses. -/
lemma w12_eq (S : List ℝ) (σ : Equiv.Perm (Fin S.length)) (hσ : σ * σ = 1) :
    w12 S σ = ∑ i, w1 (S.get i) -
      ∑ i ∈ Finset.univ.filter (fun i => i < σ i ∧
          ObeysRelation ⌊1 / S.get i⌋₊ (S.get i) (S.get (σ i))),
        w1 (S.get (σ i)) / (⌊1 / S.get i⌋₊ : ℝ) := by
  have hinv : ∀ i, σ (σ i) = i := fun i => by
    have := congrArg (fun τ : Equiv.Perm (Fin S.length) => τ i) hσ
    simpa [Equiv.Perm.mul_apply] using this
  unfold w12
  simp_rw [w2_eq]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_filter]
  -- the image of `i < σ i` under `σ` is `σ i < i`
  have hswap : ∑ i ∈ Finset.univ.filter (fun i => i < σ i), w1 (S.get (σ i)) =
      ∑ i ∈ Finset.univ.filter (fun i => σ i < i), w1 (S.get i) := by
    refine Finset.sum_nbij' (fun i => σ i) (fun i => σ i) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [hinv]; exact hi
    · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [hinv]; exact hi
    · intro i _; exact hinv i
    · intro i _; exact hinv i
    · intro i _; rfl
  rw [hswap]
  have hsplit : ∑ i, w1 (S.get i) =
      (∑ i ∈ Finset.univ.filter (fun i => σ i = i), w1 (S.get i)) +
      ((∑ i ∈ Finset.univ.filter (fun i => i < σ i), w1 (S.get i)) +
        ∑ i ∈ Finset.univ.filter (fun i => σ i < i), w1 (S.get i)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => σ i = i)]
    congr 1
    rw [← Finset.sum_union]
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro h
        rcases lt_trichotomy i (σ i) with h1 | h1 | h1
        · exact Or.inl h1
        · exact absurd h1.symm h
        · exact Or.inr h1
      · rintro (h | h)
        · exact fun he => by rw [he] at h; exact lt_irrefl _ h
        · exact fun he => by rw [he] at h; exact lt_irrefl _ h
    · rw [Finset.disjoint_filter]
      intro i _ h1 h2
      exact lt_asymm h1 h2
  rw [hsplit, Finset.filter_filter]
  ring


open Classical in
theorem main (N : ℕ) (hN : 4 ≤ N) (L : List ℝ)
    (hrange : ∀ a ∈ L, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2)
    (σ : Equiv.Perm (Fin (sortDesc L).length)) (hσ : σ ∈ pairings (sortDesc L).length) :
    w12 (sortDesc L) σ ≥
      ∑ i ∈ basic L, w1 ((sortDesc L).get i) - ∑ j ∈ Finset.Icc 3 (N - 1), 1 / (j : ℝ) := by
  have hperm : (sortDesc L).Perm L := List.mergeSort_perm _ _
  have hs : (sortDesc L).Pairwise (fun a b => b ≤ a) := by
    have := List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
      (fun a b c h1 h2 => by simp at h1 h2 ⊢; linarith)
      (fun a b => by simp; exact le_total b a) L
    exact this.imp (fun h => by simpa using h)
  have hNS : ∀ a ∈ sortDesc L, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2 :=
    fun a ha => hrange a (hperm.mem_iff.mp ha)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hS2 : ∀ a ∈ sortDesc L, 0 < a ∧ a ≤ 1 / 2 :=
    fun a ha => ⟨lt_trans (by positivity) (hNS a ha).1, (hNS a ha).2⟩
  have hS : ∀ a ∈ sortDesc L, 0 < a ∧ a ≤ 1 :=
    fun a ha => ⟨(hS2 a ha).1, by linarith [(hS2 a ha).2]⟩
  have hσ' : σ * σ = 1 := (Finset.mem_filter.mp hσ).2
  have hinv : ∀ i, σ (σ i) = i := fun i => by
    have := congrArg (fun τ : Equiv.Perm (Fin (sortDesc L).length) => τ i) hσ'
    simpa [Equiv.Perm.mul_apply] using this
  rw [w12_eq (sortDesc L) σ hσ']
  set R := Finset.univ.filter (fun i => i < σ i ∧
      ObeysRelation ⌊1 / (sortDesc L).get i⌋₊ ((sortDesc L).get i) ((sortDesc L).get (σ i))) with hR
  have hdisj : Disjoint R (R.image σ) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨b, hbR, rfl⟩ := Finset.mem_image.mp hb
    rw [hR, Finset.mem_filter] at ha hbR
    have h1 := hbR.2.1
    have h2 := ha.2.1
    rw [hinv] at h2
    exact absurd (lt_trans h1 h2) (lt_irrefl _)
  have hloss : ∑ i ∈ R, w1 ((sortDesc L).get (σ i)) / (⌊1 / (sortDesc L).get i⌋₊ : ℝ) ≤
      ∑ i, pc (sortDesc L) N i := by
    have h1 : ∀ i ∈ R, w1 ((sortDesc L).get (σ i)) / (⌊1 / (sortDesc L).get i⌋₊ : ℝ) ≤
        pc (sortDesc L) N i + pc (sortDesc L) N (σ i) := by
      intro i hi
      rw [hR, Finset.mem_filter] at hi
      have he : Ed (sortDesc L) i (σ i) := ⟨hi.2.1, hi.2.2.2⟩
      have hc := edge_cov (sortDesc L) N (by omega) hNS hS hs he
      have e : w1 ((sortDesc L).get (σ i)) / (⌊1 / (sortDesc L).get i⌋₊ : ℝ) =
          wt (sortDesc L) i * wt (sortDesc L) (σ i) := by
        unfold wt w1; ring
      rw [e]; exact hc
    calc ∑ i ∈ R, w1 ((sortDesc L).get (σ i)) / (⌊1 / (sortDesc L).get i⌋₊ : ℝ)
        ≤ ∑ i ∈ R, (pc (sortDesc L) N i + pc (sortDesc L) N (σ i)) := Finset.sum_le_sum h1
      _ = ∑ i ∈ R, pc (sortDesc L) N i + ∑ i ∈ R.image σ, pc (sortDesc L) N i := by
          rw [Finset.sum_add_distrib, Finset.sum_image (fun a _ b _ h => σ.injective h)]
      _ = ∑ i ∈ R ∪ R.image σ, pc (sortDesc L) N i := by rw [Finset.sum_union hdisj]
      _ ≤ ∑ i, pc (sortDesc L) N i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => pc_nonneg (sortDesc L) N hS hs i)
  have htot := pc_total (sortDesc L) N hS hs
  have htok := tok_total (sortDesc L) N hS hS2
  have hbasic : basic L = Finset.univ.filter (fun i => isB (sortDesc L) i) := by
    ext i
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    exact basic_iff L hS i
  have hsplit : ∑ i, w1 ((sortDesc L).get i) =
      ∑ i ∈ basic L, w1 ((sortDesc L).get i) +
        ∑ i, (if isB (sortDesc L) i then 0 else wt (sortDesc L) i) := by
    rw [hbasic, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold wt
    split_ifs <;> ring
  linarith

end C4Aux_998ce8a1


namespace WFFD_9ce81529
open BinPacking.SmallItems

lemma harmonic_bound (N : ℕ) (hN : 4 ≤ N) :
    ∑ j ∈ Finset.Icc 2 (N - 1), ((j : ℝ) - 1) / (j : ℝ) +
      ∑ j ∈ Finset.Icc 3 (N - 1), 1 / (j : ℝ) ≤ (N : ℝ) - 2 := by
  have hins : Finset.Icc 2 (N - 1) = insert 2 (Finset.Icc 3 (N - 1)) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hins, Finset.sum_insert (by simp), add_assoc, ← Finset.sum_add_distrib]
  have h1 : ∀ j ∈ Finset.Icc 3 (N - 1), ((j : ℝ) - 1) / (j : ℝ) + 1 / (j : ℝ) = 1 := by
    intro j hj
    have hj3 : 3 ≤ j := (Finset.mem_Icc.mp hj).1
    have : (j : ℝ) ≠ 0 := by positivity
    field_simp; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  have e : ((N - 1 + 1 - 3 : ℕ) : ℝ) = (N : ℝ) - 3 := by
    rw [show N - 1 + 1 - 3 = N - 3 by omega, Nat.cast_sub (by omega : 3 ≤ N)]; norm_num
  have e2 : (((2 : ℕ) : ℝ) - 1) / ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
  rw [e, e2]
  linarith

theorem W_ge (N : ℕ) (hN : 4 ≤ N) (L : List ℝ) (hL : IsList L)
    (hrange : ∀ a ∈ L, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2) :
    W L ≥ (FFD L : ℝ) - (N : ℝ) + 2 := by
  have hA := ffb_basic_weight_ge N hN L hL hrange
  have hH := harmonic_bound N hN
  unfold W
  rw [ge_iff_le]
  apply Finset.le_inf'
  intro σ hσ
  have hB := C4Aux_998ce8a1.main N hN L hrange σ hσ
  linarith

end WFFD_9ce81529

namespace P6c9b

open BinPacking.SmallItems

theorem w1_eq_of (k : ℕ) (hk : 0 < k) (x : ℝ) (h1 : 1 / ((k : ℝ) + 1) < x) (h2 : x ≤ 1 / (k : ℝ)) :
    w1 x = 1 / (k : ℝ) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : 0 < x := lt_trans (by positivity) h1
  have hfl : ⌊1 / x⌋₊ = k := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · rw [le_div_iff₀ hx]
      rw [le_div_iff₀ hk'] at h2
      linarith
    · rw [div_lt_iff₀ hx]
      rw [div_lt_iff₀ (by linarith)] at h1
      linarith
  unfold w1
  rw [hfl, one_div]

theorem w1_nonneg (y : ℝ) : 0 ≤ w1 y := by
  unfold w1; positivity

theorem w2_cases (k : ℕ) (hk : 0 < k) (x y : ℝ) (h1 : 1 / ((k : ℝ) + 1) < x)
    (h2 : x ≤ 1 / (k : ℝ)) :
    ((k : ℝ) * x + y ≤ 1 ∧ w2 x y = 1 / (k : ℝ) + ((k : ℝ) - 1) / (k : ℝ) * w1 y) ∨
    (1 < (k : ℝ) * x + y ∧ w2 x y = 1 / (k : ℝ) + w1 y) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : 0 < x := lt_trans (by positivity) h1
  have hfl : ⌊1 / x⌋₊ = k := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · rw [le_div_iff₀ hx]
      rw [le_div_iff₀ hk'] at h2
      linarith
    · rw [div_lt_iff₀ hx]
      rw [div_lt_iff₀ (by linarith)] at h1
      linarith
  have hw := w1_eq_of k hk x h1 h2
  by_cases hr : (k : ℝ) * x + y ≤ 1
  · left
    refine ⟨hr, ?_⟩
    unfold w2
    rw [if_pos ⟨by rw [hfl]; exact ⟨h1, h2⟩, by rw [hfl]; exact hr⟩, hfl, hw]
  · right
    refine ⟨lt_of_not_ge hr, ?_⟩
    unfold w2
    rw [if_neg (by rw [hfl]; exact fun h => hr h.2), hw]

theorem piece_cases (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 2) :
    (1 / 3 < x ∧ x ≤ 1 / 2 ∧ w1 x = 1 / 2) ∨ (1 / 4 < x ∧ x ≤ 1 / 3 ∧ w1 x = 1 / 3) ∨
    (1 / 5 < x ∧ x ≤ 1 / 4 ∧ w1 x = 1 / 4) ∨ (1 / 6 < x ∧ x ≤ 1 / 5 ∧ w1 x = 1 / 5) ∨
    (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := by
  rcases lt_or_ge (1 / 3) x with h3 | h3
  · exact Or.inl ⟨h3, h2, by
      have := w1_eq_of 2 (by norm_num) x (by norm_num; linarith) (by norm_num; linarith)
      simpa using this⟩
  rcases lt_or_ge (1 / 4) x with h4 | h4
  · exact Or.inr <| Or.inl ⟨h4, h3, by
      have := w1_eq_of 3 (by norm_num) x (by norm_num; linarith) (by norm_num; linarith)
      simpa using this⟩
  rcases lt_or_ge (1 / 5) x with h5 | h5
  · exact Or.inr <| Or.inr <| Or.inl ⟨h5, h4, by
      have := w1_eq_of 4 (by norm_num) x (by norm_num; linarith) (by norm_num; linarith)
      simpa using this⟩
  rcases lt_or_ge (1 / 6) x with h6 | h6
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨h6, h5, by
      have := w1_eq_of 5 (by norm_num) x (by norm_num; linarith) (by norm_num; linarith)
      simpa using this⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨h1, h6, by
      have := w1_eq_of 6 (by norm_num) x (by norm_num; linarith) (by norm_num; linarith)
      simpa using this⟩

theorem pc2 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 2) :
    (1 / 3 < x ∧ x ≤ 1 / 2 ∧ w1 x = 1 / 2) ∨ (1 / 4 < x ∧ x ≤ 1 / 3 ∧ w1 x = 1 / 3) ∨
    (1 / 5 < x ∧ x ≤ 1 / 4 ∧ w1 x = 1 / 4) ∨ (1 / 6 < x ∧ x ≤ 1 / 5 ∧ w1 x = 1 / 5) ∨
    (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := piece_cases x h1 h2

theorem pc3 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 3) :
    (1 / 4 < x ∧ x ≤ 1 / 3 ∧ w1 x = 1 / 3) ∨
    (1 / 5 < x ∧ x ≤ 1 / 4 ∧ w1 x = 1 / 4) ∨ (1 / 6 < x ∧ x ≤ 1 / 5 ∧ w1 x = 1 / 5) ∨
    (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := by
  rcases piece_cases x h1 (by linarith) with h | h
  · exfalso; linarith [h.1]
  · exact h

theorem pc4 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 4) :
    (1 / 5 < x ∧ x ≤ 1 / 4 ∧ w1 x = 1 / 4) ∨ (1 / 6 < x ∧ x ≤ 1 / 5 ∧ w1 x = 1 / 5) ∨
    (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := by
  rcases pc3 x h1 (by linarith) with h | h
  · exfalso; linarith [h.1]
  · exact h

theorem pc5 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 5) :
    (1 / 6 < x ∧ x ≤ 1 / 5 ∧ w1 x = 1 / 5) ∨ (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := by
  rcases pc4 x h1 (by linarith) with h | h
  · exfalso; linarith [h.1]
  · exact h

theorem pc6 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 6) :
    (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := by
  rcases pc5 x h1 (by linarith) with h | h
  · exfalso; linarith [h.1]
  · exact h

theorem w1le2 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 2) : w1 x ≤ 1 / 2 := by
  rcases pc2 x h1 h2 with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> norm_num

theorem w1le3 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 3) : w1 x ≤ 1 / 3 := by
  rcases pc3 x h1 h2 with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> norm_num

theorem w1le4 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 4) : w1 x ≤ 1 / 4 := by
  rcases pc4 x h1 h2 with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> norm_num

theorem w1le5 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 5) : w1 x ≤ 1 / 5 := by
  rcases pc5 x h1 h2 with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> norm_num

theorem w1le6 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 6) : w1 x ≤ 1 / 6 := by
  rcases pc6 x h1 h2 with ⟨-, -, h⟩ <;> rw [h] <;> norm_num

theorem w2c2 (x y : ℝ) (h1 : 1 / 3 < x) (h2 : x ≤ 1 / 2) :
    (2 * x + y ≤ 1 ∧ w2 x y = 1 / 2 + 1 / 2 * w1 y) ∨ (1 < 2 * x + y ∧ w2 x y = 1 / 2 + w1 y) := by
  have := w2_cases 2 (by norm_num) x y (by norm_num; linarith) (by norm_num; linarith)
  norm_num at this ⊢; exact this

theorem w2c3 (x y : ℝ) (h1 : 1 / 4 < x) (h2 : x ≤ 1 / 3) :
    (3 * x + y ≤ 1 ∧ w2 x y = 1 / 3 + 2 / 3 * w1 y) ∨ (1 < 3 * x + y ∧ w2 x y = 1 / 3 + w1 y) := by
  have := w2_cases 3 (by norm_num) x y (by norm_num; linarith) (by norm_num; linarith)
  norm_num at this ⊢; exact this

theorem w2c4 (x y : ℝ) (h1 : 1 / 5 < x) (h2 : x ≤ 1 / 4) :
    (4 * x + y ≤ 1 ∧ w2 x y = 1 / 4 + 3 / 4 * w1 y) ∨ (1 < 4 * x + y ∧ w2 x y = 1 / 4 + w1 y) := by
  have := w2_cases 4 (by norm_num) x y (by norm_num; linarith) (by norm_num; linarith)
  norm_num at this ⊢; exact this

theorem w2c5 (x y : ℝ) (h1 : 1 / 6 < x) (h2 : x ≤ 1 / 5) :
    (5 * x + y ≤ 1 ∧ w2 x y = 1 / 5 + 4 / 5 * w1 y) ∨ (1 < 5 * x + y ∧ w2 x y = 1 / 5 + w1 y) := by
  have := w2_cases 5 (by norm_num) x y (by norm_num; linarith) (by norm_num; linarith)
  norm_num at this ⊢; exact this

theorem w2c6 (x y : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 6) :
    (6 * x + y ≤ 1 ∧ w2 x y = 1 / 6 + 5 / 6 * w1 y) ∨ (1 < 6 * x + y ∧ w2 x y = 1 / 6 + w1 y) := by
  have := w2_cases 6 (by norm_num) x y (by norm_num; linarith) (by norm_num; linarith)
  norm_num at this ⊢; exact this

/-! ### w12 for the identity, one swap, two disjoint swaps -/

theorem one_mem_pairings (n : ℕ) : (1 : Equiv.Perm (Fin n)) ∈ pairings n := by
  simp [pairings]

theorem swap_mem_pairings {n : ℕ} (i j : Fin n) : Equiv.swap i j ∈ pairings n := by
  simp [pairings, Equiv.swap_mul_self]

theorem swap_comm_of_ne {n : ℕ} (i j k l : Fin n) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) : Equiv.swap i j * Equiv.swap k l = Equiv.swap k l * Equiv.swap i j := by
  apply Equiv.ext; intro x
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  by_cases h1 : x = i
  · subst h1
    rw [Equiv.swap_apply_of_ne_of_ne hik hil, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hjk hjl]
  by_cases h2 : x = j
  · subst h2
    rw [Equiv.swap_apply_of_ne_of_ne hjk hjl, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hik hil]
  by_cases h3 : x = k
  · subst h3
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk),
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hil) (Ne.symm hjl), Equiv.swap_apply_left]
  by_cases h4 : x = l
  · subst h4
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm hil) (Ne.symm hjl),
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk), Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_of_ne_of_ne h1 h2,
    Equiv.swap_apply_of_ne_of_ne h3 h4]

theorem swap2_mem_pairings {n : ℕ} (i j k l : Fin n) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) : Equiv.swap i j * Equiv.swap k l ∈ pairings n := by
  simp only [pairings, Finset.mem_filter, Finset.mem_univ, true_and]
  have hc := swap_comm_of_ne i j k l hik hil hjk hjl
  calc Equiv.swap i j * Equiv.swap k l * (Equiv.swap i j * Equiv.swap k l)
      = Equiv.swap i j * (Equiv.swap k l * Equiv.swap i j) * Equiv.swap k l := by
        simp only [mul_assoc]
    _ = 1 := by
        rw [← hc]
        simp only [Equiv.swap_mul_self_mul, Equiv.swap_mul_self]

theorem sum_w1 (S : List ℝ) : ∑ t : Fin S.length, w1 (S.get t) = (S.map w1).sum := by
  simp

theorem w12_one (S : List ℝ) : w12 S 1 = ∑ i : Fin S.length, w1 (S.get i) := by
  unfold w12
  simp

theorem w12_swap (S : List ℝ) (i j : Fin S.length) (hij : i < j) :
    w12 S (Equiv.swap i j) = (∑ t : Fin S.length, w1 (S.get t)) - w1 (S.get i) - w1 (S.get j)
      + w2 (S.get i) (S.get j) := by
  unfold w12
  have hne : i ≠ j := ne_of_lt hij
  have e1 : (Finset.univ.filter (fun t => Equiv.swap i j t = t)) = (Finset.univ.erase i).erase j := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all [eq_comm]
  have e2 : (Finset.univ.filter (fun t => t < Equiv.swap i j t)) = {i} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all [lt_asymm]
  rw [e1, e2, Finset.sum_singleton, Equiv.swap_apply_left]
  rw [Finset.sum_erase_eq_sub (by simp [Ne.symm hne]), Finset.sum_erase_eq_sub (by simp)]

theorem w12_swap2 (S : List ℝ) (i j k l : Fin S.length) (hij : i < j) (hkl : k < l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    w12 S (Equiv.swap i j * Equiv.swap k l) = (∑ t : Fin S.length, w1 (S.get t))
      - w1 (S.get i) - w1 (S.get j) - w1 (S.get k) - w1 (S.get l)
      + w2 (S.get i) (S.get j) + w2 (S.get k) (S.get l) := by
  unfold w12
  have hne : i ≠ j := ne_of_lt hij
  have hne' : k ≠ l := ne_of_lt hkl
  have vi : (Equiv.swap i j * Equiv.swap k l) i = j := by
    simp [Equiv.swap_apply_of_ne_of_ne hik hil]
  have vj : (Equiv.swap i j * Equiv.swap k l) j = i := by
    simp [Equiv.swap_apply_of_ne_of_ne hjk hjl]
  have vk : (Equiv.swap i j * Equiv.swap k l) k = l := by
    simp [Equiv.swap_apply_of_ne_of_ne (Ne.symm hil) (Ne.symm hjl)]
  have vl : (Equiv.swap i j * Equiv.swap k l) l = k := by
    simp [Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)]
  have vo : ∀ t, t ≠ i → t ≠ j → t ≠ k → t ≠ l → (Equiv.swap i j * Equiv.swap k l) t = t := by
    intro t h1 h2 h3 h4
    simp [Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have e1 : (Finset.univ.filter (fun t => (Equiv.swap i j * Equiv.swap k l) t = t))
      = (((Finset.univ.erase i).erase j).erase k).erase l := by
    ext t
    rw [Finset.mem_filter]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, true_and, ne_eq]
    by_cases h1 : t = i
    · rw [h1, vi]; simp [Ne.symm hne]
    by_cases h2 : t = j
    · rw [h2, vj]; simp [hne]
    by_cases h3 : t = k
    · rw [h3, vk]; simp [Ne.symm hne']
    by_cases h4 : t = l
    · rw [h4, vl]; simp [hne']
    rw [vo t h1 h2 h3 h4]; simp [h1, h2, h3, h4]
  have e2 : (Finset.univ.filter (fun t => t < (Equiv.swap i j * Equiv.swap k l) t)) = {i, k} := by
    ext t
    rw [Finset.mem_filter]
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, true_and]
    by_cases h1 : t = i
    · rw [h1, vi]; simp [hij]
    by_cases h2 : t = j
    · rw [h2, vj]; simp [not_lt.mpr hij.le, hne, Ne.symm hne, hjk]
    by_cases h3 : t = k
    · rw [h3, vk]; simp [hkl]
    by_cases h4 : t = l
    · rw [h4, vl]; simp [not_lt.mpr hkl.le, Ne.symm hil, Ne.symm hne']
    rw [vo t h1 h2 h3 h4]; simp [h1, h3]
  rw [e1, e2, Finset.sum_pair hik, vi, vk]
  rw [Finset.sum_erase_eq_sub (by simp [Ne.symm hil, Ne.symm hjl, Ne.symm hne']),
    Finset.sum_erase_eq_sub (by simp [Ne.symm hik, Ne.symm hjk]),
    Finset.sum_erase_eq_sub (by simp [Ne.symm hne]), Finset.sum_erase_eq_sub (by simp)]
  ring

set_option maxHeartbeats 4000000 in
theorem core1 (x0 : ℝ) (l0 : 1 / 7 < x0) (u0 : x0 ≤ 1 / 2)  (hs : x0 ≤ 1) :
    ∃ σ ∈ pairings [x0].length, w12 [x0] σ ≤ 71 / 60 := by
  exact ⟨1, one_mem_pairings _, by
    rw [w12_one, sum_w1]; show (w1 x0 + 0) ≤ 71 / 60
    have c0 := w1le2 x0 l0 (by linarith only [u0])
    linarith only [c0]⟩

set_option maxHeartbeats 4000000 in
theorem core2 (x0 x1 : ℝ) (l0 : 1 / 7 < x0) (l1 : 1 / 7 < x1) (u0 : x0 ≤ 1 / 2) (o0 : x1 ≤ x0) (hs : x0 + x1 ≤ 1) :
    ∃ σ ∈ pairings [x0, x1].length, w12 [x0, x1] σ ≤ 71 / 60 := by
  exact ⟨1, one_mem_pairings _, by
    rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + 0)) ≤ 71 / 60
    have c0 := w1le2 x0 l0 (by linarith only [u0])
    have c1 := w1le2 x1 l1 (by linarith only [u0, o0])
    linarith only [c0, c1]⟩

set_option maxHeartbeats 4000000 in
theorem core3 (x0 x1 x2 : ℝ) (l0 : 1 / 7 < x0) (l1 : 1 / 7 < x1) (l2 : 1 / 7 < x2) (u0 : x0 ≤ 1 / 2) (o0 : x1 ≤ x0) (o1 : x2 ≤ x1) (hs : x0 + x1 + x2 ≤ 1) :
    ∃ σ ∈ pairings [x0, x1, x2].length, w12 [x0, x1, x2] σ ≤ 71 / 60 := by
  rcases pc2 x0 l0 u0 with ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩
  · rcases pc2 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc2 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a2, o0, o1, hs]
      · refine ⟨Equiv.swap ⟨1, (show 1 < 3 by decide)⟩ ⟨2, (show 2 < 3 by decide)⟩, swap_mem_pairings _ _, ?_⟩
        rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
        show (w1 x0 + (w1 x1 + (w1 x2 + 0))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
        rcases w2c2 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
        · norm_num [e1, q0, q1, q2]
        · exfalso; linarith only [o0, hs, r1]
      · refine ⟨Equiv.swap ⟨1, (show 1 < 3 by decide)⟩ ⟨2, (show 2 < 3 by decide)⟩, swap_mem_pairings _ _, ?_⟩
        rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
        show (w1 x0 + (w1 x1 + (w1 x2 + 0))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
        rcases w2c2 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
        · norm_num [e1, q0, q1, q2]
        · exfalso; linarith only [o0, hs, r1]
      · refine ⟨Equiv.swap ⟨1, (show 1 < 3 by decide)⟩ ⟨2, (show 2 < 3 by decide)⟩, swap_mem_pairings _ _, ?_⟩
        rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
        show (w1 x0 + (w1 x1 + (w1 x2 + 0))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
        rcases w2c2 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
        · norm_num [e1, q0, q1, q2]
        · exfalso; linarith only [o0, hs, r1]
      · exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60; norm_num [q0, q1, q2]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
        have c2 := w1le3 x2 l2 (by linarith only [b1, o1])
        linarith only [q0, q1, c2]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
        have c2 := w1le4 x2 l2 (by linarith only [b1, o1])
        linarith only [q0, q1, c2]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
        have c2 := w1le5 x2 l2 (by linarith only [b1, o1])
        linarith only [q0, q1, c2]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        linarith only [q0, q1, c2]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
      have c1 := w1le3 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le3 x2 l2 (by linarith only [b0, o0, o1])
      linarith only [q0, c1, c2]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
      have c1 := w1le4 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le4 x2 l2 (by linarith only [b0, o0, o1])
      linarith only [q0, c1, c2]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
      have c1 := w1le5 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le5 x2 l2 (by linarith only [b0, o0, o1])
      linarith only [q0, c1, c2]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
      have c1 := w1le6 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le6 x2 l2 (by linarith only [b0, o0, o1])
      linarith only [q0, c1, c2]⟩

set_option maxHeartbeats 4000000 in
theorem core4 (x0 x1 x2 x3 : ℝ) (l0 : 1 / 7 < x0) (l1 : 1 / 7 < x1) (l2 : 1 / 7 < x2) (l3 : 1 / 7 < x3) (u0 : x0 ≤ 1 / 2) (o0 : x1 ≤ x0) (o1 : x2 ≤ x1) (o2 : x3 ≤ x2) (hs : x0 + x1 + x2 + x3 ≤ 1) :
    ∃ σ ∈ pairings [x0, x1, x2, x3].length, w12 [x0, x1, x2, x3] σ ≤ 71 / 60 := by
  rcases pc2 x0 l0 u0 with ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩
  · rcases pc2 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc2 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a2, l3, o0, o1, hs]
      · exfalso; linarith only [a1, a2, l3, o0, hs]
      · exfalso; linarith only [a1, a2, l3, o0, hs]
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a1, a3, o0, o2, hs]
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨2, (show 2 < 4 by decide)⟩ * Equiv.swap ⟨1, (show 1 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap2_mem_pairings _ _ _ _ (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), ?_⟩
          rw [w12_swap2 _ _ _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 2 by decide)) (Fin.mk_lt_mk.mpr (show 1 < 3 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x2 - w1 x1 - w1 x3 + w2 x0 x2 + w2 x1 x3 ≤ 71 / 60
          rcases w2c2 x0 x2 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · rcases w2c2 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · norm_num [e1, e2, q0, q1, q2, q3]
            · exfalso; linarith only [o0, o2, r1, r2]
          · rcases w2c2 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · exfalso; linarith only [a1, a3, o2, hs, r1]
            · exfalso; linarith only [a3, o2, hs, r1, r2]
      · rcases pc6 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨2, (show 2 < 4 by decide)⟩ * Equiv.swap ⟨1, (show 1 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap2_mem_pairings _ _ _ _ (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), ?_⟩
          rw [w12_swap2 _ _ _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 2 by decide)) (Fin.mk_lt_mk.mpr (show 1 < 3 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x2 - w1 x1 - w1 x3 + w2 x0 x2 + w2 x1 x3 ≤ 71 / 60
          rcases w2c2 x0 x2 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · rcases w2c2 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · norm_num [e1, e2, q0, q1, q2, q3]
            · exfalso; linarith only [o0, o2, r1, r2]
          · rcases w2c2 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · exfalso; linarith only [a1, a3, o2, hs, r1]
            · exfalso; linarith only [a3, o2, hs, r1, r2]
    · rcases pc3 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc3 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a3, o0, o1, o2, hs]
        · exfalso; linarith only [a0, a2, a3, o1, hs]
        · exfalso; linarith only [a0, a2, a3, o1, hs]
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨1, (show 1 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
          rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a2, a3, o1, hs, r1]
      · rcases pc4 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨1, (show 1 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
          rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a3, o1, o2, hs, r1]
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨2, (show 2 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 2 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x2 + w2 x0 x2 ≤ 71 / 60
          rcases w2c2 x0 x2 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a1, a3, o2, hs, r1]
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x3 + w2 x0 x3 ≤ 71 / 60
          rcases w2c2 x0 x3 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a1, a2, a3, hs, r1]
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨2, (show 2 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 2 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x2 + w2 x0 x2 ≤ 71 / 60
          rcases w2c2 x0 x2 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a1, a3, o2, hs, r1]
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨2, (show 2 < 4 by decide)⟩ * Equiv.swap ⟨1, (show 1 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap2_mem_pairings _ _ _ _ (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), ?_⟩
          rw [w12_swap2 _ _ _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 2 by decide)) (Fin.mk_lt_mk.mpr (show 1 < 3 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x2 - w1 x1 - w1 x3 + w2 x0 x2 + w2 x1 x3 ≤ 71 / 60
          rcases w2c2 x0 x2 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · rcases w2c3 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · norm_num [e1, e2, q0, q1, q2, q3]
            · norm_num [e1, e2, q0, q1, q2, q3]
          · rcases w2c3 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · norm_num [e1, e2, q0, q1, q2, q3]
            · exfalso; linarith only [a3, o2, hs, r1, r2]
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
    · rcases pc4 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc4 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨1, (show 1 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
          rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a3, o1, o2, hs, r1]
        · by_cases hsp : 2 * x0 + x3 ≤ 1
          · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 3 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x3 + w2 x0 x3 ≤ 71 / 60
            rcases w2c2 x0 x3 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3]
            · exfalso; linarith only [r1, hsp]
          · refine ⟨Equiv.swap ⟨2, (show 2 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 2 < 3 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x2 - w1 x3 + w2 x2 x3 ≤ 71 / 60
            rcases w2c4 x2 x3 a2 b2 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3]
            · exfalso; linarith only [o1, hs, r1, hsp]
        · exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60; norm_num [q0, q1, q2, q3]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le5 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
        have c2 := w1le5 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le5 x3 l3 (by linarith only [b1, o1, o2])
        linarith only [q0, q1, c2, c3]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        linarith only [q0, q1, c2, c3]⟩
  · rcases pc3 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc3 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc3 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a3, o0, o1, o2, hs]
        · refine ⟨Equiv.swap ⟨2, (show 2 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 2 < 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x2 - w1 x3 + w2 x2 x3 ≤ 71 / 60
          rcases w2c3 x2 x3 a2 b2 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [o0, o1, hs, r1]
        · refine ⟨Equiv.swap ⟨2, (show 2 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 2 < 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x2 - w1 x3 + w2 x2 x3 ≤ 71 / 60
          rcases w2c3 x2 x3 a2 b2 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [o0, o1, hs, r1]
        · exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60; norm_num [q0, q1, q2, q3]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le4 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le5 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
        have c2 := w1le4 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le4 x3 l3 (by linarith only [b1, o1, o2])
        linarith only [q0, q1, c2, c3]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
        have c2 := w1le5 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le5 x3 l3 (by linarith only [b1, o1, o2])
        linarith only [q0, q1, c2, c3]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        linarith only [q0, q1, c2, c3]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
      have c1 := w1le4 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le4 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le4 x3 l3 (by linarith only [b0, o0, o1, o2])
      linarith only [q0, c1, c2, c3]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
      have c1 := w1le5 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le5 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le5 x3 l3 (by linarith only [b0, o0, o1, o2])
      linarith only [q0, c1, c2, c3]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
      have c1 := w1le6 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le6 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le6 x3 l3 (by linarith only [b0, o0, o1, o2])
      linarith only [q0, c1, c2, c3]⟩

set_option maxHeartbeats 4000000 in
theorem core5 (x0 x1 x2 x3 x4 : ℝ) (l0 : 1 / 7 < x0) (l1 : 1 / 7 < x1) (l2 : 1 / 7 < x2) (l3 : 1 / 7 < x3) (l4 : 1 / 7 < x4) (u0 : x0 ≤ 1 / 2) (o0 : x1 ≤ x0) (o1 : x2 ≤ x1) (o2 : x3 ≤ x2) (o3 : x4 ≤ x3) (hs : x0 + x1 + x2 + x3 + x4 ≤ 1) :
    ∃ σ ∈ pairings [x0, x1, x2, x3, x4].length, w12 [x0, x1, x2, x3, x4] σ ≤ 71 / 60 := by
  rcases pc2 x0 l0 u0 with ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩
  · rcases pc2 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · exfalso; linarith only [a1, l4, o0, o2, o3, hs]
    · exfalso; linarith only [a0, a1, l4, o2, o3, hs]
    · rcases pc4 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a0, a2, l4, o1, o3, hs]
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a0, a1, a3, l4, o2, hs]
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o1, o2, o3, hs, r1]
      · rcases pc6 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o1, o2, o3, hs, r1]
    · rcases pc5 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc5 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · exfalso; linarith only [a0, a4, o1, o2, o3, hs]
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o1, o2, o3, hs, r1]
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o1, o2, o3, hs, r1]
      · rcases pc6 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o1, o2, o3, hs, r1]
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        linarith only [q0, q1, c2, c3, c4]⟩
  · rcases pc3 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc3 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a2, l4, o0, o1, o3, hs]
      · rcases pc4 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a1, a3, l4, o0, o2, hs]
        · exfalso; linarith only [a1, a2, a3, l4, o0, hs]
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨1, (show 1 < 5 by decide)⟩ ⟨2, (show 2 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
            rcases w2c3 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o0, o2, o3, hs, r1]
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc5 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · exfalso; linarith only [a1, a4, o0, o2, o3, hs]
          · refine ⟨Equiv.swap ⟨1, (show 1 < 5 by decide)⟩ ⟨2, (show 2 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
            rcases w2c3 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o0, o2, o3, hs, r1]
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨1, (show 1 < 5 by decide)⟩ ⟨2, (show 2 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
            rcases w2c3 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o0, o2, o3, hs, r1]
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          linarith only [q0, q1, q2, c3, c4]⟩
    · rcases pc4 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc4 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc4 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · exfalso; linarith only [a4, o0, o1, o2, o3, hs]
          · exfalso; linarith only [a0, a3, a4, o1, o2, hs]
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c3 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a3, a4, o1, o2, hs, r1]
        · rcases pc5 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨2, (show 2 < 5 by decide)⟩ ⟨3, (show 3 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 2 < 3 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x2 - w1 x3 + w2 x2 x3 ≤ 71 / 60
            rcases w2c4 x2 x3 a2 b2 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a0, a4, o1, o3, hs, r1]
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩ * Equiv.swap ⟨2, (show 2 < 5 by decide)⟩ ⟨4, (show 4 < 5 by decide)⟩, swap2_mem_pairings _ _ _ _ (Fin.ne_of_val_ne (show 0 ≠ 2 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 4 by decide)) (Fin.ne_of_val_ne (show 1 ≠ 2 by decide)) (Fin.ne_of_val_ne (show 1 ≠ 4 by decide)), ?_⟩
            rw [w12_swap2 _ _ _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)) (Fin.mk_lt_mk.mpr (show 2 < 4 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 2 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 4 by decide)) (Fin.ne_of_val_ne (show 1 ≠ 2 by decide)) (Fin.ne_of_val_ne (show 1 ≠ 4 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 - w1 x2 - w1 x4 + w2 x0 x1 + w2 x2 x4 ≤ 71 / 60
            rcases w2c3 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · rcases w2c4 x2 x4 a2 b2 with ⟨r2, e2⟩ | ⟨r2, e2⟩
              · norm_num [e1, e2, q0, q1, q2, q3, q4]
              · norm_num [e1, e2, q0, q1, q2, q3, q4]
            · rcases w2c4 x2 x4 a2 b2 with ⟨r2, e2⟩ | ⟨r2, e2⟩
              · norm_num [e1, e2, q0, q1, q2, q3, q4]
              · exfalso; linarith only [a3, a4, o1, hs, r1, r2]
        · exact ⟨1, one_mem_pairings _, by
            rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
            have c4 := w1le6 x4 l4 (by linarith only [b3, o3])
            linarith only [q0, q1, q2, q3, c4]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
          have c3 := w1le5 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le5 x4 l4 (by linarith only [b2, o2, o3])
          linarith only [q0, q1, q2, c3, c4]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          linarith only [q0, q1, q2, c3, c4]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
        have c2 := w1le5 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le5 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le5 x4 l4 (by linarith only [b1, o1, o2, o3])
        linarith only [q0, q1, c2, c3, c4]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        linarith only [q0, q1, c2, c3, c4]⟩
  · rcases pc4 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc4 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc4 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc4 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · exfalso; linarith only [a4, o0, o1, o2, o3, hs]
          · refine ⟨Equiv.swap ⟨3, (show 3 < 5 by decide)⟩ ⟨4, (show 4 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 3 < 4 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x3 - w1 x4 + w2 x3 x4 ≤ 71 / 60
            rcases w2c4 x3 x4 a3 b3 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [o0, o1, o2, hs, r1]
          · exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60; norm_num [q0, q1, q2, q3, q4]⟩
        · exact ⟨1, one_mem_pairings _, by
            rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
            have c4 := w1le5 x4 l4 (by linarith only [b3, o3])
            linarith only [q0, q1, q2, q3, c4]⟩
        · exact ⟨1, one_mem_pairings _, by
            rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
            have c4 := w1le6 x4 l4 (by linarith only [b3, o3])
            linarith only [q0, q1, q2, q3, c4]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
          have c3 := w1le5 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le5 x4 l4 (by linarith only [b2, o2, o3])
          linarith only [q0, q1, q2, c3, c4]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          linarith only [q0, q1, q2, c3, c4]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
        have c2 := w1le5 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le5 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le5 x4 l4 (by linarith only [b1, o1, o2, o3])
        linarith only [q0, q1, c2, c3, c4]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        linarith only [q0, q1, c2, c3, c4]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
      have c1 := w1le5 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le5 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le5 x3 l3 (by linarith only [b0, o0, o1, o2])
      have c4 := w1le5 x4 l4 (by linarith only [b0, o0, o1, o2, o3])
      linarith only [q0, c1, c2, c3, c4]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
      have c1 := w1le6 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le6 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le6 x3 l3 (by linarith only [b0, o0, o1, o2])
      have c4 := w1le6 x4 l4 (by linarith only [b0, o0, o1, o2, o3])
      linarith only [q0, c1, c2, c3, c4]⟩

set_option maxHeartbeats 4000000 in
theorem core6 (x0 x1 x2 x3 x4 x5 : ℝ) (l0 : 1 / 7 < x0) (l1 : 1 / 7 < x1) (l2 : 1 / 7 < x2) (l3 : 1 / 7 < x3) (l4 : 1 / 7 < x4) (l5 : 1 / 7 < x5) (u0 : x0 ≤ 1 / 2) (o0 : x1 ≤ x0) (o1 : x2 ≤ x1) (o2 : x3 ≤ x2) (o3 : x4 ≤ x3) (o4 : x5 ≤ x4) (hs : x0 + x1 + x2 + x3 + x4 + x5 ≤ 1) :
    ∃ σ ∈ pairings [x0, x1, x2, x3, x4, x5].length, w12 [x0, x1, x2, x3, x4, x5] σ ≤ 71 / 60 := by
  rcases pc2 x0 l0 u0 with ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩
  · exfalso; linarith only [a0, l5, o1, o2, o3, o4, hs]
  · rcases pc3 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · exfalso; linarith only [a1, l5, o0, o2, o3, o4, hs]
    · exfalso; linarith only [a0, a1, l5, o2, o3, o4, hs]
    · rcases pc5 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a0, a2, l5, o1, o3, o4, hs]
      · rcases pc6 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · rcases pc6 x5 l5 (le_trans o4 b4) with ⟨a5, b5, q5⟩
            · refine ⟨Equiv.swap ⟨0, (show 0 < 6 by decide)⟩ ⟨1, (show 1 < 6 by decide)⟩, swap_mem_pairings _ _, ?_⟩
              rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
              show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
              rcases w2c3 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
              · norm_num [e1, q0, q1, q2, q3, q4, q5]
              · exfalso; linarith only [a5, o1, o2, o3, o4, hs, r1]
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        have c5 := w1le6 x5 l5 (by linarith only [b1, o1, o2, o3, o4])
        linarith only [q0, q1, c2, c3, c4, c5]⟩
  · rcases pc4 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc4 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a2, l5, o0, o1, o3, o4, hs]
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a1, a3, l5, o0, o2, o4, hs]
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · rcases pc6 x5 l5 (le_trans o4 b4) with ⟨a5, b5, q5⟩
            · refine ⟨Equiv.swap ⟨2, (show 2 < 6 by decide)⟩ ⟨3, (show 3 < 6 by decide)⟩, swap_mem_pairings _ _, ?_⟩
              rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 2 < 3 by decide)), sum_w1]
              show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) - w1 x2 - w1 x3 + w2 x2 x3 ≤ 71 / 60
              rcases w2c5 x2 x3 a2 b2 with ⟨r1, e1⟩ | ⟨r1, e1⟩
              · norm_num [e1, q0, q1, q2, q3, q4, q5]
              · exfalso; linarith only [a1, a5, o0, o3, o4, hs, r1]
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          have c5 := w1le6 x5 l5 (by linarith only [b2, o2, o3, o4])
          linarith only [q0, q1, q2, c3, c4, c5]⟩
    · rcases pc5 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc5 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · exfalso; linarith only [a0, a4, l5, o1, o2, o3, hs]
          · exact ⟨1, one_mem_pairings _, by
              rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
              have c5 := w1le6 x5 l5 (by linarith only [b4, o4])
              linarith only [q0, q1, q2, q3, q4, c5]⟩
        · exact ⟨1, one_mem_pairings _, by
            rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
            have c4 := w1le6 x4 l4 (by linarith only [b3, o3])
            have c5 := w1le6 x5 l5 (by linarith only [b3, o3, o4])
            linarith only [q0, q1, q2, q3, c4, c5]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          have c5 := w1le6 x5 l5 (by linarith only [b2, o2, o3, o4])
          linarith only [q0, q1, q2, c3, c4, c5]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        have c5 := w1le6 x5 l5 (by linarith only [b1, o1, o2, o3, o4])
        linarith only [q0, q1, c2, c3, c4, c5]⟩
  · rcases pc5 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc5 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc5 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · rcases pc5 x5 l5 (le_trans o4 b4) with ⟨a5, b5, q5⟩ | ⟨a5, b5, q5⟩
            · exfalso; linarith only [a5, o0, o1, o2, o3, o4, hs]
            · exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60; norm_num [q0, q1, q2, q3, q4, q5]⟩
          · exact ⟨1, one_mem_pairings _, by
              rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
              have c5 := w1le6 x5 l5 (by linarith only [b4, o4])
              linarith only [q0, q1, q2, q3, q4, c5]⟩
        · exact ⟨1, one_mem_pairings _, by
            rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
            have c4 := w1le6 x4 l4 (by linarith only [b3, o3])
            have c5 := w1le6 x5 l5 (by linarith only [b3, o3, o4])
            linarith only [q0, q1, q2, q3, c4, c5]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          have c5 := w1le6 x5 l5 (by linarith only [b2, o2, o3, o4])
          linarith only [q0, q1, q2, c3, c4, c5]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        have c5 := w1le6 x5 l5 (by linarith only [b1, o1, o2, o3, o4])
        linarith only [q0, q1, c2, c3, c4, c5]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
      have c1 := w1le6 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le6 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le6 x3 l3 (by linarith only [b0, o0, o1, o2])
      have c4 := w1le6 x4 l4 (by linarith only [b0, o0, o1, o2, o3])
      have c5 := w1le6 x5 l5 (by linarith only [b0, o0, o1, o2, o3, o4])
      linarith only [q0, c1, c2, c3, c4, c5]⟩
theorem reduce (S : List ℝ) (hsort : S.Pairwise (fun a b => b ≤ a))
    (hr : ∀ x ∈ S, 1 / 7 < x ∧ x ≤ 1 / 2) (hs : S.sum ≤ 1) :
    ∃ σ ∈ pairings S.length, w12 S σ ≤ 71 / 60 := by
  match S, hsort, hr, hs with
  | [], _, _, _ => exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; norm_num⟩
  | [x0], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core1 x0 l0 u0  (by linarith)
  | [x0, x1], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    obtain ⟨l1, u1⟩ := hr x1 (by simp)
    have o0 : x1 ≤ x0 := List.rel_of_pairwise_cons hsort (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core2 x0 x1 l0 l1 u0 o0 (by linarith)
  | [x0, x1, x2], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    obtain ⟨l1, u1⟩ := hr x1 (by simp)
    obtain ⟨l2, u2⟩ := hr x2 (by simp)
    have o0 : x1 ≤ x0 := List.rel_of_pairwise_cons hsort (by simp)
    have o1 : x2 ≤ x1 := List.rel_of_pairwise_cons (hsort).of_cons (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core3 x0 x1 x2 l0 l1 l2 u0 o0 o1 (by linarith)
  | [x0, x1, x2, x3], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    obtain ⟨l1, u1⟩ := hr x1 (by simp)
    obtain ⟨l2, u2⟩ := hr x2 (by simp)
    obtain ⟨l3, u3⟩ := hr x3 (by simp)
    have o0 : x1 ≤ x0 := List.rel_of_pairwise_cons hsort (by simp)
    have o1 : x2 ≤ x1 := List.rel_of_pairwise_cons (hsort).of_cons (by simp)
    have o2 : x3 ≤ x2 := List.rel_of_pairwise_cons ((hsort).of_cons).of_cons (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core4 x0 x1 x2 x3 l0 l1 l2 l3 u0 o0 o1 o2 (by linarith)
  | [x0, x1, x2, x3, x4], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    obtain ⟨l1, u1⟩ := hr x1 (by simp)
    obtain ⟨l2, u2⟩ := hr x2 (by simp)
    obtain ⟨l3, u3⟩ := hr x3 (by simp)
    obtain ⟨l4, u4⟩ := hr x4 (by simp)
    have o0 : x1 ≤ x0 := List.rel_of_pairwise_cons hsort (by simp)
    have o1 : x2 ≤ x1 := List.rel_of_pairwise_cons (hsort).of_cons (by simp)
    have o2 : x3 ≤ x2 := List.rel_of_pairwise_cons ((hsort).of_cons).of_cons (by simp)
    have o3 : x4 ≤ x3 := List.rel_of_pairwise_cons (((hsort).of_cons).of_cons).of_cons (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core5 x0 x1 x2 x3 x4 l0 l1 l2 l3 l4 u0 o0 o1 o2 o3 (by linarith)
  | [x0, x1, x2, x3, x4, x5], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    obtain ⟨l1, u1⟩ := hr x1 (by simp)
    obtain ⟨l2, u2⟩ := hr x2 (by simp)
    obtain ⟨l3, u3⟩ := hr x3 (by simp)
    obtain ⟨l4, u4⟩ := hr x4 (by simp)
    obtain ⟨l5, u5⟩ := hr x5 (by simp)
    have o0 : x1 ≤ x0 := List.rel_of_pairwise_cons hsort (by simp)
    have o1 : x2 ≤ x1 := List.rel_of_pairwise_cons (hsort).of_cons (by simp)
    have o2 : x3 ≤ x2 := List.rel_of_pairwise_cons ((hsort).of_cons).of_cons (by simp)
    have o3 : x4 ≤ x3 := List.rel_of_pairwise_cons (((hsort).of_cons).of_cons).of_cons (by simp)
    have o4 : x5 ≤ x4 := List.rel_of_pairwise_cons ((((hsort).of_cons).of_cons).of_cons).of_cons (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core6 x0 x1 x2 x3 x4 x5 l0 l1 l2 l3 l4 l5 u0 o0 o1 o2 o3 o4 (by linarith)
  | x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rest, _, hr, hs =>
    exfalso
    obtain ⟨l0, -⟩ := hr x0 (by simp)
    obtain ⟨l1, -⟩ := hr x1 (by simp)
    obtain ⟨l2, -⟩ := hr x2 (by simp)
    obtain ⟨l3, -⟩ := hr x3 (by simp)
    obtain ⟨l4, -⟩ := hr x4 (by simp)
    obtain ⟨l5, -⟩ := hr x5 (by simp)
    obtain ⟨l6, -⟩ := hr x6 (by simp)
    have hrest : 0 ≤ rest.sum := List.sum_nonneg (fun x hx => le_of_lt (lt_trans (by norm_num) (hr x (by simp [hx])).1))
    simp only [List.sum_cons] at hs
    linarith

end P6c9b

open BinPacking.SmallItems in
theorem sol_6c9b70f9 (X : List ℝ) (hX : ∀ x ∈ X, 1 / 7 < x ∧ x ≤ 1 / 2)
    (hsum : X.sum ≤ 1) :
    W X ≤ 71 / 60 := by
  have hp : (sortDesc X).Perm X := List.mergeSort_perm _ _
  have hsorted : (sortDesc X).Pairwise (fun a b => b ≤ a) := by
    have h := List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; linarith)
      (fun a b => by simpa using le_total b a) X
    simpa [sortDesc] using h
  obtain ⟨σ, hσ, hw⟩ := P6c9b.reduce (sortDesc X) hsorted (fun x hx => hX x (hp.subset hx))
    (by rw [hp.sum_eq]; exact hsum)
  exact le_trans (Finset.inf'_le _ hσ) hw


namespace WLE_4c187921
open BinPacking.SmallItems

/-- `w₁₂` for a value function on `Fin n`. -/
noncomputable def wf (n : ℕ) (h : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => σ i = i), w1 (h i)) +
    ∑ i ∈ Finset.univ.filter (fun i => i < σ i), w2 (h i) (h (σ i))

lemma inv_of_sq {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : σ * σ = 1) (i : Fin n) : σ (σ i) = i := by
  have := congrArg (fun τ : Equiv.Perm (Fin n) => τ i) hσ
  simpa [Equiv.Perm.mul_apply] using this

lemma exists_w12_eq_wf (n : ℕ) (h : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (hσ : σ * σ = 1)
    (S : List ℝ) (hS : S = List.ofFn h) :
    ∃ σ' ∈ pairings S.length, w12 S σ' = wf n h σ := by
  subst hS
  let e : Fin (List.ofFn h).length ≃ Fin n := finCongr List.length_ofFn
  refine ⟨e.trans (σ.trans e.symm), ?_, ?_⟩
  · simp only [pairings, Finset.mem_filter, Finset.mem_univ, true_and]
    ext x
    simp [e, Equiv.Perm.mul_apply, inv_of_sq σ hσ]
  · unfold w12 wf
    congr 1
    · apply Finset.sum_equiv e
      · intro x; simp [e, Fin.ext_iff]
      · intro x _; simp [e]; rfl
    · apply Finset.sum_equiv e
      · intro x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Iff.rfl
      · intro x _; simp [e]; rfl

lemma W_le_wf (Z : List ℝ) (n : ℕ) (h : Fin n → ℝ) (hZ : sortDesc Z = List.ofFn h)
    (σ : Equiv.Perm (Fin n)) (hσ : σ * σ = 1) : W Z ≤ wf n h σ := by
  obtain ⟨σ', hσ', heq⟩ := exists_w12_eq_wf n h σ hσ (sortDesc Z) hZ
  unfold W
  rw [← heq]
  exact Finset.inf'_le _ hσ'

lemma sortDesc_pairwise (X : List ℝ) : (sortDesc X).Pairwise (fun a b => b ≤ a) := by
  have h := List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; linarith)
    (fun a b => by simpa using le_total b a) X
  simpa [sortDesc] using h

lemma sortDesc_eq_of (Z Y : List ℝ) (hp : Z.Perm Y) (hY : Y.Pairwise (fun a b => b ≤ a)) :
    sortDesc Z = Y := by
  have hp' : (sortDesc Z).Perm Y := (List.mergeSort_perm _ _).trans hp
  exact hp'.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h2 h1) (sortDesc_pairwise Z) hY

lemma W_perm (X Y : List ℝ) (h : X.Perm Y) : W X = W Y := by
  have : sortDesc X = sortDesc Y :=
    sortDesc_eq_of X (sortDesc Y) (h.trans (List.mergeSort_perm _ _).symm) (sortDesc_pairwise Y)
  have key : ∀ S T : List ℝ, S = T →
      (pairings S.length).inf' ⟨1, by simp [pairings]⟩ (w12 S) =
        (pairings T.length).inf' ⟨1, by simp [pairings]⟩ (w12 T) := by
    rintro S T rfl; rfl
  exact key _ _ this

lemma sort_key {n : ℕ} (g : Fin n → ℝ) (j k : Fin n) :
    (Tuple.sort (fun i => -g i)).symm j < (Tuple.sort (fun i => -g i)).symm k ↔
      g k < g j ∨ (g j = g k ∧ j < k) := by
  obtain ⟨hmono, htie⟩ := (Tuple.eq_sort_iff (f := fun i => -g i)
    (σ := Tuple.sort (fun i => -g i))).mp rfl
  have fwd : ∀ a b : Fin n, a < b →
      g (Tuple.sort (fun i => -g i) b) < g (Tuple.sort (fun i => -g i) a) ∨
      (g (Tuple.sort (fun i => -g i) a) = g (Tuple.sort (fun i => -g i) b) ∧
        Tuple.sort (fun i => -g i) a < Tuple.sort (fun i => -g i) b) := by
    intro a b hab
    have h1 : -g (Tuple.sort (fun i => -g i) a) ≤ -g (Tuple.sort (fun i => -g i) b) := hmono hab.le
    rcases lt_or_eq_of_le h1 with h2 | h2
    · left; linarith
    · right; exact ⟨by linarith, htie a b hab h2⟩
  constructor
  · intro hlt
    have := fwd _ _ hlt
    simpa using this
  · intro hor
    rcases lt_trichotomy ((Tuple.sort (fun i => -g i)).symm j)
      ((Tuple.sort (fun i => -g i)).symm k) with h | h | h
    · exact h
    · exfalso
      have hjk : j = k := by simpa using congrArg (Tuple.sort (fun i => -g i)) h
      subst hjk
      rcases hor with h' | h'
      · exact lt_irrefl _ h'
      · exact lt_irrefl _ h'.2
    · exfalso
      have := fwd _ _ h
      simp only [Equiv.apply_symm_apply] at this
      rcases hor with h' | h' <;> rcases this with h'' | h''
      · linarith
      · linarith [h''.1]
      · linarith [h'.1]
      · exact lt_asymm h'.2 h''.2

lemma orient_iff {n : ℕ} (g : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (hinv : ∀ i, σ (σ i) = i)
    (hor : ∀ j, j < σ j → g (σ j) ≤ g j) (j : Fin n) :
    (g (σ j) < g j ∨ (g j = g (σ j) ∧ j < σ j)) ↔ j < σ j := by
  constructor
  · rintro (h | h)
    · rcases lt_trichotomy j (σ j) with h1 | h1 | h1
      · exact h1
      · exfalso; rw [← h1] at h; exact lt_irrefl _ h
      · exfalso
        have := hor (σ j) (by rw [hinv]; exact h1)
        rw [hinv] at this
        linarith
    · exact h.2
  · intro h
    rcases lt_or_eq_of_le (hor j h) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨h1.symm, h⟩

lemma wf_reindex {n : ℕ} (g : Fin n → ℝ) (σT : Equiv.Perm (Fin n)) (hinv : ∀ i, σT (σT i) = i)
    (hor : ∀ j, j < σT j → g (σT j) ≤ g j) :
    wf n (g ∘ Tuple.sort (fun i => -g i))
      ((Tuple.sort (fun i => -g i)).trans (σT.trans (Tuple.sort (fun i => -g i)).symm)) =
      wf n g σT := by
  unfold wf
  congr 1
  · apply Finset.sum_equiv (Tuple.sort (fun i => -g i))
    · intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.trans_apply,
        Equiv.symm_apply_eq]
    · intro i _; rfl
  · apply Finset.sum_equiv (Tuple.sort (fun i => -g i))
    · intro i
      rw [Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, Equiv.trans_apply]
      rw [← orient_iff g σT hinv hor (Tuple.sort (fun i => -g i) i), ← sort_key g,
        Equiv.symm_apply_apply]
    · intro i _
      simp

lemma wf_split (SX SY : List ℝ) (σX : Equiv.Perm (Fin SX.length)) (σY : Equiv.Perm (Fin SY.length))
    (hX : SX.Pairwise (fun a b => b ≤ a)) (hY : SY.Pairwise (fun a b => b ≤ a))
    (hσX : σX * σX = 1) (hσY : σY * σY = 1) :
    ∃ (n : ℕ) (h : Fin n → ℝ) (σ : Equiv.Perm (Fin n)), σ * σ = 1 ∧
      (List.ofFn h).Perm (SX ++ SY) ∧ (List.ofFn h).Pairwise (fun a b => b ≤ a) ∧
      wf n h σ = w12 SX σX + w12 SY σY := by
  have iX := inv_of_sq σX hσX
  have iY := inv_of_sq σY hσY
  let g : Fin (SX.length + SY.length) → ℝ := Fin.append SX.get SY.get
  let σT : Equiv.Perm (Fin (SX.length + SY.length)) :=
    finSumFinEquiv.symm.trans ((σX.sumCongr σY).trans finSumFinEquiv)
  have hTl : ∀ i, σT (Fin.castAdd SY.length i) = Fin.castAdd SY.length (σX i) := by
    intro i; simp [σT]
  have hTr : ∀ i, σT (Fin.natAdd SX.length i) = Fin.natAdd SX.length (σY i) := by
    intro i; simp [σT]
  have hgl : ∀ i, g (Fin.castAdd SY.length i) = SX.get i := by intro i; simp [g]
  have hgr : ∀ i, g (Fin.natAdd SX.length i) = SY.get i := by intro i; simp [g]
  have hTinv : ∀ i, σT (σT i) = i := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [hTl, hTl, iX]
    · rw [hTr, hTr, iY]
  have hor : ∀ j, j < σT j → g (σT j) ≤ g j := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [hTl, hgl, hgl]
      intro hlt
      have hlt' : i < σX i := by
        rw [Fin.lt_def] at hlt ⊢; simpa using hlt
      exact List.pairwise_iff_get.mp hX i (σX i) hlt'
    · rw [hTr, hgr, hgr]
      intro hlt
      have hlt' : i < σY i := by
        rw [Fin.lt_def] at hlt ⊢; simpa using hlt
      exact List.pairwise_iff_get.mp hY i (σY i) hlt'
  refine ⟨SX.length + SY.length, g ∘ Tuple.sort (fun i => -g i),
    (Tuple.sort (fun i => -g i)).trans (σT.trans (Tuple.sort (fun i => -g i)).symm), ?_, ?_, ?_, ?_⟩
  · ext i
    simp [Equiv.Perm.mul_apply, hTinv]
  · have h1 := Equiv.Perm.ofFn_comp_perm (Tuple.sort (fun i => -g i)) g
    have h2 : List.ofFn g = SX ++ SY := by
      simp only [g, List.ofFn_fin_append, List.ofFn_get]
    rw [← h2]; exact h1
  · rw [List.pairwise_ofFn]
    intro i j hij
    have := Tuple.monotone_sort (fun i => -g i) hij.le
    simp only [Function.comp_apply] at this ⊢
    linarith
  · rw [wf_reindex g σT hTinv hor]
    unfold wf w12
    simp only [Finset.sum_filter]
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [hTl, hTr, hgl, hgr]
    have e1 : ∀ i : Fin SX.length,
        (Fin.castAdd SY.length (σX i) = Fin.castAdd SY.length i ↔ σX i = i) := by
      intro i; simp [Fin.ext_iff]
    have e2 : ∀ i : Fin SY.length,
        (Fin.natAdd SX.length (σY i) = Fin.natAdd SX.length i ↔ σY i = i) := by
      intro i; simp [Fin.ext_iff]
    have e3 : ∀ i : Fin SX.length,
        (Fin.castAdd SY.length i < Fin.castAdd SY.length (σX i) ↔ i < σX i) := by
      intro i; simp only [Fin.lt_def, Fin.val_castAdd]
    have e4 : ∀ i : Fin SY.length,
        (Fin.natAdd SX.length i < Fin.natAdd SX.length (σY i) ↔ i < σY i) := by
      intro i; simp only [Fin.lt_def, Fin.val_natAdd]; constructor <;> intro h <;> omega
    simp only [e1, e2, e3, e4]
    ring

lemma W_append_le (X Y : List ℝ) : W (X ++ Y) ≤ W X + W Y := by
  obtain ⟨σX, hσXm, hX⟩ := Finset.exists_mem_eq_inf' (s := pairings (sortDesc X).length)
    ⟨1, by simp [pairings]⟩ (w12 (sortDesc X))
  obtain ⟨σY, hσYm, hY⟩ := Finset.exists_mem_eq_inf' (s := pairings (sortDesc Y).length)
    ⟨1, by simp [pairings]⟩ (w12 (sortDesc Y))
  have hWX : W X = w12 (sortDesc X) σX := hX
  have hWY : W Y = w12 (sortDesc Y) σY := hY
  simp only [pairings, Finset.mem_filter, Finset.mem_univ, true_and] at hσXm hσYm
  obtain ⟨n, h, σ, hσ, hp, hs, heq⟩ := wf_split (sortDesc X) (sortDesc Y) σX σY
    (sortDesc_pairwise X) (sortDesc_pairwise Y) hσXm hσYm
  have hZ : sortDesc (X ++ Y) = List.ofFn h := by
    apply sortDesc_eq_of _ _ _ hs
    refine List.Perm.trans ?_ hp.symm
    exact ((List.mergeSort_perm _ _).append (List.mergeSort_perm _ _)).symm
  rw [hWX, hWY, ← heq]
  exact W_le_wf (X ++ Y) n h hZ σ hσ

lemma w12_nil (S : List ℝ) (hS : S = []) (σ : Equiv.Perm (Fin S.length)) : w12 S σ = 0 := by
  subst hS
  simp [w12]

lemma W_nil_le : W [] ≤ 0 := by
  unfold W
  have hm : (1 : Equiv.Perm (Fin (sortDesc ([] : List ℝ)).length)) ∈
      pairings (sortDesc ([] : List ℝ)).length := by simp [pairings]
  refine (Finset.inf'_le _ hm).trans (le_of_eq ?_)
  exact w12_nil _ (by simp [sortDesc]) _

lemma W_le_bins {ι : Type}
    (hbin : ∀ Y : List ℝ, (∀ y ∈ Y, 1 / 7 < y ∧ y ≤ 1 / 2) → Y.sum ≤ 1 → W Y ≤ 71 / 60)
    (v : ι → ℝ) (f : ι → ℕ) : ∀ (b : ℕ) (Q : List ι), (∀ i ∈ Q, f i < b) →
    (∀ i ∈ Q, 1 / 7 < v i ∧ v i ≤ 1 / 2) →
    (∀ j : ℕ, ((Q.filter (fun i => decide (f i = j))).map v).sum ≤ 1) →
    W (Q.map v) ≤ 71 / 60 * (b : ℝ) := by
  intro b
  induction b with
  | zero =>
    intro Q hf _ _
    have hQ : Q = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun i hi => by have := hf i hi; omega)
    subst hQ
    simpa using W_nil_le
  | succ b ih =>
    intro Q hf hv hs
    have hp : (Q.map v).Perm ((Q.filter (fun i => decide (f i = b))).map v ++
        (Q.filter (fun i => !decide (f i = b))).map v) := by
      rw [← List.map_append]
      exact ((List.filter_append_perm _ Q).symm).map v
    rw [W_perm _ _ hp]
    have h1 : W ((Q.filter (fun i => decide (f i = b))).map v) ≤ 71 / 60 := by
      apply hbin
      · intro y hy
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
        exact hv i (List.mem_of_mem_filter hi)
      · exact hs b
    have h2 : W ((Q.filter (fun i => !decide (f i = b))).map v) ≤ 71 / 60 * (b : ℝ) := by
      apply ih
      · intro i hi
        have hm := List.mem_filter.mp hi
        have h3 := hf i hm.1
        have h4 : f i ≠ b := by simpa using hm.2
        omega
      · intro i hi
        exact hv i (List.mem_of_mem_filter hi)
      · intro j
        refine le_trans ?_ (hs j)
        apply List.Sublist.sum_le_sum
        · exact (List.Sublist.filter _ List.filter_sublist).map v
        · intro y hy
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
          linarith [hv i (List.mem_of_mem_filter hi)]
    calc W ((Q.filter (fun i => decide (f i = b))).map v ++
          (Q.filter (fun i => !decide (f i = b))).map v)
        ≤ W ((Q.filter (fun i => decide (f i = b))).map v) +
          W ((Q.filter (fun i => !decide (f i = b))).map v) := W_append_le _ _
      _ ≤ 71 / 60 + 71 / 60 * (b : ℝ) := add_le_add h1 h2
      _ = 71 / 60 * ((b + 1 : ℕ) : ℝ) := by push_cast; ring

lemma W_le_of_assign
    (hbin : ∀ Y : List ℝ, (∀ y ∈ Y, 1 / 7 < y ∧ y ≤ 1 / 2) → Y.sum ≤ 1 → W Y ≤ 71 / 60)
    (X : List ℝ) (hX : ∀ x ∈ X, 1 / 7 < x ∧ x ≤ 1 / 2) (b : ℕ) (f : Fin X.length → Fin b)
    (hf : ∀ j : Fin b, ∑ i ∈ Finset.univ.filter (fun i => f i = j), X.get i ≤ 1) :
    W X ≤ 71 / 60 * (b : ℝ) := by
  have hmap : (List.finRange X.length).map X.get = X := List.map_get_finRange X
  have key := W_le_bins hbin X.get (fun i => ((f i : Fin b) : ℕ)) b (List.finRange X.length)
    (fun i _ => (f i).isLt) (fun i _ => hX _ (List.get_mem X i)) ?_
  · rwa [hmap] at key
  · intro j
    by_cases hj : j < b
    · have hfs := hf ⟨j, hj⟩
      have hnd : ((List.finRange X.length).filter
          (fun i => decide (((f i : Fin b) : ℕ) = j))).Nodup :=
        (List.nodup_finRange _).filter _
      rw [← List.sum_toFinset _ hnd]
      have hset : ((List.finRange X.length).filter
          (fun i => decide (((f i : Fin b) : ℕ) = j))).toFinset =
          Finset.univ.filter (fun i => f i = ⟨j, hj⟩) := by
        ext i; simp [Fin.ext_iff]
      rw [hset]; exact hfs
    · have : (List.finRange X.length).filter (fun i => decide (((f i : Fin b) : ℕ) = j)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro i _
        have := (f i).isLt
        simp only [decide_eq_true_eq]
        omega
      rw [this]; simp

lemma W_le_opt
    (hbin : ∀ Y : List ℝ, (∀ y ∈ Y, 1 / 7 < y ∧ y ≤ 1 / 2) → Y.sum ≤ 1 → W Y ≤ 71 / 60)
    (X : List ℝ) (hX : ∀ x ∈ X, 1 / 7 < x ∧ x ≤ 1 / 2) :
    W X ≤ 71 / 60 * (optBins X : ℝ) := by
  have hne : {b : ℕ | ∃ f : Fin X.length → Fin b, ∀ j : Fin b,
      ∑ i ∈ Finset.univ.filter (fun i => f i = j), X.get i ≤ 1}.Nonempty := by
    refine ⟨X.length, id, fun j => ?_⟩
    have : Finset.univ.filter (fun i : Fin X.length => id i = j) = {j} := by ext i; simp
    rw [this, Finset.sum_singleton]
    linarith [hX _ (List.get_mem X j)]
  obtain ⟨f, hf⟩ := Nat.sInf_mem hne
  exact W_le_of_assign hbin X hX _ f hf

end WLE_4c187921

end

/- WeightsAgree.lean -/
section

namespace BinPacking.Decreasing

-- This normalization is from the accepted proof of the Decreasing-model Lemma 4.2.
private lemma floor_cast (x : ℝ) (hx : 0 < x) : ((⌊1 / x⌋ : ℤ) : ℝ) = ((⌊1 / x⌋₊ : ℕ) : ℝ) := by
  have h : (0:ℝ) ≤ 1 / x := by positivity
  rw [← Int.natCast_floor_eq_floor h]
  simp

private lemma w1_eq (x : ℝ) (hx : 0 < x) : BinPacking.Decreasing.w1 x = BinPacking.SmallItems.w1 x := by
  unfold BinPacking.Decreasing.w1 BinPacking.SmallItems.w1 BinPacking.Decreasing.pieceNum
  rw [floor_cast x hx]

private lemma isPiece (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) : BinPacking.SmallItems.IsPiece ⌊1/x⌋₊ x := by
  have h1 : (1:ℝ) ≤ 1/x := by rw [le_div_iff₀ hx]; linarith
  have hk1 : 1 ≤ ⌊1/x⌋₊ := Nat.le_floor (by simpa using h1)
  have hle : ((⌊1/x⌋₊ : ℕ) : ℝ) ≤ 1/x := Nat.floor_le (by positivity)
  have hlt : 1/x < ((⌊1/x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hkpos : (0:ℝ) < ((⌊1/x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hk1
  rw [div_lt_iff₀ hx] at hlt
  rw [le_div_iff₀ hx] at hle
  constructor
  · rw [div_lt_iff₀ (by positivity)]; linarith
  · rw [le_div_iff₀ hkpos]; linarith

private lemma w2_eq (x y : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (hy : 0 < y) :
    BinPacking.Decreasing.w2 x y = BinPacking.SmallItems.w2 x y := by
  unfold BinPacking.Decreasing.w2 BinPacking.SmallItems.w2 BinPacking.Decreasing.ObeysRelation
    BinPacking.SmallItems.ObeysRelation
  rw [w1_eq x hx, w1_eq y hy]
  unfold BinPacking.Decreasing.pieceNum
  rw [floor_cast x hx]
  have hp := isPiece x hx hx1
  by_cases h : ((⌊1/x⌋₊ : ℕ):ℝ) * x + y ≤ 1
  · rw [if_pos h, if_pos ⟨hp, h⟩]
  · rw [if_neg h, if_neg (fun h' => h h'.2)]

private lemma w12_eq (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) (σ : Equiv.Perm (Fin S.length)) :
    BinPacking.Decreasing.w12 S σ = BinPacking.SmallItems.w12 S σ := by
  unfold BinPacking.Decreasing.w12 BinPacking.SmallItems.w12
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := hS _ (List.get_mem S i)
  have hj := hS _ (List.get_mem S (σ i))
  by_cases h1 : σ i = i
  · have h2 : ¬ i < σ i := by rw [h1]; exact lt_irrefl _
    rw [if_pos h1, if_pos h1, if_neg h2, w1_eq _ hi.1]; ring
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : i < σ i
    · rw [if_pos h2, if_pos h2, w2_eq _ _ hi.1 hi.2 hj.1]; ring
    · rw [if_neg h2, if_neg h2]; ring

theorem weight_eq_smallItems (X : List ℝ) (hX : ∀ a ∈ X, 0 < a ∧ a ≤ 1) :
    BinPacking.Decreasing.W X = BinPacking.SmallItems.W X := by
  have hS : ∀ a ∈ BinPacking.SmallItems.sortDesc X, 0 < a ∧ a ≤ 1 := fun a ha =>
    hX a (List.mem_mergeSort.1 ha)
  unfold BinPacking.Decreasing.W BinPacking.SmallItems.W
  apply le_antisymm
  · apply Finset.le_inf'
    intro σ hσ
    have hm : (⇑σ) ∈ BinPacking.Decreasing.partitions (BinPacking.SmallItems.sortDesc X).length := by
      simp only [BinPacking.SmallItems.pairings, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      simp only [BinPacking.Decreasing.partitions, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i
      exact Equiv.ext_iff.1 hσ i
    calc _ ≤ BinPacking.Decreasing.w12 (BinPacking.Decreasing.sortDesc X) ⇑σ := Finset.inf'_le _ hm
      _ = _ := w12_eq _ hS σ
  · apply Finset.le_inf'
    intro m hm
    simp only [BinPacking.Decreasing.partitions, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    have hinv : Function.Involutive m := hm
    have hσ : hinv.toPerm m ∈ BinPacking.SmallItems.pairings (BinPacking.Decreasing.sortDesc X).length := by
      simp only [BinPacking.SmallItems.pairings, Finset.mem_filter, Finset.mem_univ, true_and]
      apply Equiv.ext
      intro i
      show m (m i) = i
      exact hm i
    calc _ ≤ BinPacking.SmallItems.w12 _ (hinv.toPerm m) := Finset.inf'_le _ hσ
      _ = BinPacking.Decreasing.w12 _ (hinv.toPerm m) := (w12_eq _ hS _).symm
      _ = _ := rfl

end BinPacking.Decreasing

end

/- ResidualWeight.lean -/
section

namespace BinPacking.Decreasing

/-- Johnson's Claim 5.9.1 with the residual items supplied by the first-fit run. -/
theorem residual_weight (L : List ℝ) (hL : IsList L)
    (h211 : ∀ a ∈ L, (2 / 11 : ℝ) < a) :
    W (residualItems L) ≥
      (FFD L : ℝ) - ((L.filter (fun a => decide ((1 / 2 : ℝ) < a))).length : ℝ) - 4 := by
  let residual := residualItems L
  obtain ⟨hsub, hcount⟩ := residual_firstFit L
  have original : ∀ a ∈ residual, a ∈ L := fun a ha =>
    List.mem_mergeSort.mp (List.mem_of_mem_filter (hsub.subset ha))
  have range : ∀ a ∈ residual, (1 / 6 : ℝ) < a ∧ a ≤ 1 / 2 := fun a ha =>
    ⟨by linarith [h211 a (original a ha)], by simpa using (List.mem_filter.mp (hsub.subset ha)).2⟩
  have hweight := WFFD_9ce81529.W_ge 6 (by decide) residual
    (fun a ha => hL a (original a ha)) (by simpa using range)
  change BinPacking.SmallItems.W residual ≥ (FFD residual : ℝ) - (6 : ℝ) + 2 at hweight
  rw [weight_eq_smallItems (residualItems L) (fun a ha => hL a (original a ha)), hcount, Nat.cast_add]
  linarith

end BinPacking.Decreasing

end

/- ResponsibilityReduction.lean -/
section

namespace BinPacking.Decreasing

theorem weight_flatten_le_sum (parts : List (List ℝ)) (hparts : IsList parts.flatten) :
    W parts.flatten ≤ (parts.map W).sum := by
  induction parts with
  | nil =>
    simpa [weight_eq_smallItems [] hparts] using WLE_4c187921.W_nil_le
  | cons part rest ih =>
    have hpart : IsList part := fun a ha => hparts a (List.mem_append_left _ ha)
    have hrest : IsList rest.flatten := fun a ha => hparts a (List.mem_append_right _ ha)
    have hadd : W (part ++ rest.flatten) ≤ W part + W rest.flatten := by
      simpa only [← weight_eq_smallItems (part ++ rest.flatten) hparts,
        ← weight_eq_smallItems part hpart, ← weight_eq_smallItems rest.flatten hrest] using
        WLE_4c187921.W_append_le part rest.flatten
    exact hadd.trans (add_le_add (le_refl _) (ih hrest))

/-- Once an optimal packing's responsibility groups cover the residual input and
obey the per-bin and total credit bounds, the restricted first-fit theorem follows. -/
theorem ffd_le_of_optimal_responsibilities (L : List ℝ) (hL : IsList L)
    (h211 : ∀ a ∈ L, (2 / 11 : ℝ) < a)
    (assign : Fin L.length → Fin (optBins L))
    (hfit : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), L.get i ≤ 1)
    (pieces : Fin (optBins L) → List ℝ) (credit : Fin (optBins L) → ℝ)
    (hcover : (residualItems L).Perm (List.ofFn pieces).flatten)
    (hbin : ∀ i, W (pieces i) + credit i ≤
      11 / 9 * ((if i ∈ binsWithLargeItems assign then 0 else 1) + credit i))
    (hcredit : ∑ i, credit i ≤ ((L.filter (fun a => decide ((1 / 2 : ℝ) < a))).length : ℝ)) :
    (FFD L : ℝ) ≤ 11 / 9 * (optBins L : ℝ) + 4 := by
  have hsub := (residual_firstFit L).1
  have hgroups : IsList (List.ofFn pieces).flatten := fun item hitem =>
    hL item (List.mem_mergeSort.mp (List.mem_of_mem_filter (hsub.subset (hcover.mem_iff.mpr hitem))))
  exact ffd_le_of_responsibility L (residualItems L)
    (L.filter (fun a => decide ((1 / 2 : ℝ) < a))).length pieces
    (fun i => if i ∈ binsWithLargeItems assign then 0 else 1) credit
    (residual_weight L hL h211) (weight_le_sum_of_perm pieces hcover (weight_flatten_le_sum _ hgroups))
    (sum_nonLarge_bins hL assign hfit) hbin hcredit

end BinPacking.Decreasing

end

/- OrdinaryGroupCost.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

open PieceChains

noncomputable section

variable {S : List ℝ} (p : AlignedPacking S)

def ordinaryDirectPieces (item : NonLargePosition S) : List ℝ :=
  (p.ordinaryDirect item).toList.map residualSize

def ordinaryIndirectPieces (item : NonLargePosition S) : List ℝ :=
  (p.ordinaryIndirectPositions item).toList.map residualSize

theorem ordinaryOwnerPieces_perm_direct_indirect (item : NonLargePosition S) :
    (p.ordinaryOwnerPieces item).Perm (p.ordinaryDirectPieces item ++ p.ordinaryIndirectPieces item) := by
  classical
  have direct (r : ResidualPosition S) :
      r ∈ (p.ordinaryDirect item).toList ↔ r ∈ p.ordinaryDirectPositions item :=
    Option.mem_toList.trans (p.ordinaryDirect_eq_some_iff item r)
  have nodup : (p.ordinaryOwnerPositions item).Nodup := p.residualPositions_nodup.filter _
  have disjoint : List.Disjoint (p.ordinaryDirect item).toList
      (p.ordinaryIndirectPositions item).toList := fun r inDirect inIndirect =>
    Finset.disjoint_left.mp (p.ordinary_positions_disjoint item)
      ((direct r).mp inDirect) (Finset.mem_toList.mp inIndirect)
  have nodupParts := (Option.toList_nodup (p.ordinaryDirect item)).append
    (Finset.nodup_toList (p.ordinaryIndirectPositions item)) disjoint
  have perm := (List.perm_ext_iff_of_nodup nodup nodupParts).mpr fun r => by
    rw [List.mem_append, direct, Finset.mem_toList, p.mem_ordinaryIndirectPositions_iff,
      p.mem_ordinaryDirectPositions_iff]
    simp [ordinaryOwnerPositions, mem_ownerGroup_iff, p.mem_residualPositions, ← and_or_left]
    exact fun _ => (em _).symm
  simpa only [ordinaryOwnerPieces, ordinaryDirectPieces, ordinaryIndirectPieces, List.map_append]
    using perm.map residualSize

theorem ordinaryDirectPieces_weight_sum (item : NonLargePosition S) :
    ((p.ordinaryDirectPieces item).map w1).sum = (p.ordinaryWeights item).direct := by
  cases observed : p.ordinaryDirect item <;> simp [ordinaryDirectPieces,
    ordinaryWeights, ordinaryDirectWeight, observed]

theorem ordinaryIndirectPieces_weight_sum (item : NonLargePosition S) :
    ((p.ordinaryIndirectPieces item).map w1).sum = (p.ordinaryWeights item).indirect := by
  classical
  unfold ordinaryIndirectPieces ordinaryWeights ordinaryIndirectWeight
  rw [List.map_map, ← List.sum_toFinset _ (Finset.nodup_toList _), Finset.toList_toFinset]
  rfl

theorem ordinaryOwnerPieces_weight_sum (item : NonLargePosition S) :
    ((p.ordinaryOwnerPieces item).map w1).sum =
      (p.ordinaryWeights item).direct + (p.ordinaryWeights item).indirect := by
  rw [((p.ordinaryOwnerPieces_perm_direct_indirect item).map w1).sum_eq, List.map_append,
    List.sum_append, p.ordinaryDirectPieces_weight_sum, p.ordinaryIndirectPieces_weight_sum]

def ordinaryGroupCost (owners : List (NonLargePosition S)) : ℝ :=
  W (owners.flatMap p.ordinaryOwnerPieces) -
    2 / 9 * (owners.map (ResponsibilityWeights.credit ∘ p.ordinaryWeights)).sum

theorem ordinaryGroupCost_perm {owners other : List (NonLargePosition S)}
    (perm : owners.Perm other) : p.ordinaryGroupCost owners = p.ordinaryGroupCost other := by
  unfold ordinaryGroupCost
  rw [weight_perm (perm.flatMap_right p.ordinaryOwnerPieces), (perm.map _).sum_eq]

theorem ordinaryGroupPieces_valid (owners : List (NonLargePosition S)) :
    IsList (owners.flatMap p.ordinaryOwnerPieces) := by
  intro a ha
  obtain ⟨i, _, member⟩ := List.mem_flatMap.mp ha
  obtain ⟨item, _, rfl⟩ := List.mem_map.mp member
  exact p.valid _ (List.get_mem S item.val.val)

/-- Bounding the costs of disjoint groups bounds the cost of the whole bin. -/
theorem ordinaryGroupCost_append_le (left right : List (NonLargePosition S)) :
    p.ordinaryGroupCost (left ++ right) ≤ p.ordinaryGroupCost left + p.ordinaryGroupCost right := by
  have valid := p.ordinaryGroupPieces_valid (left ++ right)
  rw [List.flatMap_append] at valid
  have weights : W (left.flatMap p.ordinaryOwnerPieces ++ right.flatMap p.ordinaryOwnerPieces) ≤
      W (left.flatMap p.ordinaryOwnerPieces) + W (right.flatMap p.ordinaryOwnerPieces) := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
      weight_flatten_le_sum [left.flatMap p.ordinaryOwnerPieces, right.flatMap p.ordinaryOwnerPieces]
        (by simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using valid)
  simp only [ordinaryGroupCost, List.flatMap_append, List.map_append, List.sum_append]
  linarith

theorem ordinaryGroupCost_le_singleton_costs (owners : List (NonLargePosition S)) :
    p.ordinaryGroupCost owners ≤ (owners.map (fun i => (p.ordinaryWeights i).weightedCost 1)).sum := by
  unfold ordinaryGroupCost
  have weights := weight_le_singleton_sum (owners.flatMap p.ordinaryOwnerPieces)
  rw [List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map, List.map_map] at weights
  change W (owners.flatMap p.ordinaryOwnerPieces) ≤
    (owners.map (fun item => ((p.ordinaryOwnerPieces item).map w1).sum)).sum at weights
  have sums (items : List (NonLargePosition S)) :
      (items.map (fun item => ((p.ordinaryOwnerPieces item).map w1).sum)).sum -
      2 / 9 * (items.map (ResponsibilityWeights.credit ∘ p.ordinaryWeights)).sum =
      (items.map (fun i => (p.ordinaryWeights i).weightedCost 1)).sum := by
    induction items with
    | nil => simp
    | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply]
      rw [← ih, p.ordinaryOwnerPieces_weight_sum]
      unfold ResponsibilityWeights.weightedCost
      ring
  simpa only [← sums owners] using sub_le_sub_right weights
    (2 / 9 * (owners.map (ResponsibilityWeights.credit ∘ p.ordinaryWeights)).sum)

theorem ordinaryGroupCost_pair_le_of_direct (left right : NonLargePosition S) :
    p.ordinaryGroupCost [left, right] ≤ W (p.ordinaryDirectPieces left ++ p.ordinaryDirectPieces right) +
      (p.ordinaryWeights left).indirect + (p.ordinaryWeights right).indirect -
      2 / 9 * ((p.ordinaryWeights left).credit + (p.ordinaryWeights right).credit) := by
  let dx := p.ordinaryDirectPieces left
  let dy := p.ordinaryDirectPieces right
  let ix := p.ordinaryIndirectPieces left
  let iy := p.ordinaryIndirectPieces right
  let blocks := [dx ++ dy, ix, iy]
  have reorder : ([left, right].flatMap p.ordinaryOwnerPieces).Perm blocks.flatten := by
    have separate := (p.ordinaryOwnerPieces_perm_direct_indirect left).append
      (p.ordinaryOwnerPieces_perm_direct_indirect right)
    have swap := (List.perm_append_comm_assoc ix dy iy).append_left dx
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, blocks, List.flatten_cons,
      List.flatten_nil, List.append_assoc, dx, dy, ix, iy] using
      separate.trans (by simpa only [List.append_assoc, dx, dy, ix, iy] using swap)
  have valid : IsList blocks.flatten := fun a ha =>
    p.ordinaryGroupPieces_valid [left, right] a (reorder.mem_iff.mpr ha)
  have sum := weight_flatten_le_sum blocks valid
  have indirectX := weight_le_singleton_sum ix
  have indirectY := weight_le_singleton_sum iy
  rw [show ix = p.ordinaryIndirectPieces left from rfl, p.ordinaryIndirectPieces_weight_sum] at indirectX
  rw [show iy = p.ordinaryIndirectPieces right from rfl, p.ordinaryIndirectPieces_weight_sum] at indirectY
  have total : W blocks.flatten ≤ W (dx ++ dy) + W ix + W iy := by
    simpa only [blocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, add_assoc] using sum
  unfold ordinaryGroupCost
  rw [weight_perm reorder]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Function.comp_apply]
  linarith

theorem direct_pair_weight_le_plain (left right : NonLargePosition S) :
    W (p.ordinaryDirectPieces left ++ p.ordinaryDirectPieces right) ≤
      (p.ordinaryWeights left).direct + (p.ordinaryWeights right).direct := by
  simpa only [List.map_append, List.sum_append, p.ordinaryDirectPieces_weight_sum] using
    weight_le_singleton_sum (p.ordinaryDirectPieces left ++ p.ordinaryDirectPieces right)

end

end BinPacking.Decreasing.AlignedPacking

end

/- assembly/NonLargeBinBudget.lean -/
section

namespace BinPacking.Decreasing

/-- Evaluate a singleton and pair partition using a subadditive cost. -/
theorem DiscountPlan.cost_le {Piece : Type*} {hasC : Bool} {size : Piece → ℝ}
    {items : List Piece} {budget : ℝ} (plan : DiscountPlan hasC size items budget)
    (cost : List Piece → ℝ) (appendCost : ∀ X Y, cost (X ++ Y) ≤ cost X + cost Y)
    (permCost : ∀ ⦃X Y⦄, X.Perm Y → cost X = cost Y)
    (singleton : ∀ group, group ⊆ items →
      cost group ≤ (group.map (singletonAllowance hasC ∘ smallPieceClass ∘ size)).sum)
    (pair : ∀ a ∈ items, ∀ b ∈ items, ∀ allowance,
      pairAllowance hasC (smallPieceClass (size a)) (smallPieceClass (size b)) = some allowance →
      ObeysRelation (size a) (size b) → cost [a, b] ≤ allowance) :
    cost items ≤ budget := by
  induction plan with
  | singletons items => exact singleton items (fun _ h => h)
  | pair left right row relation tail ih =>
      calc
        _ ≤ cost [left, right] + cost _ := appendCost [left, right] _
        _ ≤ _ := add_le_add (pair left (by simp) right (by simp) _ row relation)
          (ih (fun group included => singleton group (fun _ ha => by simp [included ha]))
            (fun a ha b hb => pair a (by simp [ha]) b (by simp [hb])))
  | perm reorder plan ih =>
      rw [← permCost reorder]
      exact ih (fun group included => singleton group (fun _ ha => reorder.subset (included ha)))
        (fun a ha b hb => pair a (reorder.subset ha) b (reorder.subset hb))

namespace AlignedPacking

/-- Claim 5.9.28 reduces to the local pair bound and the five exceptional
configuration budgets for the actual ordinary responsibility groups. -/
theorem ordinaryGroupCost_le_of_configurations {S : List ℝ} (p : AlignedPacking S) (hasC : Bool)
    (items : List (NonLargePosition S))
    (sorted : items.Pairwise (fun a b => S.get b.val ≤ S.get a.val))
    (small : ∀ a ∈ items, 2 / 11 < S.get a.val ∧ S.get a.val ≤ 1 / 2)
    (fits : (items.map fun a => S.get a.val).sum ≤ 1)
    (admissible : ∀ a ∈ items, (p.ordinaryWeights a).Admissible hasC (smallPieceClass (S.get a.val)))
    (pair : ∀ a ∈ items, ∀ b ∈ items, ∀ allowance,
      pairAllowance hasC (smallPieceClass (S.get a.val)) (smallPieceClass (S.get b.val)) = some allowance →
      ObeysRelation (S.get a.val) (S.get b.val) → p.ordinaryGroupCost [a, b] ≤ allowance)
    (exceptional : (items.map fun a => smallPieceClass (S.get a.val)) ∈ exceptionalConfigurations hasC →
      p.ordinaryGroupCost items ≤ 11 / 9) : p.ordinaryGroupCost items ≤ 11 / 9 := by
  rcases nonLarge_bin_configuration hasC (fun a : NonLargePosition S => S.get a.val)
    items sorted small fits with ⟨budget, cap, plan⟩ | hard
  · refine (plan.cost_le p.ordinaryGroupCost p.ordinaryGroupCost_append_le
      (fun ⦃_ _⦄ => p.ordinaryGroupCost_perm) ?_ pair).trans cap
    intro group included
    exact (p.ordinaryGroupCost_le_singleton_costs group).trans
      (List.sum_le_sum fun a ha => (admissible a (included ha)).cost_le_allowance)
  · exact exceptional hard

/-- The sorted sizes of the indexed ordinary owners are the bin's optimal sizes. -/
theorem ordinaryOwners_sizes {S : List ℝ} (p : AlignedPacking S)
    (bin : Fin (optBins S)) (outside : ¬isLargeBin S bin.val) :
    ((p.ordinaryOwners bin outside).map fun a => S.get a.val) = assignmentBin p.assign bin := by
  rw [assignmentBin, ← p.ordinaryOwners_map_val bin outside, List.map_map]
  rfl

/-- On an actual non-A optimal bin, the classified responsibility cost
gives (5.9C) once the applicable pair and exceptional bounds are supplied. -/
theorem nonLarge_bin_budget_of_configurations {S : List ℝ} (p : AlignedPacking S) (hasC : Bool)
    (bin : Fin (optBins S)) (outside : ¬isLargeBin S bin.val)
    (case_iff : hasC = true ↔ HasResidualC S)
    (residualCD : ∃ r : ResidualPosition S, (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3)
    (pair : ∀ a ∈ p.ordinaryOwners bin outside, ∀ b ∈ p.ordinaryOwners bin outside, ∀ allowance,
      pairAllowance hasC (smallPieceClass (S.get a.val)) (smallPieceClass (S.get b.val)) = some allowance →
      ObeysRelation (S.get a.val) (S.get b.val) → p.ordinaryGroupCost [a, b] ≤ allowance)
    (exceptional : ((p.ordinaryOwners bin outside).map fun a => smallPieceClass (S.get a.val)) ∈
      exceptionalConfigurations hasC → p.ordinaryGroupCost (p.ordinaryOwners bin outside) ≤ 11 / 9) :
    W (p.responsiblePieces bin) + p.credit bin ≤ 11 / 9 * (1 + p.credit bin) := by
  let owners := p.ordinaryOwners bin outside
  have sorted : owners.Pairwise (fun a b => S.get b.val ≤ S.get a.val) := by
    have assignmentSorted := assignmentBin_sorted p.assign bin p.sorted
    rw [← p.ordinaryOwners_sizes bin outside] at assignmentSorted
    exact List.pairwise_map.mp assignmentSorted
  have small (a : NonLargePosition S) : 2 / 11 < S.get a.val ∧ S.get a.val ≤ 1 / 2 :=
    ⟨p.threshold _ (List.get_mem S a.val), le_of_not_gt fun large =>
      (Nat.not_lt_of_ge a.property) ((largeItem_iff_lt_filter_length p.sorted a.val).mp large)⟩
  have fits : (owners.map fun a => S.get a.val).sum ≤ 1 := by
    rw [p.ordinaryOwners_sizes bin outside, assignmentBin_sum]
    exact p.fits bin
  have bounded := p.ordinaryGroupCost_le_of_configurations hasC owners sorted (fun a _ => small a) fits
    (fun a _ => p.ordinaryWeights_admissible a hasC _ case_iff residualCD
      (smallPieceClass_bounds (small a).1 (small a).2)) pair exceptional
  have creditSum : p.credit bin = (owners.map (ResponsibilityWeights.credit ∘ p.ordinaryWeights)).sum :=
    p.credit_eq_sum_ordinaryOwners bin outside
  rw [ordinaryGroupCost, List.flatMap_def,
    ← weight_perm (p.responsiblePieces_perm_ordinaryOwners bin outside), ← creditSum] at bounded
  linarith

end AlignedPacking
end BinPacking.Decreasing

end

/- small-only/OrderedMatching.lean -/
section

set_option autoImplicit false

namespace BinPacking.Decreasing

/-- The matching comparison used in Johnson's Lemma 4.5. If an optimal match is
absent in the greedy matching, every optimal bin for that item or an earlier
item already has a greedy match. The last missing item gives a cut at which to
compare the two matchings. -/
theorem card_optimal_matches_le_greedy_matches {Piece Bin : Type*} [LinearOrder Piece]
    (optimal greedy : Finset Piece) (optimalBin greedyBin : Piece → Bin)
    (distinct : Set.InjOn optimalBin ↑optimal)
    (occupied : ∀ x ∈ optimal, x ∉ greedy → ∀ p ∈ optimal, p ≤ x →
      ∃ q ∈ greedy, q < x ∧ greedyBin q = optimalBin p) :
    optimal.card ≤ greedy.card := by
  classical
  by_cases bad : (optimal \ greedy).Nonempty
  · let last := (optimal \ greedy).max' bad
    have hlast := Finset.mem_sdiff.mp (Finset.max'_mem (optimal \ greedy) bad)
    have early : (optimal.filter (· ≤ last)).card ≤ (greedy.filter (· ≤ last)).card := by
      have contained : (optimal.filter (· ≤ last)).image optimalBin ⊆
          (greedy.filter (· ≤ last)).image greedyBin := by
        intro b hb
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
        obtain ⟨hopt, hle⟩ := Finset.mem_filter.mp hp
        obtain ⟨q, hgreedy, hlt, heq⟩ := occupied last hlast.1 hlast.2 p hopt hle
        exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hgreedy, hlt.le⟩, heq⟩
      have hcard := Finset.card_le_card contained
      rw [Finset.card_image_of_injOn (distinct.mono (Finset.filter_subset _ _))] at hcard
      exact hcard.trans Finset.card_image_le
    have late : (optimal.filter (fun p => ¬p ≤ last)).card ≤
        (greedy.filter (fun p => ¬p ≤ last)).card := by
      apply Finset.card_le_card
      intro p hp
      obtain ⟨hopt, hgt⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_filter.mpr ⟨?_, hgt⟩
      by_contra hnot
      have hbad := Finset.mem_sdiff.mpr ⟨hopt, hnot⟩
      exact hgt (Finset.le_max' _ _ hbad)
    rw [← Finset.card_filter_add_card_filter_not (s := optimal) (p := (· ≤ last)),
      ← Finset.card_filter_add_card_filter_not (s := greedy) (p := (· ≤ last))]
    exact Nat.add_le_add early late
  · apply Finset.card_le_card
    intro x hx
    by_contra hnot
    exact bad ⟨x, Finset.mem_sdiff.mpr ⟨hx, hnot⟩⟩

end BinPacking.Decreasing

end

/- small-only/SmallTail.lean -/
section

set_option autoImplicit false

namespace BinPacking.Decreasing

private theorem getD_inside {α : Type*} (xs : List α) (i : ℕ) (fallback : α)
    (hi : i < xs.length) : xs.getD i fallback = xs[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

/-- First Fit passes over an earlier bin only when its current contents reject the item. -/
theorem earlier_rejection {S : List ℝ} (i : Fin S.length) (j : ℕ)
    (before : j < binOf ffChoice S i) :
    1 < (FirstFitHistory.contents S i.val j).sum + S.get i := by
  let bins := run ffChoice (S.take i.val)
  change j < bins.findIdx (fun B : List ℝ => decide (B.sum + S.get i ≤ 1)) at before
  have rejected := List.not_of_lt_findIdx before
  have existsBin : j < bins.length := before.trans_le List.findIdx_le_length
  rw [show FirstFitHistory.contents S i.val j = bins.getD j [] from rfl,
    getD_inside _ _ _ existsBin]
  simpa using rejected

/-- A piece assigned to the right of a bin cannot fit in that bin at the end of the run. -/
theorem final_rejection {S : List ℝ} (hS : IsList S) (i : Fin S.length) (j : ℕ)
    (before : j < binOf ffChoice S i) :
    1 < ((run ffChoice S).getD j []).sum + S.get i := by
  have early := earlier_rejection i j before
  have grows : (FirstFitHistory.contents S i.val j).sum ≤
      ((run ffChoice S).getD j []).sum := by
    have pref := FirstFitHistory.contents_prefix S (b := j) i.isLt.le
    rw [show FirstFitHistory.contents S S.length j = (run ffChoice S).getD j [] by
      simp [FirstFitHistory.contents]] at pref
    obtain ⟨rest, hrest⟩ := pref
    rw [← hrest, List.sum_append]
    apply le_add_of_nonneg_right
    apply List.sum_nonneg
    intro a ha
    have hmem : a ∈ (run ffChoice S).getD j [] := by rw [← hrest]; simp [ha]
    exact (hS a (FirstFitHistory.run_getD_subset S j hmem)).1.le
  linarith only [early, grows]

/-- The bin of a piece is already present by the end of every prefix containing that piece. -/
theorem binOf_lt_ff_take {S : List ℝ} (i : Fin S.length) {k : ℕ} (hi : i.val < k) :
    binOf ffChoice S i < FF (S.take k) := by
  apply lt_of_lt_of_le ?_ (ff_le_of_prefix (List.take_prefix_take_left (Nat.succ_le_of_lt hi)))
  rw [ff_take_succ_count]
  have hle : binOf ffChoice S i ≤ FF (S.take i.val) := List.findIdx_le_length
  split <;> omega

private noncomputable def packedSize (bins : List (List ℝ)) : ℝ :=
  ∑ j ∈ Finset.range bins.length, (bins.getD j []).sum

private theorem packedSize_placeAt (bins : List (List ℝ)) (j : ℕ) (a : ℝ) :
    packedSize (placeAt bins j a) = packedSize bins + a := by
  by_cases hj : j < bins.length
  · let updated := bins.mapIdx (fun i B => if i = j then B ++ [a] else B)
    have hlen : updated.length = bins.length := by simp [updated]
    have pointwise (i : ℕ) (hi : i ∈ Finset.range bins.length) :
        (updated.getD i []).sum = (bins.getD i []).sum + (if i = j then a else 0) := by
      have hin := Finset.mem_range.mp hi
      rw [getD_inside _ _ _ (by rwa [hlen]), getD_inside _ _ _ hin]
      simp only [updated, List.getElem_mapIdx]
      split <;> simp
    rw [placeAt, if_pos hj]
    change packedSize updated = _
    rw [packedSize, hlen, Finset.sum_congr rfl pointwise, Finset.sum_add_distrib,
      Finset.sum_ite_eq']
    simp [packedSize, hj]
  · simp only [placeAt, if_neg hj, packedSize, List.length_append, List.length_singleton,
      Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hin := Finset.mem_range.mp hi
      rw [getD_inside _ _ _ (by simp; omega), getD_inside _ _ _ hin,
        List.getElem_append_left hin]
    · rw [getD_inside _ _ _ (by simp)]
      simp

private theorem packedSize_fold (S : List ℝ) (bins : List (List ℝ)) :
    packedSize (S.foldl firstFitStep bins) = packedSize bins + S.sum := by
  induction S generalizing bins with
  | nil => simp
  | cons a S ih =>
    rw [List.foldl_cons, ih, firstFitStep, packedSize_placeAt, List.sum_cons, add_assoc]

/-- First Fit preserves the total input size. -/
theorem sum_final_bin_loads (S : List ℝ) :
    (∑ j ∈ Finset.range (FF S), ((run ffChoice S).getD j []).sum) = S.sum := by
  change packedSize (S.foldl firstFitStep []) = S.sum
  rw [packedSize_fold]
  simp [packedSize]

/-- The total size of a valid input is bounded by its optimal bin count. -/
theorem sum_le_optBins {S : List ℝ} (hS : IsList S) : S.sum ≤ (optBins S : ℝ) := by
  obtain ⟨assign, hfit⟩ := exists_optimal_assignment hS
  let bins := (List.finRange (optBins S)).map (assignmentBin assign)
  have each (a : ℝ) (ha : a ∈ bins.map List.sum) : a ≤ 1 := by
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hB
    rw [assignmentBin_sum]
    exact hfit j
  calc
    S.sum = bins.flatten.sum := (assignmentBins_flatten_perm assign).sum_eq.symm
    _ = (bins.map List.sum).sum := List.sum_flatten
    _ ≤ (bins.map List.sum).length • (1 : ℝ) := List.sum_le_card_nsmul _ _ each
    _ = optBins S := by simp [bins, nsmul_eq_mul]

private theorem step_bins_nonempty {bins : List (List ℝ)}
    (nonempty : ∀ B ∈ bins, B ≠ []) (a : ℝ) : ∀ B ∈ firstFitStep bins a, B ≠ [] := by
  intro B hB
  rw [firstFitStep, placeAt] at hB
  split at hB
  · obtain ⟨j, hj, hentry⟩ := List.mem_iff_getElem.mp hB
    rw [← hentry]
    simp only [List.getElem_mapIdx]
    split
    · simp
    · apply nonempty
      exact List.getElem_mem _
  · rcases List.mem_append.mp hB with hbin | hnew
    · exact nonempty B hbin
    · have : B = [a] := by simpa using hnew
      simp [this]

private theorem fold_bins_nonempty (items : List ℝ) (bins : List (List ℝ))
    (nonempty : ∀ B ∈ bins, B ≠ []) : ∀ B ∈ items.foldl firstFitStep bins, B ≠ [] := by
  induction items generalizing bins with
  | nil => exact nonempty
  | cons a items ih => exact ih _ (step_bins_nonempty nonempty a)

/-- Each bin opened by First Fit contains at least one item. -/
theorem final_bin_nonempty {S : List ℝ} {j : ℕ} (hj : j < FF S) :
    (run ffChoice S).getD j [] ≠ [] := by
  rw [getD_inside _ _ _ hj]
  exact fold_bins_nonempty S [] (by simp) _ (List.getElem_mem hj)

private theorem final_bin_sum_nonneg {S : List ℝ} (hS : IsList S) (j : ℕ) :
    0 ≤ ((run ffChoice S).getD j []).sum := by
  apply List.sum_nonneg
  intro a ha
  exact (hS a (FirstFitHistory.run_getD_subset S j ha)).1.le

/-- Johnson's Lemma 4.3 with `k = 0`. If a prefix uses at most the optimal bin count
for the whole input, and each remaining piece is at most `1 / n`, then the full
First Fit count is at most `opt + opt / n + 1`. -/
theorem ff_le_of_small_tail {S : List ℝ} (hS : IsList S) (k n : ℕ) (hn : 0 < n)
    (hprefix : FF (S.take k) ≤ optBins S)
    (htail : ∀ i : Fin S.length, k ≤ i.val → S.get i ≤ 1 / (n : ℝ)) :
    (FF S : ℝ) ≤ (optBins S : ℝ) + (optBins S : ℝ) / (n : ℝ) + 1 := by
  let b := optBins S
  let m := FF S
  change (m : ℝ) ≤ (b : ℝ) + (b : ℝ) / (n : ℝ) + 1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  by_cases short : m ≤ b + 1
  · have hcast : (m : ℝ) ≤ (b : ℝ) + 1 := by exact_mod_cast short
    have hdiv : (0 : ℝ) ≤ (b : ℝ) / (n : ℝ) := by positivity
    linarith only [hcast, hdiv]
  let last := m - 1
  let load := fun j => ((run ffChoice S).getD j []).sum
  have last_lt : last < m := by dsimp [last]; omega
  have hlast : b ≤ last := by dsimp [last]; omega
  have last_succ : last + 1 = m := by dsimp [last]; omega
  have last_pos : 0 < load last := List.sum_pos _ (fun a ha =>
    (hS a (FirstFitHistory.run_getD_subset S last ha)).1) (final_bin_nonempty last_lt)
  have after_prefix (i : Fin S.length) (hi : b ≤ binOf ffChoice S i) : k ≤ i.val := by
    by_contra! before
    exact (not_lt_of_ge (hprefix.trans hi)) (binOf_lt_ff_take i before)
  have bin_small (j : ℕ) (hj : b ≤ j) (a : ℝ) (ha : a ∈ (run ffChoice S).getD j []) :
      a ≤ 1 / (n : ℝ) := by
    obtain ⟨slot, hslot, hvalue⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨i, hi, hitem⟩ := FirstFitHistory.exists_greedySlot_of_lt_run S j slot hslot
    have atBin : binOf ffChoice S i = j := congrArg Prod.fst hi
    rw [List.getElem?_eq_getElem hslot, hvalue] at hitem
    rw [Option.some.inj hitem]
    exact htail i (after_prefix i (by rwa [atBin]))
  have total : ∑ j ∈ Finset.range m, load j ≤ (b : ℝ) := by
    change (∑ j ∈ Finset.range (FF S), ((run ffChoice S).getD j []).sum) ≤ (optBins S : ℝ)
    rw [sum_final_bin_loads]
    exact sum_le_optBins hS
  have total_split : (∑ j ∈ Finset.range b, load j) +
      (∑ j ∈ Finset.Ico b last, load j) + load last ≤ (b : ℝ) := by
    rw [Finset.sum_range_add_sum_Ico _ hlast, ← Finset.sum_range_succ, last_succ]
    exact total
  have bpos : 0 < b := by
    have last_le : load last ≤ ∑ j ∈ Finset.range m, load j := by
      apply Finset.single_le_sum (f := load) (fun j _ => final_bin_sum_nonneg hS j)
      exact Finset.mem_range.mpr last_lt
    exact_mod_cast (last_pos.trans_le (last_le.trans total))
  obtain ⟨light, hlight, lightest⟩ := Finset.exists_min_image (Finset.range b) load
    ⟨0, Finset.mem_range.mpr bpos⟩
  let d := 1 - load light
  have d_nonneg : 0 ≤ d := sub_nonneg.mpr (FirstFitHistory.run_getD_sum_le_one hS light)
  have early : (b : ℝ) * (1 - d) ≤ ∑ j ∈ Finset.range b, load j := by
    calc
      (b : ℝ) * (1 - d) = ∑ _j ∈ Finset.range b, (1 - d) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have h := lightest j hj
        dsimp [d]
        linarith only [h]
  obtain ⟨lastIndex, atLast, _⟩ := FirstFitHistory.exists_greedySlot_of_lt_run
    S last 0 (List.length_pos_iff.mpr (final_bin_nonempty last_lt))
  have lastBin : binOf ffChoice S lastIndex = last := congrArg Prod.fst atLast
  have lastSmall := htail lastIndex (after_prefix lastIndex (by rwa [lastBin]))
  have middle_bin (j : ℕ) (hj : j ∈ Finset.Ico b last) : (n : ℝ) * d ≤ load j := by
    obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ico.mp hj
    let bin := (run ffChoice S).getD j []
    have dense : 1 - 1 / (n : ℝ) < load j := by
      have reject := final_rejection hS lastIndex j (by rwa [lastBin])
      change 1 < load j + S.get lastIndex at reject
      linarith only [reject, lastSmall]
    have upper : load j ≤ (bin.length : ℝ) * (1 / (n : ℝ)) := by
      simpa only [nsmul_eq_mul] using
        List.sum_le_card_nsmul bin (1 / (n : ℝ)) (bin_small j hjlo)
    have enough : n ≤ bin.length := by
      by_contra! short_bin
      have hlen : (bin.length : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt short_bin)
      have scale := mul_le_mul_of_nonneg_right hlen (show 0 ≤ 1 / (n : ℝ) by positivity)
      have cancel : (n : ℝ) * (1 / (n : ℝ)) = 1 := by simp [one_div, hnR.ne']
      rw [cancel, add_mul, one_mul] at scale
      linarith only [scale, dense, upper]
    have lower : (bin.length : ℝ) * d ≤ load j := by
      rw [← nsmul_eq_mul]
      apply List.card_nsmul_le_sum
      intro a ha
      obtain ⟨slot, hslot, value⟩ := List.mem_iff_getElem.mp ha
      obtain ⟨i, hi, hitem⟩ := FirstFitHistory.exists_greedySlot_of_lt_run S j slot hslot
      have place : binOf ffChoice S i = j := congrArg Prod.fst hi
      have before : light < binOf ffChoice S i := by
        rw [place]
        exact (Finset.mem_range.mp hlight).trans_le hjlo
      have rejects := final_rejection hS i light before
      change 1 < load light + S.get i at rejects
      rw [List.getElem?_eq_getElem hslot, value] at hitem
      rw [Option.some.inj hitem]
      exact (sub_lt_iff_lt_add'.mpr rejects).le
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast enough) d_nonneg).trans lower
  have middle : ((last - b : ℕ) : ℝ) * ((n : ℝ) * d) ≤ ∑ j ∈ Finset.Ico b last, load j := by
    calc
      ((last - b : ℕ) : ℝ) * ((n : ℝ) * d) = ∑ _j ∈ Finset.Ico b last, (n : ℝ) * d := by
        simp [nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum middle_bin
  have balance : (b : ℝ) * (1 - d) + ((last - b : ℕ) : ℝ) * ((n : ℝ) * d) + load last ≤ b :=
    (add_le_add_left (add_le_add early middle) _).trans total_split
  have d_pos : 0 < d := by
    by_contra! hnonpos
    rw [le_antisymm hnonpos d_nonneg] at balance
    simp at balance
    linarith only [balance, last_pos]
  have scaled : ((last - b : ℕ) : ℝ) * (n : ℝ) * d ≤ (b : ℝ) * d := by
    nlinarith only [balance, last_pos]
  have count := (mul_le_mul_iff_left₀ d_pos).mp scaled
  have last_count : (last : ℝ) - (b : ℝ) ≤ (b : ℝ) / (n : ℝ) := by
    apply (le_div_iff₀ hnR).mpr
    simpa only [Nat.cast_sub hlast] using count
  have last_cast : (last : ℝ) + 1 = (m : ℝ) := by exact_mod_cast last_succ
  linarith only [last_count, last_cast]

end BinPacking.Decreasing

end

/- small-only/ReductionThree.lean -/
section

set_option autoImplicit false

namespace BinPacking.Decreasing

/-- Processing a segment leaves the bin count unchanged if all its pieces are
placed in bins present before the segment began. -/
theorem ff_take_eq_of_existing_bins (S : List ℝ) (start finish : ℕ)
    (hstart : start ≤ finish) (hfinish : finish ≤ S.length)
    (hplaced : ∀ i : Fin S.length, start ≤ i.val → i.val < finish →
      binOf ffChoice S i < FF (S.take start)) :
    FF (S.take finish) = FF (S.take start) := by
  induction finish, hstart using Nat.le_induction with
  | base => rfl
  | succ finish hstart ih =>
    have earlier := ih (Nat.le_of_succ_le hfinish)
      (fun i hlo hhi => hplaced i hlo (hhi.trans (Nat.lt_succ_self finish)))
    let i : Fin S.length := ⟨finish, Nat.lt_of_succ_le hfinish⟩
    have hi : binOf ffChoice S i < FF (S.take i.val) := by
      change binOf ffChoice S i < FF (S.take finish)
      rw [earlier]
      exact hplaced i hstart (Nat.lt_succ_self finish)
    change FF (S.take (i.val + 1)) = _
    rw [ff_take_succ_count, if_pos hi]
    exact earlier

/-- The estimate in Johnson's Reduction 3. A prefix ending with the B-pieces
uses at most the optimal count. All subsequent C- and D-pieces go into the
initial A-bins, so the number of bins grows only when the E-pieces begin. -/
theorem ff_le_reduction_three {S : List ℝ} (hS : IsList S) (ab abcd aBins : ℕ)
    (hab : ab ≤ abcd) (habcd : abcd ≤ S.length)
    (haBins : aBins ≤ FF (S.take ab)) (hAB : FF (S.take ab) ≤ optBins S)
    (hCD : ∀ i : Fin S.length, ab ≤ i.val → i.val < abcd → binOf ffChoice S i < aBins)
    (hE : ∀ i : Fin S.length, abcd ≤ i.val → S.get i ≤ 1 / 5) :
    (FF S : ℝ) ≤ (6 / 5 : ℝ) * (optBins S : ℝ) + 1 := by
  have count := ff_take_eq_of_existing_bins S ab abcd hab habcd
    (fun i hlo hhi => (hCD i hlo hhi).trans_le haBins)
  have bound := ff_le_of_small_tail hS abcd 5 (by decide) (count.symm ▸ hAB)
    (by simpa only [Nat.cast_ofNat] using hE)
  norm_num at bound
  linarith only [bound]

end BinPacking.Decreasing

end

/- small-only/DescendingLarge.lean -/
section

set_option autoImplicit false

namespace BinPacking.Decreasing

open FirstFitHistory

noncomputable section

private abbrev largePrefix (S : List ℝ) : List ℝ :=
  S.filter (fun a => decide ((1 / 2 : ℝ) < a))

private theorem starts_large {S : List ℝ} (hsort : S.Pairwise (fun a b => b ≤ a)) :
    largePrefix S <+: S :=
  ⟨S.filter (fun a => !decide ((1 / 2 : ℝ) < a)), (split_large_of_sorted hsort).symm⟩

private theorem prefix_allLarge (S : List ℝ) : ∀ a ∈ largePrefix S, (1 / 2 : ℝ) < a :=
  fun _ ha => of_decide_eq_true (List.mem_filter.mp ha).2

private def largeAnchor {S : List ℝ} (j : Fin (largePrefix S).length) : Fin S.length :=
  ⟨j, j.isLt.trans_le (List.length_filter_le _ _)⟩

private def smallPositions (S : List ℝ) : Finset (Fin S.length) :=
  Finset.univ.filter (fun i => (largePrefix S).length ≤ i.val)

private def smallMatches (S : List ℝ) (label : Fin S.length → ℕ) : Finset (Fin S.length) :=
  (smallPositions S).filter (fun i => label i < (largePrefix S).length)

private theorem mem_smallMatches {S : List ℝ} {label : Fin S.length → ℕ} {i : Fin S.length} :
    i ∈ smallMatches S label ↔ (largePrefix S).length ≤ i.val ∧ label i < (largePrefix S).length := by
  simp [smallMatches, smallPositions]

private theorem card_actual_matches {S : List ℝ} (hS : IsList S)
    (hsort : S.Pairwise (fun a b => b ≤ a)) (hthird : ∀ i : Fin S.length, (1 / 3 : ℝ) < S.get i)
    {b : ℕ} (assign : Fin S.length → Fin b)
    (hfit : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), S.get i ≤ 1)
    (halign : ∀ i, (1 / 2 : ℝ) < S.get i → (assign i).val = i.val) :
    (smallMatches S (fun i => (assign i).val)).card ≤ (smallMatches S (binOf ffChoice S)).card := by
  have starts := starts_large hsort
  have anchor_large (j : Fin (largePrefix S).length) : (1 / 2 : ℝ) < S.get (largeAnchor j) :=
    (largeItem_iff_lt_filter_length hsort (largeAnchor j)).mpr j.isLt
  have anchor_label (j : Fin (largePrefix S).length) : (assign (largeAnchor j)).val = j.val :=
    halign _ (anchor_large j)
  apply card_optimal_matches_le_greedy_matches _ _ (fun i => (assign i).val) (binOf ffChoice S)
  · intro p hp q hq same
    obtain ⟨hpAfter, hpABin⟩ := mem_smallMatches.mp (Finset.mem_coe.mp hp)
    obtain ⟨hqAfter, _⟩ := mem_smallMatches.mp (Finset.mem_coe.mp hq)
    let j : Fin (largePrefix S).length := ⟨(assign p).val, hpABin⟩
    have pLabel : assign p = assign (largeAnchor j) := Fin.ext (anchor_label j).symm
    have qLabel : assign q = assign (largeAnchor j) := (Fin.ext same).symm.trans pLabel
    have beforeP : largeAnchor j < p := j.isLt.trans_le hpAfter
    have beforeQ : largeAnchor j < q := j.isLt.trans_le hqAfter
    by_contra different
    have sum := assignment_triple_sum_le_one hS assign hfit (largeAnchor j) p q
      (ne_of_lt beforeP) (ne_of_lt beforeQ) different pLabel qLabel
    linarith only [sum, anchor_large j, hthird p, hthird q]
  · intro x hx notGreedy p hp hpx
    obtain ⟨hxAfter, _⟩ := mem_smallMatches.mp hx
    obtain ⟨hpAfter, hpABin⟩ := mem_smallMatches.mp hp
    have xOutside : (largePrefix S).length ≤ binOf ffChoice S x :=
      le_of_not_gt (fun h => notGreedy (mem_smallMatches.mpr ⟨hxAfter, h⟩))
    let j : Fin (largePrefix S).length := ⟨(assign p).val, hpABin⟩
    have pLabel : assign p = assign (largeAnchor j) := Fin.ext (anchor_label j).symm
    have beforeP : largeAnchor j < p := j.isLt.trans_le hpAfter
    have pFits := assignment_pair_sum_le_one hS assign hfit (largeAnchor j) p
      (ne_of_lt beforeP) pLabel
    have xSmaller : S.get x ≤ S.get p := by
      rcases lt_or_eq_of_le hpx with hlt | rfl
      · exact hsort.rel_get_of_lt hlt
      · rfl
    have anchorEq : S.get (largeAnchor j) = (largePrefix S).get j :=
      (starts.getElem j.isLt).symm
    have xFits : (largePrefix S).get j + S.get x ≤ 1 := by
      rw [← anchorEq]
      exact (add_le_add (le_refl _) xSmaller).trans pFits
    have rejected := earlier_rejection x j.val (j.isLt.trans_le xOutside)
    have anchorPresent := large_anchor_prefix starts (prefix_allLarge S) hxAfter j.isLt
    have second : 1 < (contents S x.val j.val).length := by
      by_contra! onlyAnchor
      have singleton := (anchorPresent.eq_of_length_le (by simpa using onlyAnchor)).symm
      rw [singleton, List.sum_singleton] at rejected
      exact (not_lt_of_ge xFits) rejected
    obtain ⟨q, hqBefore, hqSlot, _⟩ := exists_greedySlot_of_lt_contents S x.val j.val 1 x.isLt.le second
    have qAfter : (largePrefix S).length ≤ q.val := by
      by_contra! qLarge
      have zero := greedySlot_of_large starts (prefix_allLarge S) q qLarge
      rw [hqSlot] at zero
      have impossible : 1 = 0 := congrArg Prod.snd zero
      omega
    have qLabel : binOf ffChoice S q = j.val := congrArg Prod.fst hqSlot
    exact ⟨q, mem_smallMatches.mpr ⟨qAfter, by rw [qLabel]; exact j.isLt⟩, hqBefore, qLabel⟩

private def outsidePositions (S : List ℝ) (label : Fin S.length → ℕ) : Finset (Fin S.length) :=
  Finset.univ.filter (fun i => (largePrefix S).length ≤ label i)

private theorem mem_outsidePositions {S : List ℝ} {label : Fin S.length → ℕ} {i : Fin S.length} :
    i ∈ outsidePositions S label ↔ (largePrefix S).length ≤ label i := by
  simp [outsidePositions]

private theorem card_matches_add_card_outside {S : List ℝ} (label : Fin S.length → ℕ)
    (aligned : ∀ i, i.val < (largePrefix S).length → label i = i.val) :
    (smallMatches S label).card + (outsidePositions S label).card = (smallPositions S).card := by
  have outside_eq : outsidePositions S label =
      (smallPositions S).filter (fun i => ¬label i < (largePrefix S).length) := by
    ext i
    simp only [mem_outsidePositions, smallPositions, Finset.mem_filter, Finset.mem_univ,
      true_and, not_lt]
    exact ⟨fun h => ⟨le_of_not_gt (fun hi => (not_lt_of_ge h) ((aligned i hi).symm ▸ hi)), h⟩,
      And.right⟩
  rw [outside_eq]
  exact Finset.card_filter_add_card_filter_not _

private theorem card_optimal_outside_le {S : List ℝ} (hthird : ∀ a ∈ S, (1 / 3 : ℝ) < a)
    {b : ℕ} (assign : Fin S.length → Fin b)
    (hfit : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), S.get i ≤ 1) :
    (outsidePositions S (fun i => (assign i).val)).card ≤ 2 * (b - (largePrefix S).length) := by
  let slots := (Finset.Ico (largePrefix S).length b) ×ˢ (Finset.range 2)
  have range : Set.MapsTo (optimalPosition assign) ↑(outsidePositions S (fun i => (assign i).val))
      ↑slots := by
    intro i hi
    apply Finset.mem_coe.mpr
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨mem_outsidePositions.mp (Finset.mem_coe.mp hi), (assign i).isLt⟩,
      Finset.mem_range.mpr ?_⟩
    let bin := assignmentBin assign (assign i)
    have upper : bin.sum ≤ 1 := by rw [assignmentBin_sum]; exact hfit (assign i)
    have count : bin.length ≤ 2 := by
      by_contra! hlen
      have minsize (a : ℝ) (ha : a ∈ bin) : (1 / 3 : ℝ) < a :=
        hthird _ ((assignmentBin_sublist assign _).subset ha)
      have lower := List.sum_lt_sum_of_ne_nil (List.ne_nil_of_length_pos (by omega : 0 < bin.length))
        (fun _ : ℝ => (1 / 3 : ℝ)) id (fun a ha => minsize a ha)
      simp only [List.map_const', List.sum_replicate, List.map_id, nsmul_eq_mul] at lower
      have length_cast : (3 : ℝ) ≤ (bin.length : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hlen)
      linarith only [lower, upper, length_cast]
    exact (assignmentSlot_lt assign i).trans_le (by simpa [bin, assignmentBin] using count)
  calc
    _ ≤ slots.card := Finset.card_le_card_of_injOn _ range (optimalPosition_injective assign).injOn
    _ = _ := by simp [slots, Nat.mul_comm]

private theorem card_greedy_outside_ge {S : List ℝ} (hS : IsList S)
    (hsort : S.Pairwise (fun a b => b ≤ a)) (many : (largePrefix S).length < FF S) :
    2 * (FF S - (largePrefix S).length) ≤
      (outsidePositions S (binOf ffChoice S)).card + 1 := by
  let a := (largePrefix S).length
  let last := FF S - 1
  have atLeast : a ≤ last := by dsimp [last, a]; omega
  have last_lt : last < FF S := by dsimp [last]; omega
  have hsmall (i : Fin S.length) (hbin : a ≤ binOf ffChoice S i) : S.get i ≤ 1 / 2 := by
    by_contra! hlarge
    have early := (largeItem_iff_lt_filter_length hsort i).mp hlarge
    have label : binOf ffChoice S i = i.val := congrArg Prod.fst
      (greedySlot_of_large (starts_large hsort) (prefix_allLarge S) i early)
    rw [label] at hbin
    exact (not_lt_of_ge hbin) early
  have last_nonempty := List.length_pos_iff.mpr (final_bin_nonempty last_lt)
  obtain ⟨lastIndex, hlastSlot, _⟩ := exists_greedySlot_of_lt_run S last 0 last_nonempty
  have lastLabel : binOf ffChoice S lastIndex = last := congrArg Prod.fst hlastSlot
  have lastSmall := hsmall lastIndex (by rwa [lastLabel])
  let slots := (Finset.Ico a last) ×ˢ Finset.range 2
  have slots_present : slots ⊆ (outsidePositions S (binOf ffChoice S)).image (greedySlot S) := by
    rintro ⟨j, k⟩ hk
    obtain ⟨hj, hslot⟩ := Finset.mem_product.mp hk
    obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ico.mp hj
    let bin := (run ffChoice S).getD j []
    have load : (1 / 2 : ℝ) < bin.sum := by
      have rejected := final_rejection hS lastIndex j (by rwa [lastLabel])
      change 1 < bin.sum + S.get lastIndex at rejected
      linarith only [rejected, lastSmall]
    have each (y : ℝ) (hy : y ∈ bin) : y ≤ 1 / 2 := by
      obtain ⟨t, ht, hvalue⟩ := List.mem_iff_getElem.mp hy
      obtain ⟨i, hplace, hitem⟩ := exists_greedySlot_of_lt_run S j t ht
      have label : binOf ffChoice S i = j := congrArg Prod.fst hplace
      rw [List.getElem?_eq_getElem ht, hvalue] at hitem
      rw [Option.some.inj hitem]
      exact hsmall i (by rwa [label])
    have enough : 2 ≤ bin.length := by
      by_contra! hlen
      have upper := List.sum_le_card_nsmul bin (1 / 2 : ℝ) each
      rw [nsmul_eq_mul] at upper
      have short : (bin.length : ℝ) ≤ 1 := by exact_mod_cast (Nat.le_of_lt_succ hlen)
      linarith only [load, short, upper]
    obtain ⟨i, hplace, _⟩ := exists_greedySlot_of_lt_run S j k ((Finset.mem_range.mp hslot).trans_le enough)
    have label : binOf ffChoice S i = j := congrArg Prod.fst hplace
    exact Finset.mem_image.mpr ⟨i, mem_outsidePositions.mpr (by rwa [label]), hplace⟩
  have outside_card : (insert (last, 0) slots).card ≤ (outsidePositions S (binOf ffChoice S)).card := by
    refine (Finset.card_le_card ?_).trans (Finset.card_image_le (f := greedySlot S))
    intro slot hslot
    rcases Finset.mem_insert.mp hslot with rfl | hslot
    · exact Finset.mem_image.mpr
        ⟨lastIndex, mem_outsidePositions.mpr (by rwa [lastLabel]), hlastSlot⟩
    · exact slots_present hslot
  have lastNew : (last, 0) ∉ slots := by simp [slots]
  rw [Finset.card_insert_of_notMem lastNew] at outside_card
  have beforeCount : slots.card = 2 * (last - a) := by simp [slots, Nat.mul_comm]
  rw [beforeCount] at outside_card
  have : last + 1 = FF S := by dsimp [last]; omega
  omega

/-- Johnson's Lemma 4.5. Decreasing First Fit is optimal when all items exceed one third. -/
theorem ff_le_optBins_of_one_third {S : List ℝ} (hS : IsList S)
    (hsort : S.Pairwise (fun a b => b ≤ a)) (ht : ∀ a ∈ S, (1 / 3 : ℝ) < a) :
    FF S ≤ optBins S := by
  obtain ⟨assign, hfit, aligned⟩ := exists_optimal_assignment_aligned hS hsort
  let a := (largePrefix S).length
  have opt_aligned (i : Fin S.length) (hi : i.val < a) : (assign i).val = i.val :=
    aligned i ((largeItem_iff_lt_filter_length hsort i).mpr hi)
  have greedy_aligned (i : Fin S.length) (hi : i.val < a) : binOf ffChoice S i = i.val :=
    congrArg Prod.fst (greedySlot_of_large (starts_large hsort) (prefix_allLarge S) i hi)
  have optLarge : a ≤ optBins S := by
    by_contra! tooFew
    let i : Fin S.length := ⟨optBins S, tooFew.trans_le (List.length_filter_le _ _)⟩
    have outOfBounds := (assign i).isLt
    rw [opt_aligned i tooFew] at outOfBounds
    exact (lt_irrefl (optBins S)) outOfBounds
  by_cases enough : FF S ≤ a
  · exact enough.trans optLarge
  have matchCount := card_actual_matches hS hsort (fun i => ht _ (List.get_mem S i)) assign hfit aligned
  have optCount := card_matches_add_card_outside (fun i => (assign i).val) opt_aligned
  have greedyCount := card_matches_add_card_outside (binOf ffChoice S) greedy_aligned
  have hgreedy := card_greedy_outside_ge hS hsort (lt_of_not_ge enough)
  have hopt := card_optimal_outside_le ht assign hfit
  omega

private theorem size_gt_iff_before_cut {S : List ℝ} (hsort : S.Pairwise (fun a b => b ≤ a))
    (size : ℝ) (i : Fin S.length) :
    size < S.get i ↔ i.val < S.findIdx (fun a => decide (a ≤ size)) := by
  constructor
  · intro hsize
    by_contra! cutBefore
    let cut := S.findIdx (fun a => decide (a ≤ size))
    let j : Fin S.length := ⟨cut, cutBefore.trans_lt i.isLt⟩
    have atCut : S[cut]? = some (S.get j) := List.getElem?_eq_getElem j.isLt
    have small : S.get j ≤ size := of_decide_eq_true
      (List.findIdx_of_getElem?_eq_some (p := fun a : ℝ => decide (a ≤ size)) atCut)
    have ordered : S.get i ≤ S.get j := by
      rcases lt_or_eq_of_le (show j ≤ i from cutBefore) with before | same
      · exact hsort.rel_get_of_lt before
      · rw [same]
    exact (not_lt_of_ge (ordered.trans small)) hsize
  · intro before
    simpa using List.not_of_lt_findIdx before

/-- Johnson's Reduction 3 in the First Fit model. If a descending input has
no C- or D-piece in a bin outside the initial A-bins, First Fit uses at most
`(6/5) * opt + 1` bins. -/
theorem ff_le_of_no_cd_outside {S : List ℝ} (hS : IsList S)
    (hsort : S.Pairwise (fun a b => b ≤ a))
    (hCD : ∀ i : Fin S.length, (1 / 5 : ℝ) < S.get i → S.get i ≤ 1 / 3 →
      binOf ffChoice S i < (S.filter (fun a => decide ((1 / 2 : ℝ) < a))).length) :
    (FF S : ℝ) ≤ (6 / 5 : ℝ) * (optBins S : ℝ) + 1 := by
  let ab := S.findIdx (fun a => decide (a ≤ (1 / 3 : ℝ)))
  let abcd := S.findIdx (fun a => decide (a ≤ (1 / 5 : ℝ)))
  have abLen : ab ≤ S.length := List.findIdx_le_length
  have abcdLen : abcd ≤ S.length := List.findIdx_le_length
  have hab : ab ≤ abcd := by
    by_contra! cuts
    let i : Fin S.length := ⟨abcd, cuts.trans_le abLen⟩
    have large := (size_gt_iff_before_cut hsort (1 / 3) i).mpr cuts
    have small : S.get i ≤ 1 / 5 :=
      le_of_not_gt (fun h => (lt_irrefl abcd) ((size_gt_iff_before_cut hsort (1 / 5) i).mp h))
    linarith only [large, small]
  have prefixCount : FF (S.take ab) ≤ optBins S := by
    apply le_trans ?_ (optBins_take_le hS ab)
    apply ff_le_optBins_of_one_third
    · exact fun a ha => hS a (List.mem_of_mem_take ha)
    · exact hsort.sublist (List.take_sublist _ _)
    · intro a ha
      obtain ⟨rank, hrank, hget⟩ := List.mem_iff_getElem.mp ha
      have before : rank < ab := by simpa only [List.length_take_of_le abLen] using hrank
      let i : Fin S.length := ⟨rank, before.trans_le abLen⟩
      have item : S.get i = a := by simpa only [i, List.get_eq_getElem, List.getElem_take] using hget
      rw [← item]
      exact (size_gt_iff_before_cut hsort (1 / 3) i).mpr before
  have aCount : (largePrefix S).length ≤ FF (S.take ab) := by
    by_contra! few
    let i : Fin S.length := ⟨FF (S.take ab), few.trans_le (List.length_filter_le _ _)⟩
    have item := (largeItem_iff_lt_filter_length hsort i).mpr few
    have before : i.val < ab := (size_gt_iff_before_cut hsort (1 / 3) i).mp (by linarith only [item])
    have place := binOf_lt_ff_take i before
    have label : binOf ffChoice S i = i.val := congrArg Prod.fst
      (greedySlot_of_large (starts_large hsort) (prefix_allLarge S) i few)
    rw [label] at place
    exact (lt_irrefl _) place
  apply ff_le_reduction_three hS ab abcd (largePrefix S).length hab abcdLen aCount prefixCount
  · intro i above below
    exact hCD i ((size_gt_iff_before_cut hsort (1 / 5) i).mpr below)
      (le_of_not_gt (fun h => (not_lt_of_ge above) ((size_gt_iff_before_cut hsort (1 / 3) i).mp h)))
  · intro i above
    exact le_of_not_gt (fun h => (not_lt_of_ge above) ((size_gt_iff_before_cut hsort (1 / 5) i).mp h))

/-- Every descending counterexample has a C- or D-piece outside the initial A-bins. -/
theorem exists_cd_outside_of_violation {S : List ℝ} (hS : IsList S)
    (hsort : S.Pairwise (fun a b => b ≤ a))
    (violation : (11 / 9 : ℝ) * (optBins S : ℝ) + 4 < (FF S : ℝ)) :
    ∃ i : Fin S.length, (1 / 5 : ℝ) < S.get i ∧ S.get i ≤ 1 / 3 ∧
      (S.filter (fun a => decide ((1 / 2 : ℝ) < a))).length ≤ binOf ffChoice S i := by
  by_contra! excluded
  have estimate := ff_le_of_no_cd_outside hS hsort (fun i hlo hhi => excluded i hlo hhi)
  linarith only [estimate, violation, Nat.cast_nonneg (α := ℝ) (optBins S)]

end

end BinPacking.Decreasing

end

/- LargeBinBudget.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

open PieceChains

noncomputable section

variable {S : List ℝ} (p : AlignedPacking S)

private theorem responsible_size_le_quarter_of_anchor (j : Fin (largePrefixItems S).length)
    (item : ResidualPosition S) (assigned : p.responsibilityBin item = p.anchorBin j) :
    residualSize item ≤ 1 / 4 := by
  have owner := (p.responsibilityBin_eq_anchorBin_iff item j).mp assigned
  obtain ⟨head, _, path, direct | ⟨bin, atThird, _⟩⟩ := p.owner_head_cases item
  · exact ((Nat.not_lt_of_ge head.property)
      ((direct.2.symm.trans owner).symm ▸ j.isLt)).elim
  · have inside : isLargeBin S (p.smallOptimalSlot head).1 :=
      (congrArg Prod.fst atThird).symm ▸ bin.property.1
    exact (p.terminal_size_le_max_head_quarter (Nat.le_of_not_gt item.property) path).trans
      (max_le (p.optimal_third_lt_quarter head inside (congrArg Prod.snd atThird)).le le_rfl)

/-- Claim 5.9.21 after bounding the number of indirect terms routed to each anchor. -/
theorem large_bin_budget_of_count (j : Fin (largePrefixItems S).length)
    (count : (p.responsiblePositions (p.anchorBin j)).length ≤ 3)
    (countWithoutB : ¬p.optimalHasB j.val → (p.responsiblePositions (p.anchorBin j)).length ≤ 2) :
    W (p.responsiblePieces (p.anchorBin j)) + p.credit (p.anchorBin j) ≤
      (11 / 9 : ℝ) * p.credit (p.anchorBin j) := by
  classical
  let pieces := p.responsiblePieces (p.anchorBin j)
  let baseline := anchorCredit
    (IsDeficit smallGreedySlot p.smallOptimalSlot (isLargeBin S)) p.optimalHasB j.val
  let extra := secondCredit p.thirdSlotRoute (p.anchorBin j)
  have first : p.credit (p.anchorBin j) = (baseline + (pieces.length : ℝ)) + extra := by
    unfold credit firstCredit
    rw [p.routed_anchorCredit_eq j, p.routed_indirectCredit_eq_count_of_anchor j]
    simp only [pieces, responsiblePieces, List.length_map, baseline, extra]
  have pieceBound (x : ℝ) (hx : x ∈ pieces) : 0 < x ∧ x ≤ 1 / 4 := by
    obtain ⟨item, itemMem, rfl⟩ := List.mem_map.mp hx
    exact ⟨(p.valid _ (List.get_mem S item.val.val)).1,
      p.responsible_size_le_quarter_of_anchor j item
        ((p.mem_responsiblePositions_iff _ item).mp itemMem)⟩
  have nondeficit (nonempty : pieces.length ≠ 0) :
      ¬IsDeficit smallGreedySlot p.smallOptimalSlot (isLargeBin S) j.val := by
    have nonemptyPositions : p.responsiblePositions (p.anchorBin j) ≠ [] := by
      intro empty
      exact nonempty (by simp [pieces, responsiblePieces, empty])
    obtain ⟨item, mem⟩ := List.exists_mem_of_ne_nil _ nonemptyPositions
    have assigned := (p.mem_responsiblePositions_iff _ item).mp mem
    exact (p.owner_anchor_of_label item j ((congrArg Fin.val assigned).trans
      (p.anchor_bin_index j))).2
  have extraNonneg : 0 ≤ extra := by
    unfold extra secondCredit routedCredit
    exact Finset.sum_nonneg fun _ _ => by norm_num
  have baselineNonneg : 0 ≤ baseline := by
    unfold baseline anchorCredit
    split_ifs <;> norm_num
  have lengthCap : pieces.length ≤ 3 := by simpa [pieces, responsiblePieces] using count
  have lengthCases : pieces.length = 0 ∨ pieces.length = 1 ∨ pieces.length = 2 ∨ pieces.length = 3 :=
    by omega
  rw [first]
  apply large_bin_responsibility_bound pieces (baseline + (pieces.length : ℝ)) extra pieceBound extraNonneg
  rcases lengthCases with length | length | length | length
  · exact .inl ⟨length, by simp [length, baselineNonneg]⟩
  · refine .inr (.inl ⟨length, ?_⟩)
    simp only [baseline, anchorCredit, if_neg (nondeficit (by omega)), length]
    split_ifs <;> norm_num
  · refine .inr (.inr (.inl ⟨length, ?_⟩))
    simp only [baseline, anchorCredit, if_neg (nondeficit (by omega)), length]
    split_ifs <;> norm_num
  · refine .inr (.inr (.inr ⟨length, ?_⟩))
    have hasB : p.optimalHasB j.val := by
      by_contra noB
      have three : (p.responsiblePositions (p.anchorBin j)).length = 3 := by
        simpa [pieces, responsiblePieces] using length
      have smaller := countWithoutB noB
      omega
    norm_num [baseline, anchorCredit, nondeficit (by omega), length, hasB]

theorem large_bin_budget (bin : Fin (optBins S)) (hasAnchor : bin ∈ binsWithLargeItems p.assign) :
    W (p.responsiblePieces bin) + p.credit bin ≤ (11 / 9 : ℝ) * p.credit bin := by
  classical
  have inside := (mem_aligned_binsWithLargeItems_iff_lt_count p.sorted p.assign p.aligned bin).mp hasAnchor
  let j : Fin (largePrefixItems S).length := ⟨bin.val, inside⟩
  have same : p.anchorBin j = bin := Fin.ext (p.anchor_bin_index j)
  rw [← same]
  have cap := (p.length_responsiblePositions_anchor_le_ownedDeficits j).trans
    (p.card_ownedDeficits_large_le j)
  apply p.large_bin_budget_of_count j
  · split_ifs at cap <;> omega
  · intro noB
    simpa only [if_neg noB] using cap

end

end BinPacking.Decreasing.AlignedPacking

end

/- NonLargeBudgetReduction.lean -/
section

namespace BinPacking.Decreasing

/-- Johnson's reductions leave the per-bin inequalities in non-large optimal
bins for sorted packings with a C- or D-piece in the residual input. -/
theorem ffd_le_of_nonLarge_bin_budget
    (binBudget : ∀ (S : List ℝ) (p : AlignedPacking S),
      (∃ r : AlignedPacking.ResidualPosition S, (1 / 5 : ℝ) < AlignedPacking.residualSize r ∧
        AlignedPacking.residualSize r ≤ 1 / 3) →
      ∀ j : Fin (optBins S), j ∉ binsWithLargeItems p.assign →
        W (p.responsiblePieces j) + p.credit j ≤ (11 / 9 : ℝ) * (1 + p.credit j))
    (L : List ℝ) (valid : IsList L) (threshold : ∀ a ∈ L, (2 / 11 : ℝ) < a) :
    (FFD L : ℝ) ≤ (11 / 9 : ℝ) * (optBins L : ℝ) + 4 := by
  by_contra! violation
  obtain ⟨S, ⟨p⟩, violates⟩ := exists_aligned_counterexample valid threshold violation
  obtain ⟨i, lower, upper, outside⟩ := exists_cd_outside_of_violation p.valid p.sorted violates
  have residualCD : ∃ r : AlignedPacking.ResidualPosition S,
      (1 / 5 : ℝ) < AlignedPacking.residualSize r ∧ AlignedPacking.residualSize r ≤ 1 / 3 :=
    ⟨p.residualPositionOfIndex i outside, lower, upper⟩
  have bounded := ffd_le_of_optimal_responsibilities S p.valid p.threshold p.assign p.fits
    p.responsiblePieces p.credit p.residualItems_perm_responsiblePieces (by
      intro j
      by_cases hasAnchor : j ∈ binsWithLargeItems p.assign
      · simpa only [if_pos hasAnchor, zero_add] using p.large_bin_budget j hasAnchor
      · simpa only [if_neg hasAnchor] using binBudget S p residualCD j hasAnchor) p.sum_credit_le
  rw [FFD, sortDesc_eq_self_of_sorted p.sorted] at bounded
  exact (not_lt_of_ge bounded) violates

end BinPacking.Decreasing

end

/- assembly/ExceptionalBudgets.lean -/
section

namespace BinPacking.Decreasing

namespace ResponsibilityWeights

theorem caseII_cost_le_of_charge {r : ResponsibilityWeights} {kind : SmallPieceClass}
    (h : r.Admissible false kind) (hcharge : 2 / 3 ≤ r.extra) :
    r.weightedCost 1 ≤ singletonAllowance false kind - (4 / 27 - 1 / 20) := by
  have hscore {d : ℝ} {n : ℕ} (hd : r.direct ≤ d) (hn : r.count ≤ n) :
      r.weightedCost 1 ≤ d + (n : ℝ) / 36 - 2 / 9 * (2 / 3) := by
    simpa only [weightedCost, credit, one_mul] using
      responsibility_cost_le 1 r.direct r.indirect r.extra d (2 / 3) r.count n
        zero_le_one hd h.indirect_le hn hcharge
  cases kind
  case B =>
    by_cases hzero : r.count = 0
    · have hc := hscore (d := 1 / 2)
        (by simpa [directWeightLimit, hzero] using h.direct_le) hzero.le
      norm_num [singletonAllowance] at hc ⊢
      linarith
    · have hc := hscore (d := 1 / 4)
        (by simpa [directWeightLimit, hzero] using h.direct_le)
        (n := 3) (by simpa [indirectCountLimit] using h.count_le)
      norm_num [singletonAllowance] at hc ⊢
      linarith
  case C | D =>
    have hc := hscore (d := 1 / 4) h.direct_le
      (n := 1) (by simpa [indirectCountLimit] using h.count_le)
    norm_num [singletonAllowance] at hc ⊢
    linarith
  case E =>
    have hc := hscore (d := 1 / 4) h.direct_le
      (n := 0) (by simpa [indirectCountLimit] using h.count_le)
    norm_num [singletonAllowance] at hc ⊢
    linarith

theorem caseII_D_cost_le_of_E_indirect {r : ResponsibilityWeights}
    (h : r.Admissible false .D) (hindirect : r.indirect ≤ (r.count : ℝ) / 5) :
    r.weightedCost 1 ≤ 1 / 4 := by
  have hdirect : r.direct ≤ 1 / 4 := h.direct_le
  unfold weightedCost credit
  linarith [h.extra_nonneg, Nat.cast_nonneg (α := ℝ) r.count]

theorem caseII_E_cost_le_of_no_direct {r : ResponsibilityWeights}
    (h : r.Admissible false .E) (habsent : r.direct = 0) :
    r.weightedCost 1 ≤ 0 := by
  have hcount : r.count = 0 := by simpa [indirectCountLimit] using h.count_le
  have hindirect := h.indirect_le
  unfold weightedCost credit
  rw [hcount] at hindirect
  rw [habsent, hcount]
  norm_num at hindirect ⊢
  linarith [h.extra_nonneg]

theorem cost_le_of_demoted_B {r : ResponsibilityWeights} {hasC : Bool}
    (h : r.Admissible hasC .B) (hdirect : r.direct ≤ demotedWeightLimit hasC .B) :
    r.weightedCost 1 ≤ if hasC then 7 / 18 else 1 / 3 := by
  have hc := responsibility_cost_le 1 r.direct r.indirect r.extra
    (demotedWeightLimit hasC .B) 0 r.count (indirectCountLimit hasC .B)
    zero_le_one hdirect h.indirect_le h.count_le h.extra_nonneg
  cases hasC <;>
    norm_num [credit, weightedCost, demotedWeightLimit, indirectCountLimit] at hc ⊢ <;>
    linarith

end ResponsibilityWeights

private theorem sum_le_of_saved_cost {n : ℕ}
    (hasC : Bool) (kind : Fin n → SmallPieceClass) (r : Fin n → ResponsibilityWeights)
    (h : ∀ i, (r i).Admissible hasC (kind i)) (saving : ℝ) (j : Fin n)
    (hsave : (r j).weightedCost 1 ≤ singletonAllowance hasC (kind j) - saving)
    (hbudget : (∑ i, singletonAllowance hasC (kind i)) ≤ 11 / 9 + saving) :
    (∑ i, (r i).weightedCost 1) ≤ 11 / 9 := by
  calc
    _ ≤ ∑ i, (singletonAllowance hasC (kind i) - if i = j then saving else 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i = j
      · simpa [hi] using hsave
      · simpa [hi] using (h i).cost_le_allowance
    _ = (∑ i, singletonAllowance hasC (kind i)) - saving := by
      rw [Finset.sum_sub_distrib]
      simp
    _ ≤ 11 / 9 := by linarith

private theorem caseII_sum_le_of_charge {n : ℕ}
    (kind : Fin n → SmallPieceClass) (r : Fin n → ResponsibilityWeights)
    (h : ∀ i, (r i).Admissible false (kind i))
    (hcharged : ∃ i, 2 / 3 ≤ (r i).extra)
    (hbudget : (∑ i, singletonAllowance false (kind i)) ≤ 11 / 9 + (4 / 27 - 1 / 20)) :
    (∑ i, (r i).weightedCost 1) ≤ 11 / 9 := by
  obtain ⟨j, hj⟩ := hcharged
  exact sum_le_of_saved_cost false kind r h (4 / 27 - 1 / 20) j
    (ResponsibilityWeights.caseII_cost_le_of_charge (h j) hj) hbudget

/-- Convert a bound on the singleton costs into the weight inequality (5.9C). -/
theorem weight_bound_of_responsibility_singleton_costs {n : ℕ}
    (pieces : Fin n → List ℝ) (r : Fin n → ResponsibilityWeights)
    (hpieces : ∀ i, ((pieces i).map w1).sum ≤ (r i).direct + (r i).indirect)
    (hbudget : (∑ i, (r i).weightedCost 1) ≤ 11 / 9) :
    W (List.ofFn pieces).flatten + ∑ i, (r i).credit ≤
      11 / 9 * (1 + ∑ i, (r i).credit) := by
  apply nonLarge_bin_bound_of_singleton_costs pieces (fun i => (r i).credit)
    (fun i => (r i).weightedCost 1) _ hbudget
  intro i
  simpa only [ResponsibilityWeights.weightedCost, one_mul] using
    sub_le_sub_right (hpieces i) (2 / 9 * (r i).credit)

/-- The DDDEE configuration of Case II. If each E-piece has a direct
responsibility and there is no extra charge, the size estimates force one
of the first two D-pieces to have only E-pieces as indirect responsibilities. -/
theorem caseII_DDDEE_singleton_budget
    (d₁ d₂ d₃ e₄ e₅ : ℝ) (r : Fin 5 → ResponsibilityWeights)
    (directE₄ directE₅ : Option ℝ)
    (hD₃ : 1 / 5 < d₃) (hfit : d₁ + d₂ + d₃ + e₄ + e₅ ≤ 1)
    (h : ∀ i, (r i).Admissible false (![.D, .D, .D, .E, .E] i))
    (hdiscrete : ∀ i, (r i).extra = 0 ∨ 2 / 3 ≤ (r i).extra)
    (habsent₄ : directE₄ = none → (r 3).direct = 0)
    (habsent₅ : directE₅ = none → (r 4).direct = 0)
    (hsize₄ : ∀ x, directE₄ = some x → (r 3).extra = 0 → x ≤ e₄)
    (hsize₅ : ∀ x, directE₅ = some x → (r 4).extra = 0 → x ≤ e₅)
    (hgap₁ : ∀ x, directE₄ = some x → (r 0).extra = 0 →
      d₁ + x ≤ 2 / 5 → (r 0).indirect ≤ ((r 0).count : ℝ) / 5)
    (hgap₂ : ∀ x, directE₅ = some x → (r 1).extra = 0 →
      d₂ + x ≤ 2 / 5 → (r 1).indirect ≤ ((r 1).count : ℝ) / 5) :
    (∑ i, (r i).weightedCost 1) ≤ 11 / 9 := by
  let kind : Fin 5 → SmallPieceClass := ![.D, .D, .D, .E, .E]
  by_cases hcharged : ∃ i, 2 / 3 ≤ (r i).extra
  · refine caseII_sum_le_of_charge kind r h hcharged ?_
    norm_num [kind, Fin.sum_univ_succ, singletonAllowance]
  · have hzero (i : Fin 5) : (r i).extra = 0 :=
      (hdiscrete i).resolve_right (fun hi => hcharged ⟨i, hi⟩)
    have save (j : Fin 5) (hcost :
        (r j).weightedCost 1 ≤ singletonAllowance false (kind j) - 1 / 36) :
        (∑ i, (r i).weightedCost 1) ≤ 11 / 9 := by
      refine sum_le_of_saved_cost false kind r h (1 / 36) j hcost ?_
      norm_num [kind, Fin.sum_univ_succ, singletonAllowance]
    by_cases hnone₄ : directE₄ = none
    · exact save 3 ((ResponsibilityWeights.caseII_E_cost_le_of_no_direct (h 3)
        (habsent₄ hnone₄)).trans (by change (0 : ℝ) ≤ 1 / 5 - 1 / 36; norm_num))
    by_cases hnone₅ : directE₅ = none
    · exact save 4 ((ResponsibilityWeights.caseII_E_cost_le_of_no_direct (h 4)
        (habsent₅ hnone₅)).trans (by change (0 : ℝ) ≤ 1 / 5 - 1 / 36; norm_num))
    obtain ⟨x₄, hx₄⟩ := Option.ne_none_iff_exists'.mp hnone₄
    obtain ⟨x₅, hx₅⟩ := Option.ne_none_iff_exists'.mp hnone₅
    rcases pair_size_le_of_three_D_two_E d₁ d₂ d₃ e₄ e₅ hD₃ hfit with hfirst | hsecond
    · have hsmall := hgap₁ x₄ hx₄ (hzero 0)
        (by linarith [hsize₄ x₄ hx₄ (hzero 3)])
      exact save 0 ((ResponsibilityWeights.caseII_D_cost_le_of_E_indirect (h 0) hsmall).trans
        (by change (1 / 4 : ℝ) ≤ 5 / 18 - 1 / 36; norm_num))
    · have hsmall := hgap₂ x₅ hx₅ (hzero 1)
        (by linarith [hsize₅ x₅ hx₅ (hzero 4)])
      exact save 1 ((ResponsibilityWeights.caseII_D_cost_le_of_E_indirect (h 1) hsmall).trans
        (by change (1 / 4 : ℝ) ≤ 5 / 18 - 1 / 36; norm_num))

/-- The DDDDE configuration of Case II. Each D-piece and a direct
responsibility for the E-piece fit in a gap of at most two fifths. -/
theorem caseII_DDDDE_singleton_budget
    (d : Fin 4 → ℝ) (e : ℝ) (r : Fin 5 → ResponsibilityWeights) (directE : Option ℝ)
    (hD : ∀ i, 1 / 5 < d i) (hfit : (∑ i, d i) + e ≤ 1)
    (h : ∀ i, (r i).Admissible false (![.D, .D, .D, .D, .E] i))
    (hdiscrete : ∀ i, (r i).extra = 0 ∨ 2 / 3 ≤ (r i).extra)
    (habsent : directE = none → (r 4).direct = 0)
    (hsize : ∀ x, directE = some x → (r 4).extra = 0 → x ≤ e)
    (hgap : ∀ i x, directE = some x → (r i.castSucc).extra = 0 →
      d i + x ≤ 2 / 5 → (r i.castSucc).indirect ≤ ((r i.castSucc).count : ℝ) / 5) :
    (∑ i, (r i).weightedCost 1) ≤ 11 / 9 := by
  let kind : Fin 5 → SmallPieceClass := ![.D, .D, .D, .D, .E]
  by_cases hcharged : ∃ i, 2 / 3 ≤ (r i).extra
  · refine caseII_sum_le_of_charge kind r h hcharged ?_
    norm_num [kind, Fin.sum_univ_succ, singletonAllowance]
  · have hzero (i : Fin 5) : (r i).extra = 0 :=
      (hdiscrete i).resolve_right (fun hi => hcharged ⟨i, hi⟩)
    by_cases hnone : directE = none
    · refine sum_le_of_saved_cost false kind r h (1 / 5) 4 ?_ ?_
      · have hc := ResponsibilityWeights.caseII_E_cost_le_of_no_direct (h 4) (habsent hnone)
        simpa [show kind 4 = .E from rfl, singletonAllowance] using hc
      · norm_num [kind, Fin.sum_univ_succ, singletonAllowance]
    · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hnone
      have hs := hsize x hx (hzero 4)
      rw [Fin.sum_univ_four] at hfit
      have hsmall (i : Fin 4) : d i + x ≤ 2 / 5 := by
        fin_cases i
        all_goals
          first
          | change d 0 + x ≤ 2 / 5
          | change d 1 + x ≤ 2 / 5
          | change d 2 + x ≤ 2 / 5
          | change d 3 + x ≤ 2 / 5
          linarith [hD 0, hD 1, hD 2, hD 3]
      have hDcost (i : Fin 4) : (r i.castSucc).weightedCost 1 ≤ 1 / 4 := by
        have hadm : (r i.castSucc).Admissible false .D := by
          fin_cases i <;> first | exact h 0 | exact h 1 | exact h 2 | exact h 3
        exact ResponsibilityWeights.caseII_D_cost_le_of_E_indirect hadm
          (hgap i x hx (hzero i.castSucc) (hsmall i))
      have hEcost : (r (Fin.last 4)).weightedCost 1 ≤ 1 / 5 := (h 4).cost_le_allowance
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_four]
      linarith [hDcost 0, hDcost 1, hDcost 2, hDcost 3]

/-- The BDDE configuration of Case II. A retained B-piece either has size at
most two fifths or bounds both D–E gaps by two fifths through feasibility. -/
theorem caseII_BDDE_singleton_budget
    (b d₂ d₃ e : ℝ) (r : Fin 4 → ResponsibilityWeights) (directE : Option ℝ)
    (hD₂ : 1 / 5 < d₂) (hD₃ : 1 / 5 < d₃) (hfit : b + d₂ + d₃ + e ≤ 1)
    (h : ∀ i, (r i).Admissible false (![.B, .D, .D, .E] i))
    (hdiscrete : ∀ i, (r i).extra = 0 ∨ 2 / 3 ≤ (r i).extra)
    (hB : (r 0).direct ≤ 1 / 4 ∨
      ∃ directB : ℝ, directB ≤ b ∧
        (directB ≤ 2 / 5 →
          (r 1).indirect ≤ ((r 1).count : ℝ) / 5 ∧
          (r 2).indirect ≤ ((r 2).count : ℝ) / 5))
    (habsent : directE = none → (r 3).direct = 0)
    (hsize : ∀ x, directE = some x → (r 3).extra = 0 → x ≤ e)
    (hgap₂ : ∀ x, directE = some x → (r 1).extra = 0 →
      d₂ + x ≤ 2 / 5 → (r 1).indirect ≤ ((r 1).count : ℝ) / 5)
    (hgap₃ : ∀ x, directE = some x → (r 2).extra = 0 →
      d₃ + x ≤ 2 / 5 → (r 2).indirect ≤ ((r 2).count : ℝ) / 5) :
    (∑ i, (r i).weightedCost 1) ≤ 11 / 9 := by
  let kind : Fin 4 → SmallPieceClass := ![.B, .D, .D, .E]
  by_cases hcharged : ∃ i, 2 / 3 ≤ (r i).extra
  · refine caseII_sum_le_of_charge kind r h hcharged ?_
    norm_num [kind, Fin.sum_univ_succ, singletonAllowance]
  · have hzero (i : Fin 4) : (r i).extra = 0 :=
      (hdiscrete i).resolve_right (fun hi => hcharged ⟨i, hi⟩)
    rcases hB with hdemote | ⟨directB, hBsize, hBsmall⟩
    · refine sum_le_of_saved_cost false kind r h (1 / 6) 0 ?_ ?_
      · have hc : (r 0).weightedCost 1 ≤ 1 / 3 :=
          ResponsibilityWeights.cost_le_of_demoted_B (h 0) hdemote
        change (r 0).weightedCost 1 ≤ 1 / 2 - 1 / 6
        linarith
      · norm_num [kind, Fin.sum_univ_succ, singletonAllowance]
    · have finish (h₂ : (r 1).indirect ≤ ((r 1).count : ℝ) / 5)
          (h₃ : (r 2).indirect ≤ ((r 2).count : ℝ) / 5) :
          (∑ i, (r i).weightedCost 1) ≤ 11 / 9 := by
        have hfirst : (r 0).weightedCost 1 ≤ 1 / 2 := (h 0).cost_le_allowance
        have hlast : (r 3).weightedCost 1 ≤ 1 / 5 := (h 3).cost_le_allowance
        rw [Fin.sum_univ_four]
        linarith [ResponsibilityWeights.caseII_D_cost_le_of_E_indirect (h 1) h₂,
          ResponsibilityWeights.caseII_D_cost_le_of_E_indirect (h 2) h₃]
      by_cases hsmall : directB ≤ 2 / 5
      · exact finish (hBsmall hsmall).1 (hBsmall hsmall).2
      · by_cases hnone : directE = none
        · refine sum_le_of_saved_cost false kind r h (1 / 5) 3 ?_ ?_
          · have hc := ResponsibilityWeights.caseII_E_cost_le_of_no_direct (h 3) (habsent hnone)
            simpa [show kind 3 = .E from rfl, singletonAllowance] using hc
          · norm_num [kind, Fin.sum_univ_succ, singletonAllowance]
        · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hnone
          have hb : 2 / 5 < b := (lt_of_not_ge hsmall).trans_le hBsize
          have hxe := hsize x hx (hzero 3)
          have hp₂ := pair_size_le_of_large_B_and_other_D b d₂ d₃ e hb hD₃ hfit
          have hp₃ := pair_size_le_of_large_B_and_other_D b d₃ d₂ e hb hD₂ (by linarith)
          exact finish (hgap₂ x hx (hzero 1) (by linarith))
            (hgap₃ x hx (hzero 2) (by linarith))

end BinPacking.Decreasing

end

/- assembly/ExceptionalBudgetsI.lean -/
section

namespace BinPacking.Decreasing

private theorem bc_pair_le_table
    (b c : ResponsibilityWeights) (joint : ℝ)
    (hB : b.Admissible true .B) (hC : c.Admissible true .C)
    (hplain : joint ≤ b.direct + c.direct)
    (hpair : (joint ≤ b.direct + (1 / 2 : ℝ) * c.direct ∧ b.count = 0) ∨
      b.direct ≤ 1 / 3) :
    joint + b.indirect + c.indirect - 2 / 9 * (b.credit + c.credit) ≤ 3 / 4 := by
  apply pair_cost_le_allowance true .B .C b c joint (3 / 4) rfl hB hC hplain
  rcases hpair with ⟨hjoint, hcount⟩ | hdemote
  · have hlimit : b.direct ≤ unpromotedWeightLimit true .B := by
      simpa [unpromotedWeightLimit, directWeightLimit, hcount] using hB.direct_le
    exact Or.inl ⟨hjoint, hlimit, hC.direct_le, hcount.le⟩
  · exact Or.inr (Or.inl hdemote)

/-- Case I, BBC. A retained first B-piece has direct size below `5/12`
by feasibility. The resulting deficit gap forces a direct or indirect
demotion unless the C-piece already pays a promotion charge. -/
theorem caseI_BBC_pair_budget
    (b₁ b₂ c : ℝ) (r₁ r₂ r₃ : ResponsibilityWeights) (joint : ℝ)
    (hb₂ : 1 / 3 < b₂ ∧ b₂ ≤ 1 / 2) (hc : 1 / 4 < c)
    (horder : b₂ ≤ b₁) (hfit : b₁ + b₂ + c ≤ 1)
    (h₁ : r₁.Admissible true .B) (h₂ : r₂.Admissible true .B)
    (h₃ : r₃.Admissible true .C)
    (hB₁ : r₁.direct ≤ 1 / 3 ∨
      ∃ directB₁ : ℝ, directB₁ ≤ b₁ ∧
        (directB₁ < 5 / 12 → r₃.direct ≤ 1 / 4 ∨
          r₃.indirect ≤ (r₃.count : ℝ) / 5 ∨ 2 / 3 ≤ r₃.extra))
    (hplain : joint ≤ r₂.direct + r₃.direct)
    (hpair : ObeysRelation b₂ c →
      (joint ≤ r₂.direct + (1 / 2 : ℝ) * r₃.direct ∧ r₂.count = 0) ∨
        r₂.direct ≤ 1 / 3) :
    r₁.weightedCost 1 + (joint + r₂.indirect + r₃.indirect -
      2 / 9 * (r₂.credit + r₃.credit)) ≤ 11 / 9 := by
  have hrelation := relation_of_two_B b₁ b₂ c hb₂ horder hfit
  rcases hB₁ with hdemote | ⟨directB₁, hBsize, hgap⟩
  · have hfirst : r₁.weightedCost 1 ≤ 7 / 18 :=
      ResponsibilityWeights.cost_le_of_demoted_B h₁ hdemote
    linarith [bc_pair_le_table r₂ r₃ joint h₂ h₃ hplain (hpair hrelation)]
  · have hfirst : r₁.weightedCost 1 ≤ 1 / 2 := h₁.cost_le_allowance
    have hthird (factor : ℝ) (hfactor : 1 / 3 ≤ factor) :
        r₃.weightedCost factor ≤ factor * (1 / 3) := by
      have hc' : r₃.direct ≤ 1 / 3 := h₃.direct_le
      have hcount : r₃.count ≤ 1 := h₃.count_le
      have hcountReal : (r₃.count : ℝ) ≤ 1 := by exact_mod_cast hcount
      have hnonnegative : 0 ≤ factor := by linarith
      unfold ResponsibilityWeights.weightedCost ResponsibilityWeights.credit
      rcases hgap (by linarith [hb₂.1]) with hdemote | hindirect | hcharge
      · linarith [mul_le_mul_of_nonneg_left hdemote hnonnegative, h₃.indirect_le,
          h₃.extra_nonneg]
      · linarith [mul_le_mul_of_nonneg_left hc' hnonnegative, h₃.extra_nonneg,
          Nat.cast_nonneg (α := ℝ) r₃.count]
      · linarith [mul_le_mul_of_nonneg_left hc' hnonnegative, h₃.indirect_le]
    rcases hpair hrelation with ⟨hjoint, _⟩ | hdemote
    · have hsecond : r₂.weightedCost 1 ≤ 1 / 2 := h₂.cost_le_allowance
      have hc' := hthird (1 / 2) (by norm_num)
      unfold ResponsibilityWeights.weightedCost at hsecond hc'
      linarith
    · have hsecond : r₂.weightedCost 1 ≤ 7 / 18 :=
        ResponsibilityWeights.cost_le_of_demoted_B h₂ hdemote
      have hc' := hthird 1 (by norm_num)
      unfold ResponsibilityWeights.weightedCost at hsecond hc'
      linarith

private theorem w1_C {x : ℝ} (hx : 1 / 4 < x ∧ x ≤ 1 / 3) : w1 x = 1 / 3 := by
  norm_num [w1, pieceNum_C hx.1 hx.2]

private theorem w1_D {x : ℝ} (hx : 1 / 5 < x ∧ x ≤ 1 / 4) : w1 x = 1 / 4 := by
  norm_num [w1, pieceNum_D hx.1 hx.2]

private theorem discounted_C_D_bound (c d : ℝ)
    (hc : 1 / 4 < c ∧ c ≤ 1 / 3) (hd : 1 / 5 < d ∧ d ≤ 1 / 4)
    (hfit : 3 * c + d ≤ 1) : W [c, d] ≤ 1 / 2 := by
  have hdiscount : ObeysRelation c d := by
    unfold ObeysRelation
    simpa [pieceNum_C hc.1 hc.2] using hfit
  have hp := weight_pair_le c d (hd.2.trans hc.1.le)
  rw [w2, if_pos hdiscount] at hp
  norm_num [pieceNum_C hc.1 hc.2, w1_C hc, w1_D hd] at hp
  exact hp

/-- Case I, CCCD with three retained C-pieces, three D-pieces from their
indirect responsibilities, and a retained D-piece. The hypotheses express
the size comparisons used to choose two disjoint discounted pairs. -/
theorem caseI_CCCD_saturated_weight_budget
    (c₁ c₂ c₃ d q₁ q₂ q₃ v u₁ u₂ u₃ : ℝ) (pieces : List ℝ)
    (hfit : c₁ + c₂ + c₃ + d ≤ 1) (h₁ : c₃ ≤ c₁) (h₂ : c₃ ≤ c₂)
    (hCs : ∀ x ∈ [q₁, q₂, q₃], 1 / 4 < x ∧ x ≤ 1 / 3)
    (hDs : ∀ x ∈ [v, u₁, u₂, u₃], 1 / 5 < x ∧ x ≤ 1 / 4)
    (hleft₁ : q₁ ≤ c₃) (hleft₃ : q₃ ≤ c₃) (hright : v ≤ d)
    (hdeficit : q₃ + u₃ ≤ c₃ + v)
    (hvalid : IsList pieces)
    (hperm : pieces.Perm [q₁, v, q₃, u₃, q₂, u₁, u₂]) :
    W pieces + 3 ≤ 11 / 9 * (1 + 3) := by
  have hcapacity : 3 * c₃ + d ≤ 1 := by linarith
  have hfirst := discounted_C_D_bound q₁ v
    (hCs _ (by simp)) (hDs _ (by simp)) (by linarith)
  have hsecond := discounted_C_D_bound q₃ u₃
    (hCs _ (by simp)) (hDs _ (by simp)) (by linarith)
  have htail : W [q₂, u₁, u₂] ≤ 5 / 6 := by
    have h := weight_le_singleton_sum [q₂, u₁, u₂]
    norm_num [w1_C (hCs q₂ (by simp)), w1_D (hDs u₁ (by simp)),
      w1_D (hDs u₂ (by simp))] at h
    exact h
  have hgroup : W pieces ≤ W [q₁, v] + (W [q₃, u₃] + W [q₂, u₁, u₂]) := by
    rw [weight_perm hperm]
    simpa using (weight_flatten_le_sum [[q₁, v], [q₃, u₃], [q₂, u₁, u₂]]
      (fun _ hx => hvalid _ (hperm.mem_iff.mpr hx)))
  linarith

private theorem caseI_C_cost_le_of_deficiency (c : ResponsibilityWeights)
    (h : c.Admissible true .C)
    (hdef : c.direct ≤ 1 / 4 ∨ c.indirect ≤ (c.count : ℝ) / 5) :
    c.weightedCost 1 ≤ 1 / 3 := by
  rcases hdef with hdemote | he
  · have hb : c.count ≤ 1 := h.count_le
    have hc := responsibility_cost_le 1 c.direct c.indirect c.extra
      (1 / 4) 0 c.count 1 zero_le_one hdemote h.indirect_le hb h.extra_nonneg
    unfold ResponsibilityWeights.weightedCost ResponsibilityWeights.credit
    norm_num at hc
    linarith
  · have hd : c.direct ≤ 1 / 3 := h.direct_le
    unfold ResponsibilityWeights.weightedCost ResponsibilityWeights.credit
    linarith [h.extra_nonneg, Nat.cast_nonneg (α := ℝ) c.count]

private theorem cd_pair_le_table (c d : ResponsibilityWeights) (joint : ℝ)
    (hC : c.Admissible true .C) (hD : d.Admissible true .D)
    (hplain : joint ≤ c.direct + d.direct)
    (hpair : joint ≤ c.direct + (2 / 3 : ℝ) * d.direct ∨
      c.direct ≤ 1 / 4 ∨ 2 / 3 ≤ d.extra) :
    joint + c.indirect + d.indirect - 2 / 9 * (c.credit + d.credit) ≤ 19 / 36 := by
  apply pair_cost_le_allowance true .C .D c d joint (19 / 36) rfl hC hD hplain
  rcases hpair with hcut | hdemote | hcharge
  · exact Or.inl ⟨hcut, hC.direct_le, hD.direct_le, hC.count_le⟩
  · exact Or.inr (Or.inl hdemote)
  · exact Or.inr (Or.inr (Or.inr ⟨Or.inl rfl, hcharge⟩))

private theorem cd_pair_le_half_of_deficiency (c d : ResponsibilityWeights) (joint : ℝ)
    (hC : c.Admissible true .C) (hD : d.Admissible true .D)
    (hplain : joint ≤ c.direct + d.direct)
    (hpair : joint ≤ c.direct + (2 / 3 : ℝ) * d.direct ∨
      c.direct ≤ 1 / 4 ∨ 2 / 3 ≤ d.extra)
    (hdef : c.indirect ≤ (c.count : ℝ) / 5 ∨ d.direct ≤ 1 / 5) :
    joint + c.indirect + d.indirect - 2 / 9 * (c.credit + d.credit) ≤ 1 / 2 := by
  have hdscore (factor cap floor : ℝ) (hf : 0 ≤ factor) (hcap : d.direct ≤ cap)
      (hflo : floor ≤ d.extra) :
      d.weightedCost factor ≤ factor * cap - 2 / 9 * floor := by
    have hn : d.count ≤ 0 := hD.count_le
    simpa only [ResponsibilityWeights.credit, ResponsibilityWeights.weightedCost,
      Nat.cast_zero, zero_div, add_zero] using
      responsibility_cost_le factor d.direct d.indirect d.extra cap floor d.count 0
        hf hcap hD.indirect_le hn hflo
  have hCbase : c.weightedCost 1 ≤ 13 / 36 := hC.cost_le_allowance
  have hDbase : d.direct ≤ 1 / 4 := hD.direct_le
  rcases hpair with hcut | hdemote | hcharge
  · rcases hdef with hE | hsmall
    · have hc := caseI_C_cost_le_of_deficiency c hC (Or.inr hE)
      have hd := hdscore (2 / 3) (1 / 4) 0 (by norm_num) hDbase hD.extra_nonneg
      unfold ResponsibilityWeights.weightedCost at hc hd
      linarith
    · have hd := hdscore (2 / 3) (1 / 5) 0 (by norm_num) hsmall hD.extra_nonneg
      unfold ResponsibilityWeights.weightedCost at hCbase hd
      linarith
  · rcases hdef with hE | hsmall
    · have hc : c.weightedCost 1 ≤ 1 / 4 := by
        unfold ResponsibilityWeights.weightedCost ResponsibilityWeights.credit
        linarith [hC.extra_nonneg, Nat.cast_nonneg (α := ℝ) c.count]
      have hd := hdscore 1 (1 / 4) 0 zero_le_one hDbase hD.extra_nonneg
      unfold ResponsibilityWeights.weightedCost at hc hd
      linarith
    · have hc := responsibility_cost_le 1 c.direct c.indirect c.extra
        (1 / 4) 0 c.count 1 zero_le_one hdemote hC.indirect_le
        (show c.count ≤ 1 from hC.count_le) hC.extra_nonneg
      have hd := hdscore 1 (1 / 5) 0 zero_le_one hsmall hD.extra_nonneg
      unfold ResponsibilityWeights.weightedCost ResponsibilityWeights.credit at hd
      unfold ResponsibilityWeights.credit
      norm_num at hc
      linarith
  · have hd := hdscore 1 (1 / 4) (2 / 3) zero_le_one hDbase hcharge
    unfold ResponsibilityWeights.weightedCost at hCbase hd
    linarith

/-- In CCCD, retain the C₃–D discount and tighten the estimate whenever a
responsibility group has one of the indicated smaller weights. -/
theorem caseI_CCCD_refined_pair_budget
    (c₁ c₂ c₃ d : ℝ) (r₁ r₂ r₃ r₄ : ResponsibilityWeights) (joint : ℝ)
    (hc₃ : 1 / 4 < c₃ ∧ c₃ ≤ 1 / 3) (hs₁ : c₃ ≤ c₁) (hs₂ : c₃ ≤ c₂)
    (hfit : c₁ + c₂ + c₃ + d ≤ 1)
    (h₁ : r₁.Admissible true .C) (h₂ : r₂.Admissible true .C)
    (h₃ : r₃.Admissible true .C) (h₄ : r₄.Admissible true .D)
    (hplain : joint ≤ r₃.direct + r₄.direct)
    (hpair : ObeysRelation c₃ d → joint ≤ r₃.direct + (2 / 3 : ℝ) * r₄.direct ∨
      r₃.direct ≤ 1 / 4 ∨ 2 / 3 ≤ r₄.extra)
    (hrefinement :
      (r₁.direct ≤ 1 / 4 ∨ r₁.indirect ≤ (r₁.count : ℝ) / 5) ∨
      (r₂.direct ≤ 1 / 4 ∨ r₂.indirect ≤ (r₂.count : ℝ) / 5) ∨
      (r₃.indirect ≤ (r₃.count : ℝ) / 5 ∨ r₄.direct ≤ 1 / 5)) :
    r₁.weightedCost 1 + r₂.weightedCost 1 + (joint + r₃.indirect + r₄.indirect -
      2 / 9 * (r₃.credit + r₄.credit)) ≤ 11 / 9 := by
  have hrelation := relation_of_three_C c₁ c₂ c₃ d hc₃ hs₁ hs₂ hfit
  have hfirst : r₁.weightedCost 1 ≤ 13 / 36 := h₁.cost_le_allowance
  have hsecond : r₂.weightedCost 1 ≤ 13 / 36 := h₂.cost_le_allowance
  have hpaired := cd_pair_le_table r₃ r₄ joint h₃ h₄ hplain (hpair hrelation)
  rcases hrefinement with hdef | hdef | hdef
  · linarith [caseI_C_cost_le_of_deficiency r₁ h₁ hdef]
  · linarith [caseI_C_cost_le_of_deficiency r₂ h₂ hdef]
  · linarith [cd_pair_le_half_of_deficiency r₃ r₄ joint h₃ h₄ hplain (hpair hrelation) hdef]

private theorem caseI_CD_cost_le_of_charge (r : ResponsibilityWeights) (kind : SmallPieceClass)
    (hkind : kind = .C ∨ kind = .D) (hr : r.Admissible true kind) (he : 2 / 3 ≤ r.extra) :
    r.weightedCost 1 ≤ singletonAllowance true kind - 4 / 27 := by
  have hc := responsibility_cost_le 1 r.direct r.indirect r.extra
    (directWeightLimit true r.count kind) (2 / 3) r.count (indirectCountLimit true kind)
    zero_le_one hr.direct_le hr.indirect_le hr.count_le he
  rcases hkind with rfl | rfl <;>
    norm_num [ResponsibilityWeights.weightedCost, ResponsibilityWeights.credit,
      directWeightLimit, indirectCountLimit, singletonAllowance] at hc ⊢ <;>
    linarith

/-- In CCCD, an extra charge of at least two thirds pays for the entire
excess of the singleton estimate. -/
theorem caseI_CCCD_singleton_budget_of_charge
    (r : Fin 4 → ResponsibilityWeights)
    (h : ∀ i, (r i).Admissible true (![.C, .C, .C, .D] i))
    (hcharge : ∃ i, 2 / 3 ≤ (r i).extra) :
    (∑ i, (r i).weightedCost 1) ≤ 11 / 9 := by
  obtain ⟨j, hj⟩ := hcharge
  have h₁ : (r 0).weightedCost 1 ≤ 13 / 36 := (h 0).cost_le_allowance
  have h₂ : (r 1).weightedCost 1 ≤ 13 / 36 := (h 1).cost_le_allowance
  have h₃ : (r 2).weightedCost 1 ≤ 13 / 36 := (h 2).cost_le_allowance
  have h₄ : (r 3).weightedCost 1 ≤ 1 / 4 := (h 3).cost_le_allowance
  rw [Fin.sum_univ_four]
  fin_cases j
  · have hc : (r 0).weightedCost 1 ≤ 13 / 36 - 4 / 27 :=
      caseI_CD_cost_le_of_charge (r 0) .C (Or.inl rfl) (h 0) hj
    linarith
  · have hc : (r 1).weightedCost 1 ≤ 13 / 36 - 4 / 27 :=
      caseI_CD_cost_le_of_charge (r 1) .C (Or.inl rfl) (h 1) hj
    linarith
  · have hc : (r 2).weightedCost 1 ≤ 13 / 36 - 4 / 27 :=
      caseI_CD_cost_le_of_charge (r 2) .C (Or.inl rfl) (h 2) hj
    linarith
  · have hd : (r 3).weightedCost 1 ≤ 1 / 4 - 4 / 27 :=
      caseI_CD_cost_le_of_charge (r 3) .D (Or.inr rfl) (h 3) hj
    linarith

/-- When C₃ is demoted and each C-piece has one indirect responsibility,
pair D with a retained C₁ responsibility. The residual C-piece size bound
still gives the discount. -/
theorem caseI_CCCD_demoted_third_weight_budget
    (c₁ c₂ c₃ d q v : ℝ) (indirect₁ group₂ group₃ pieces : List ℝ)
    (hfit : c₁ + c₂ + c₃ + d ≤ 1) (h₁ : c₃ ≤ c₁) (h₂ : c₃ ≤ c₂)
    (hq : 1 / 4 < q ∧ q ≤ 1 / 3) (hv : 1 / 5 < v ∧ v ≤ 1 / 4)
    (hqsize : q ≤ c₃) (hvsize : v ≤ d)
    (hweight₁ : (indirect₁.map w1).sum ≤ 1 / 4)
    (hweight₂ : (group₂.map w1).sum ≤ 7 / 12)
    (hweight₃ : (group₃.map w1).sum ≤ 1 / 2)
    (hvalid : IsList pieces)
    (hperm : pieces.Perm ([q, v] ++ (indirect₁ ++ (group₂ ++ group₃)))) :
    W pieces + 3 ≤ 11 / 9 * (1 + 3) := by
  have hdiscount := discounted_C_D_bound q v hq hv (by linarith)
  let parts := [[q, v], indirect₁, group₂, group₃]
  have hcover : pieces.Perm parts.flatten := by simpa [parts] using hperm
  have hweight : W parts.flatten ≤ W [q, v] + (W indirect₁ + (W group₂ + W group₃)) := by
    simpa [parts] using weight_flatten_le_sum parts
      (fun _ hx => hvalid _ (hcover.mem_iff.mpr hx))
  rw [weight_perm hcover]
  linarith [(weight_le_singleton_sum indirect₁).trans hweight₁,
    (weight_le_singleton_sum group₂).trans hweight₂,
    (weight_le_singleton_sum group₃).trans hweight₃]

end BinPacking.Decreasing

end

/- OrdinaryCaseI.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

open PieceChains

noncomputable section

variable {S : List ℝ} (p : AlignedPacking S)

theorem ordinary_uncharged_of_extra_eq_zero (item : NonLargePosition S) (r : ResidualPosition S)
    (owner : p.owner r = ordinaryOwner item) (zero : (p.ordinaryWeights item).extra = 0) :
    r.val ∉ p.thirdSlotTerminals := by
  intro charged
  have positive := p.ordinary_extra_ge_of_mem item r owner charged
  linarith

private theorem exists_direct_of_weight_gt (item : NonLargePosition S) (k : ℕ) (positive : 0 < k)
    (heavy : (1 / (k : ℝ)) < (p.ordinaryWeights item).direct) :
    ∃ r, p.ordinaryDirect item = some r ∧ (1 / (k : ℝ)) < residualSize r := by
  by_contra! noLarge
  apply (not_lt_of_ge ?_) heavy
  exact p.ordinaryDirectWeight_le_of_size_le item k positive fun r mem =>
    noLarge r ((p.ordinaryDirect_eq_some_iff item r).mpr mem)

private theorem exists_indirect_of_weight_gt (item : NonLargePosition S) (k : ℕ) (positive : 0 < k)
    (heavy : ((p.ordinaryWeights item).count : ℝ) / k < (p.ordinaryWeights item).indirect) :
    ∃ r ∈ p.ordinaryIndirectPositions item, (1 / (k : ℝ)) < residualSize r := by
  by_contra! noLarge
  exact (not_lt_of_ge (p.ordinaryIndirectWeight_le_count item k positive noLarge)) heavy

private theorem ordinaryIndirect_eq_singleton (item : NonLargePosition S) (r : ResidualPosition S)
    (mem : r ∈ p.ordinaryIndirectPositions item) (count : (p.ordinaryWeights item).count ≤ 1) :
    p.ordinaryIndirectPositions item = {r} := by
  classical
  change (p.ordinaryIndirectPositions item).card ≤ 1 at count
  ext x
  simp only [Finset.mem_singleton]
  exact ⟨fun h => Finset.card_le_one_iff.mp count h mem, fun same => same.symm ▸ mem⟩

private theorem retained_C_terminal (item : NonLargePosition S)
    (upper : S.get item.val ≤ 1 / 3) (zero : (p.ordinaryWeights item).extra = 0)
    (heavy : 1 / 4 < (p.ordinaryWeights item).direct) :
    ∃ r, p.ordinaryDirect item = some r ∧ (1 / 4 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3 := by
  obtain ⟨r, present, lower⟩ := p.exists_direct_of_weight_gt item 4 (by decide) (by simpa using heavy)
  exact ⟨r, present, by simpa using lower, (p.direct_size_le_of_extra_eq_zero item r
    ((p.ordinaryDirect_eq_some_iff item r).mp present) zero).trans upper⟩

private theorem retained_D_terminal (item : NonLargePosition S)
    (upper : S.get item.val ≤ 1 / 4) (zero : (p.ordinaryWeights item).extra = 0)
    (heavy : 1 / 5 < (p.ordinaryWeights item).direct) :
    ∃ r, p.ordinaryDirect item = some r ∧ (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 4 := by
  obtain ⟨r, present, lower⟩ := p.exists_direct_of_weight_gt item 5 (by decide) (by simpa using heavy)
  exact ⟨r, present, by simpa using lower, (p.direct_size_le_of_extra_eq_zero item r
    ((p.ordinaryDirect_eq_some_iff item r).mp present) zero).trans upper⟩

private theorem retained_indirect_D (item : NonLargePosition S) (count : (p.ordinaryWeights item).count ≤ 1)
    (heavy : ((p.ordinaryWeights item).count : ℝ) / 5 < (p.ordinaryWeights item).indirect) :
    ∃ r ∈ p.ordinaryIndirectPositions item, (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 4 ∧
      p.ordinaryIndirectPieces item = [residualSize r] ∧ (p.ordinaryWeights item).count = 1 := by
  obtain ⟨r, member, lower⟩ := p.exists_indirect_of_weight_gt item 5 (by decide) (by simpa using heavy)
  have singleton := p.ordinaryIndirect_eq_singleton item r member count
  refine ⟨r, member, by simpa using lower, p.indirect_size_le_quarter r
    ((p.mem_ordinaryIndirectPositions_iff item r).mp member).2, ?_, ?_⟩
  · simp [ordinaryIndirectPieces, singleton]
  · simp [ordinaryWeights, singleton]

private theorem ordinary_C_refined_by_B (c : NonLargePosition S) (resB : ResidualPosition S)
    (cSmall : S.get c.val ≤ 1 / 3)
    (bSize : (1 / 3 : ℝ) < residualSize resB ∧ residualSize resB < 5 / 12) :
    (p.ordinaryWeights c).direct ≤ 1 / 4 ∨
      (p.ordinaryWeights c).indirect ≤ ((p.ordinaryWeights c).count : ℝ) / 5 ∨
      (2 / 3 : ℝ) ≤ (p.ordinaryWeights c).extra := by
  rcases p.ordinary_extra_discrete c with zero | charge
  · by_contra! notRefined
    obtain ⟨direct, known, directLarge⟩ := p.exists_direct_of_weight_gt c 4 (by decide)
      (by simpa using notRefined.1)
    obtain ⟨indirect, indirectMem, indirectLarge⟩ := p.exists_indirect_of_weight_gt c 5
      (by decide) (by simpa using notRefined.2.1)
    have directMem := (p.ordinaryDirect_eq_some_iff c direct).mp known
    have indirectOwner := p.mem_ordinaryIndirectPositions_iff c indirect |>.mp indirectMem |>.1
    have directOwner := p.mem_ordinaryDirectPositions_iff c direct |>.mp directMem |>.1
    obtain ⟨head, deficit, third, owned, path⟩ := p.ordinaryIndirectPosition_head c indirect indirectMem
    have slot := p.ordinary_responsible_greedySlot c deficit cSmall owned
    have refined := p.uncharged_BBC_companions_demoted resB bSize cSmall slot third
      (Nat.le_of_not_gt direct.property) (Nat.le_of_not_gt indirect.property)
      (p.ordinary_uncharged_of_extra_eq_zero c direct directOwner zero)
      (p.ordinary_uncharged_of_extra_eq_zero c indirect indirectOwner zero)
      (p.ordinaryDirectPosition_path c direct directMem) path
    rcases refined with directSmall | indirectSmall
    · exact (not_lt_of_ge directSmall) (by simpa [residualSize] using directLarge)
    · exact (not_lt_of_ge indirectSmall) (by simpa [residualSize] using indirectLarge)
  · exact Or.inr (Or.inr charge)

theorem ordinary_BBC_budget (b₁ b₂ c : NonLargePosition S)
    (b₂Size : 1 / 3 < S.get b₂.val ∧ S.get b₂.val ≤ 1 / 2)
    (cSize : 1 / 4 < S.get c.val ∧ S.get c.val ≤ 1 / 3)
    (ordered : S.get b₂.val ≤ S.get b₁.val) (fits : S.get b₁.val + S.get b₂.val + S.get c.val ≤ 1)
    (b₁Weight : (p.ordinaryWeights b₁).Admissible true .B)
    (b₂Weight : (p.ordinaryWeights b₂).Admissible true .B)
    (cWeight : (p.ordinaryWeights c).Admissible true .C)
    (pair : ObeysRelation (S.get b₂.val) (S.get c.val) →
      (W (p.ordinaryDirectPieces b₂ ++ p.ordinaryDirectPieces c) ≤
        (p.ordinaryWeights b₂).direct + (1 / 2 : ℝ) * (p.ordinaryWeights c).direct ∧
        (p.ordinaryWeights b₂).count = 0) ∨ (p.ordinaryWeights b₂).direct ≤ 1 / 3) :
    p.ordinaryGroupCost [b₁, b₂, c] ≤ 11 / 9 := by
  have first : (p.ordinaryWeights b₁).direct ≤ 1 / 3 ∨
      ∃ d : ℝ, d ≤ S.get b₁.val ∧ (d < 5 / 12 →
        (p.ordinaryWeights c).direct ≤ 1 / 4 ∨
        (p.ordinaryWeights c).indirect ≤ ((p.ordinaryWeights c).count : ℝ) / 5 ∨
        (2 / 3 : ℝ) ≤ (p.ordinaryWeights c).extra) := by
    by_cases small : (p.ordinaryWeights b₁).direct ≤ 1 / 3
    · exact Or.inl small
    · obtain ⟨direct, known, large⟩ := p.exists_direct_of_weight_gt b₁ 3 (by decide)
        (by simpa using lt_of_not_ge small)
      have lower : (1 / 3 : ℝ) < residualSize direct := by simpa using large
      have bound := p.direct_size_le_max_of_mem b₁ direct
        ((p.ordinaryDirect_eq_some_iff b₁ direct).mp known)
      have leOwner : residualSize direct ≤ S.get b₁.val := by
        rcases le_max_iff.mp bound with leOwner | small
        · exact leOwner
        · linarith
      exact Or.inr ⟨residualSize direct, leOwner, fun size =>
        p.ordinary_C_refined_by_B c direct cSize.2 ⟨lower, size⟩⟩
  calc
    p.ordinaryGroupCost [b₁, b₂, c] ≤ p.ordinaryGroupCost [b₁] + p.ordinaryGroupCost [b₂, c] :=
      p.ordinaryGroupCost_append_le [b₁] [b₂, c]
    _ ≤ _ := by
      have one := p.ordinaryGroupCost_le_singleton_costs [b₁]
      have two := p.ordinaryGroupCost_pair_le_of_direct b₂ c
      have budget := caseI_BBC_pair_budget (S.get b₁.val) (S.get b₂.val) (S.get c.val)
        (p.ordinaryWeights b₁) (p.ordinaryWeights b₂) (p.ordinaryWeights c)
        (W (p.ordinaryDirectPieces b₂ ++ p.ordinaryDirectPieces c)) b₂Size cSize.1 ordered fits
        b₁Weight b₂Weight cWeight first (p.direct_pair_weight_le_plain b₂ c) pair
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at one
      linarith

private theorem ordinary_CCCD_uncharged_budget (c₁ c₂ c₃ d : NonLargePosition S)
    (upper₁ : S.get c₁.val ≤ 1 / 3) (upper₂ : S.get c₂.val ≤ 1 / 3) (upper₃ : S.get c₃.val ≤ 1 / 3)
    (upperD : S.get d.val ≤ 1 / 4)
    (ordered₁ : S.get c₃.val ≤ S.get c₁.val) (ordered₂ : S.get c₃.val ≤ S.get c₂.val)
    (fits : S.get c₁.val + S.get c₂.val + S.get c₃.val + S.get d.val ≤ 1)
    (w₁ : (p.ordinaryWeights c₁).Admissible true .C)
    (w₂ : (p.ordinaryWeights c₂).Admissible true .C)
    (w₃ : (p.ordinaryWeights c₃).Admissible true .C)
    (wD : (p.ordinaryWeights d).Admissible true .D)
    (z₁ : (p.ordinaryWeights c₁).extra = 0) (z₂ : (p.ordinaryWeights c₂).extra = 0)
    (z₃ : (p.ordinaryWeights c₃).extra = 0) (zD : (p.ordinaryWeights d).extra = 0)
    (large₁ : 1 / 4 < (p.ordinaryWeights c₁).direct)
    (large₂ : 1 / 4 < (p.ordinaryWeights c₂).direct)
    (largeD : 1 / 5 < (p.ordinaryWeights d).direct)
    (indirect₁ : ((p.ordinaryWeights c₁).count : ℝ) / 5 < (p.ordinaryWeights c₁).indirect)
    (indirect₂ : ((p.ordinaryWeights c₂).count : ℝ) / 5 < (p.ordinaryWeights c₂).indirect)
    (indirect₃ : ((p.ordinaryWeights c₃).count : ℝ) / 5 < (p.ordinaryWeights c₃).indirect) :
    p.ordinaryGroupCost [c₁, c₂, c₃, d] ≤ 11 / 9 := by
  obtain ⟨q₁, q₁At, q₁Lo, q₁Hi⟩ := p.retained_C_terminal c₁ upper₁ z₁ large₁
  obtain ⟨q₂, q₂At, q₂Lo, q₂Hi⟩ := p.retained_C_terminal c₂ upper₂ z₂ large₂
  obtain ⟨v, vAt, vLo, vHi⟩ := p.retained_D_terminal d upperD zD largeD
  obtain ⟨u₁, _, u₁Lo, u₁Hi, u₁List, n₁⟩ := p.retained_indirect_D c₁ w₁.count_le indirect₁
  obtain ⟨u₂, _, u₂Lo, u₂Hi, u₂List, n₂⟩ := p.retained_indirect_D c₂ w₂.count_le indirect₂
  obtain ⟨u₃, u₃Mem, u₃Lo, u₃Hi, u₃List, n₃⟩ := p.retained_indirect_D c₃ w₃.count_le indirect₃
  have nD : (p.ordinaryWeights d).count = 0 := Nat.eq_zero_of_le_zero wD.count_le
  have emptyD : p.ordinaryIndirectPositions d = ∅ := Finset.card_eq_zero.mp nD
  have allCredit : ([c₁, c₂, c₃, d].map (ResponsibilityWeights.credit ∘ p.ordinaryWeights)).sum = 3 := by
    norm_num [ResponsibilityWeights.credit, n₁, n₂, n₃, nD, z₁, z₂, z₃, zD]
  have q₁Size := p.residual_size_le_ordinary_of_indirect c₃ u₃Mem q₁ q₁Hi
  have vSize := p.direct_size_le_of_extra_eq_zero d v ((p.ordinaryDirect_eq_some_iff d v).mp vAt) zD
  let pieces := [c₁, c₂, c₃, d].flatMap p.ordinaryOwnerPieces
  have valid : IsList pieces := p.ordinaryGroupPieces_valid [c₁, c₂, c₃, d]
  have first : (p.ordinaryOwnerPieces c₁).Perm [residualSize q₁, residualSize u₁] := by
    simpa [ordinaryDirectPieces, q₁At, u₁List] using p.ordinaryOwnerPieces_perm_direct_indirect c₁
  have second : (p.ordinaryOwnerPieces c₂).Perm [residualSize q₂, residualSize u₂] := by
    simpa [ordinaryDirectPieces, q₂At, u₂List] using p.ordinaryOwnerPieces_perm_direct_indirect c₂
  have fourth : (p.ordinaryOwnerPieces d).Perm [residualSize v] := by
    simpa [ordinaryDirectPieces, ordinaryIndirectPieces, vAt, emptyD] using
      p.ordinaryOwnerPieces_perm_direct_indirect d
  have bounded : W pieces + 3 ≤ (11 / 9 : ℝ) * (1 + 3) := by
    by_cases demoted : (p.ordinaryWeights c₃).direct ≤ 1 / 4
    · have perm : pieces.Perm ([residualSize q₁, residualSize v] ++
          (p.ordinaryIndirectPieces c₁ ++ (p.ordinaryOwnerPieces c₂ ++ p.ordinaryOwnerPieces c₃))) := by
        have separated := first.append ((List.Perm.refl (p.ordinaryOwnerPieces c₂)).append
          ((List.Perm.refl (p.ordinaryOwnerPieces c₃)).append fourth))
        have swap := (List.perm_append_comm (l₁ := [residualSize u₁] ++
            (p.ordinaryOwnerPieces c₂ ++ p.ordinaryOwnerPieces c₃))
          (l₂ := [residualSize v])).cons (residualSize q₁)
        exact (by simpa [pieces, List.append_assoc] using
          separated.trans (by simpa [u₁List, List.append_assoc] using swap))
      have weight₁ : ((p.ordinaryIndirectPieces c₁).map w1).sum ≤ 1 / 4 := by
        rw [p.ordinaryIndirectPieces_weight_sum]
        simpa [n₁] using w₁.indirect_le
      have weight₂ : ((p.ordinaryOwnerPieces c₂).map w1).sum ≤ 7 / 12 := by
        rw [p.ordinaryOwnerPieces_weight_sum]
        have indirect := w₂.indirect_le
        rw [n₂] at indirect
        have direct : (p.ordinaryWeights c₂).direct ≤ 1 / 3 := w₂.direct_le
        linarith only [direct, indirect]
      have weight₃ : ((p.ordinaryOwnerPieces c₃).map w1).sum ≤ 1 / 2 := by
        rw [p.ordinaryOwnerPieces_weight_sum]
        have indirect := w₃.indirect_le
        rw [n₃] at indirect
        linarith
      exact caseI_CCCD_demoted_third_weight_budget _ _ _ _ _ _ _ _ _ _ fits ordered₁ ordered₂
        ⟨q₁Lo, q₁Hi⟩ ⟨vLo, vHi⟩ q₁Size vSize weight₁ weight₂ weight₃ valid perm
    · obtain ⟨q₃, q₃At, q₃Lo, q₃Hi⟩ := p.retained_C_terminal c₃ upper₃ z₃ (lt_of_not_ge demoted)
      have third : (p.ordinaryOwnerPieces c₃).Perm [residualSize q₃, residualSize u₃] := by
        simpa [ordinaryDirectPieces, q₃At, u₃List] using p.ordinaryOwnerPieces_perm_direct_indirect c₃
      have initial : pieces.Perm [residualSize q₁, residualSize u₁,
          residualSize q₂, residualSize u₂, residualSize q₃, residualSize u₃, residualSize v] := by
        simpa [pieces] using first.append (second.append (third.append fourth))
      let ordered : Fin 7 → ℝ := ![residualSize q₁, residualSize v, residualSize q₃,
        residualSize u₃, residualSize q₂, residualSize u₁, residualSize u₂]
      have rearranged : [residualSize q₁, residualSize u₁, residualSize q₂, residualSize u₂,
          residualSize q₃, residualSize u₃, residualSize v].Perm
            [residualSize q₁, residualSize v, residualSize q₃, residualSize u₃,
              residualSize q₂, residualSize u₁, residualSize u₂] := by
        simpa [ordered] using ((by decide : List.Perm ([0, 5, 4, 6, 2, 3, 1] : List (Fin 7))
          [0, 1, 2, 3, 4, 5, 6]).map ordered)
      have q₃Mem := (p.ordinaryDirect_eq_some_iff c₃ q₃).mp q₃At
      have q₃Size := p.direct_size_le_of_extra_eq_zero c₃ q₃ q₃Mem z₃
      obtain ⟨head, deficit, headAt, owns, headPath⟩ := p.ordinaryIndirectPosition_head c₃ u₃ u₃Mem
      have greedy := p.ordinary_responsible_greedySlot c₃ deficit upper₃ owns
      have gap := p.uncharged_deficit_terminal_sum_lt_rejected v.val.val greedy headAt
        (Nat.le_of_not_gt q₃.property) (Nat.le_of_not_gt u₃.property)
        (p.ordinary_uncharged_of_extra_eq_zero c₃ q₃
          ((p.mem_ordinaryDirectPositions_iff c₃ q₃).mp q₃Mem).1 z₃)
        (p.ordinary_uncharged_of_extra_eq_zero c₃ u₃
          ((p.mem_ordinaryIndirectPositions_iff c₃ u₃).mp u₃Mem).1 z₃)
        (p.ordinaryDirectPosition_path c₃ q₃ q₃Mem) headPath
      refine caseI_CCCD_saturated_weight_budget _ _ _ _ _ _ _ _ _ _ _ _ fits ordered₁ ordered₂
        ?_ ?_ q₁Size q₃Size vSize gap.le valid (initial.trans rearranged)
      · intro x hx
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨q₁Lo, q₁Hi⟩
        · exact ⟨q₂Lo, q₂Hi⟩
        · exact ⟨q₃Lo, q₃Hi⟩
      · intro x hx
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact ⟨vLo, vHi⟩
        · exact ⟨u₁Lo, u₁Hi⟩
        · exact ⟨u₂Lo, u₂Hi⟩
        · exact ⟨u₃Lo, u₃Hi⟩
  unfold ordinaryGroupCost
  rw [allCredit]
  change W pieces - 2 / 9 * 3 ≤ 11 / 9
  linarith

theorem ordinary_CCCD_budget (c₁ c₂ c₃ d : NonLargePosition S)
    (upper₁ : S.get c₁.val ≤ 1 / 3) (upper₂ : S.get c₂.val ≤ 1 / 3)
    (c₃Size : 1 / 4 < S.get c₃.val ∧ S.get c₃.val ≤ 1 / 3)
    (upperD : S.get d.val ≤ 1 / 4)
    (ordered₁ : S.get c₃.val ≤ S.get c₁.val) (ordered₂ : S.get c₃.val ≤ S.get c₂.val)
    (fits : S.get c₁.val + S.get c₂.val + S.get c₃.val + S.get d.val ≤ 1)
    (w₁ : (p.ordinaryWeights c₁).Admissible true .C)
    (w₂ : (p.ordinaryWeights c₂).Admissible true .C)
    (w₃ : (p.ordinaryWeights c₃).Admissible true .C)
    (wD : (p.ordinaryWeights d).Admissible true .D)
    (pair : ObeysRelation (S.get c₃.val) (S.get d.val) →
      W (p.ordinaryDirectPieces c₃ ++ p.ordinaryDirectPieces d) ≤
        (p.ordinaryWeights c₃).direct + (2 / 3 : ℝ) * (p.ordinaryWeights d).direct ∨
      (p.ordinaryWeights c₃).direct ≤ 1 / 4 ∨ (2 / 3 : ℝ) ≤ (p.ordinaryWeights d).extra) :
    p.ordinaryGroupCost [c₁, c₂, c₃, d] ≤ 11 / 9 := by
  let weights : Fin 4 → ResponsibilityWeights :=
    ![p.ordinaryWeights c₁, p.ordinaryWeights c₂, p.ordinaryWeights c₃, p.ordinaryWeights d]
  by_cases charged : ∃ i, (2 / 3 : ℝ) ≤ (weights i).extra
  · have adm (i : Fin 4) : (weights i).Admissible true (![.C, .C, .C, .D] i) := by
      fin_cases i
      · exact w₁
      · exact w₂
      · exact w₃
      · exact wD
    have checked := caseI_CCCD_singleton_budget_of_charge weights adm charged
    exact (p.ordinaryGroupCost_le_singleton_costs [c₁, c₂, c₃, d]).trans (by
      simpa [weights, Fin.sum_univ_four, add_assoc] using checked)
  have zero (i : Fin 4) : (weights i).extra = 0 := by
    fin_cases i
    · exact (p.ordinary_extra_discrete c₁).resolve_right (fun positive => charged ⟨0, positive⟩)
    · exact (p.ordinary_extra_discrete c₂).resolve_right (fun positive => charged ⟨1, positive⟩)
    · exact (p.ordinary_extra_discrete c₃).resolve_right (fun positive => charged ⟨2, positive⟩)
    · exact (p.ordinary_extra_discrete d).resolve_right (fun positive => charged ⟨3, positive⟩)
  by_cases refined :
    ((p.ordinaryWeights c₁).direct ≤ 1 / 4 ∨
      (p.ordinaryWeights c₁).indirect ≤ ((p.ordinaryWeights c₁).count : ℝ) / 5) ∨
    ((p.ordinaryWeights c₂).direct ≤ 1 / 4 ∨
      (p.ordinaryWeights c₂).indirect ≤ ((p.ordinaryWeights c₂).count : ℝ) / 5) ∨
    ((p.ordinaryWeights c₃).indirect ≤ ((p.ordinaryWeights c₃).count : ℝ) / 5 ∨
      (p.ordinaryWeights d).direct ≤ 1 / 5)
  · calc
      p.ordinaryGroupCost [c₁, c₂, c₃, d] ≤
          p.ordinaryGroupCost [c₁, c₂] + p.ordinaryGroupCost [c₃, d] :=
        p.ordinaryGroupCost_append_le [c₁, c₂] [c₃, d]
      _ ≤ _ := by
        have first := p.ordinaryGroupCost_le_singleton_costs [c₁, c₂]
        have second := p.ordinaryGroupCost_pair_le_of_direct c₃ d
        have checked := caseI_CCCD_refined_pair_budget _ _ _ _ _ _ _ _ _
          c₃Size ordered₁ ordered₂ fits w₁ w₂ w₃ wD (p.direct_pair_weight_le_plain c₃ d)
          pair refined
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at first
        linarith
  · push Not at refined
    exact p.ordinary_CCCD_uncharged_budget c₁ c₂ c₃ d upper₁ upper₂ c₃Size.2 upperD
      ordered₁ ordered₂ fits w₁ w₂ w₃ wD (zero 0) (zero 1) (zero 2) (zero 3)
      refined.1.1 refined.2.1.1 refined.2.2.2 refined.1.2 refined.2.1.2 refined.2.2.1

end

end BinPacking.Decreasing.AlignedPacking

end

/- assembly/OrdinaryIndirectSizes.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

open PieceChains

variable {S : List ℝ} (p : AlignedPacking S)

/-- Claim 5.9.20. An indirect terminal of any ordinary non-B owner is
E-sized if a B-piece of size at most two fifths is in the greedy residual. -/
theorem ordinary_indirect_terminal_lt_fifth (owner : NonLargePosition S)
    (small : S.get owner.val ≤ 1 / 3) (residualB : ResidualPosition S)
    (smallB : (1 / 3 : ℝ) < S.get residualB.val.val ∧ S.get residualB.val.val ≤ 2 / 5)
    (terminal : ↥p.indirectTerminals)
    (owned : p.owner ⟨terminal.val, p.indirectTerminals_outside terminal⟩ = ordinaryOwner owner) :
    S.get terminal.val.val < 1 / 5 := by
  classical
  obtain ⟨head, deficit, slot, path⟩ := (Finset.mem_filter.mp terminal.property).2.2
  let d : p.Deficit := ⟨(p.smallOptimalSlot head).1, deficit⟩
  have optThird : p.smallOptimalSlot head = (d.val, 2) := Prod.ext rfl slot
  have isHead : IsHead p.points head := fun previous arrow =>
    d.property.2.2 previous (arrow.2.trans optThird)
  have origin : p.origin head = .inr d := (slotOrigin_eq_inr_iff
    smallGreedySlot p.smallOptimalSlot (isLargeBin S)
    (fun item _ => ordinaryOwner item) (fun bin inside _ => largeOwner bin inside) head d).mpr rfl
  obtain ⟨responsible, responsibleFor, _⟩ := existsUnique_responsible p.predecessor p.predecessor_noThree d
  have actual := (p.owner_eq_iff ⟨terminal.val, p.indirectTerminals_outside terminal⟩ responsible).mpr
    ⟨⟨head, isHead⟩, path, by
      change ownsHead p.predecessor (p.origin head) responsible
      rw [origin]
      exact responsibleFor⟩
  have owns : ResponsibleFor p.predecessor (ordinaryOwner owner) d :=
    (actual.symm.trans owned) ▸ responsibleFor
  have greedySecond := p.ordinary_responsible_greedySlot owner d small owns
  exact p.terminal_lt_fifth_of_small_residual_B residualB.val head terminal.val
    (Nat.le_of_not_gt residualB.property) smallB ⟨d.val, d.property.1⟩ owner optThird greedySecond
    small (Nat.le_of_not_gt (p.indirectTerminals_outside terminal)) path

end BinPacking.Decreasing.AlignedPacking

end

/- chains/OrdinaryTightGap.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

noncomputable section

variable {S : List ℝ} (p : AlignedPacking S)

/-- The tight gap in Case II forces each uncharged indirect terminal to have size below one fifth.
The candidate may be any occurrence because the terminal arrival is the smallest input item. -/
theorem ordinaryIndirectWeight_le_fifth_of_tightGap (owner : NonLargePosition S)
    (candidate : Fin S.length) (small : S.get owner.val ≤ 1 / 3)
    (gap : S.get owner.val + S.get candidate ≤ 2 / 5)
    (uncharged : (p.ordinaryWeights owner).extra = 0) :
    (p.ordinaryWeights owner).indirect ≤ ((p.ordinaryWeights owner).count : ℝ) / 5 := by
  change p.ordinaryIndirectWeight owner ≤ ((p.ordinaryIndirectPositions owner).card : ℝ) / 5
  apply p.ordinaryIndirectWeight_le_count owner 5 (by decide)
  intro r member
  have noCharge : r.val ∉ p.thirdSlotTerminals := fun charged => by
    have positive := p.ordinary_extra_ge_of_mem owner r
      ((p.mem_ordinaryIndirectPositions_iff owner r).mp member).1 charged
    linarith only [uncharged, positive]
  obtain ⟨head, d, third, owned, path⟩ := p.ordinaryIndirectPosition_head owner r member
  exact (p.uncharged_deficit_terminal_lt_fifth candidate third
    (p.ordinary_responsible_greedySlot owner d small owned) gap
    (Nat.le_of_not_gt r.property) noCharge path).le

end

end BinPacking.Decreasing.AlignedPacking

end

/- chains/OrdinaryCaseII.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

noncomputable section

variable {S : List ℝ} (p : AlignedPacking S)

local notation "size" => (fun i : NonLargePosition S => List.get S (Subtype.val i))
local notation "classOf" => smallPieceClass ∘ size

include p in
private theorem bounds_of_D (item : NonLargePosition S) (classEq : classOf item = .D) :
    1 / 5 < size item ∧ size item ≤ 1 / 4 := by
  have bounds := smallPieceClass_bounds (p.threshold _ (List.get_mem _ item.val))
    (p.ordinary_size_le_half item)
  change smallPieceClass (size item) = .D at classEq
  rw [classEq] at bounds
  exact bounds

include p in
private theorem lower_of_B (item : NonLargePosition S) (classEq : classOf item = .B) :
    1 / 3 < size item := by
  have bounds := smallPieceClass_bounds (p.threshold _ (List.get_mem _ item.val))
    (p.ordinary_size_le_half item)
  change smallPieceClass (size item) = .B at classEq
  rw [classEq] at bounds
  exact bounds.1

private theorem admissible_caseII (noC : ¬HasResidualC S)
    (residualCD : ∃ r : ResidualPosition S, (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3)
    (item : NonLargePosition S) (kind : SmallPieceClass) (classEq : classOf item = kind) :
    (p.ordinaryWeights item).Admissible false kind := by
  subst kind
  exact p.ordinaryWeights_admissible item false _
    ⟨fun impossible => ((by decide : false ≠ true) impossible).elim, fun found => (noC found).elim⟩
    residualCD (smallPieceClass_bounds (p.threshold _ (List.get_mem _ item.val))
      (p.ordinary_size_le_half item))

private def directSize (item : NonLargePosition S) : Option ℝ :=
  (p.ordinaryDirect item).map residualSize

private theorem direct_weight_eq_zero (item : NonLargePosition S) (absent : p.directSize item = none) :
    (p.ordinaryWeights item).direct = 0 := by
  cases observed : p.ordinaryDirect item with
  | none => simp [ordinaryWeights, ordinaryDirectWeight, observed]
  | some r => simp [directSize, observed] at absent

private theorem directSize_le_of_no_charge (item : NonLargePosition S) (x : ℝ)
    (direct : p.directSize item = some x) (uncharged : (p.ordinaryWeights item).extra = 0) :
    x ≤ size item := by
  obtain ⟨r, observed, rfl⟩ := Option.map_eq_some_iff.mp direct
  exact p.direct_size_le_of_extra_eq_zero item r ((p.ordinaryDirect_eq_some_iff item r).mp observed)
    uncharged

private theorem indirectWeight_le_fifth_of_direct_gap (item other : NonLargePosition S)
    (small : size item ≤ 1 / 3) (x : ℝ) (direct : p.directSize other = some x)
    (uncharged : (p.ordinaryWeights item).extra = 0) (gap : size item + x ≤ 2 / 5) :
    (p.ordinaryWeights item).indirect ≤ ((p.ordinaryWeights item).count : ℝ) / 5 := by
  obtain ⟨r, _, rfl⟩ := Option.map_eq_some_iff.mp direct
  exact p.ordinaryIndirectWeight_le_fifth_of_tightGap item r.val.val small gap uncharged

private theorem indirectWeight_le_fifth_of_small_residual_B (item : NonLargePosition S)
    (small : size item ≤ 1 / 3) (r : ResidualPosition S)
    (smallB : (1 / 3 : ℝ) < residualSize r ∧ residualSize r ≤ 2 / 5) :
    (p.ordinaryWeights item).indirect ≤ ((p.ordinaryWeights item).count : ℝ) / 5 := by
  change p.ordinaryIndirectWeight item ≤ ((p.ordinaryIndirectPositions item).card : ℝ) / 5
  apply p.ordinaryIndirectWeight_le_count item 5 (by decide)
  intro terminal member
  obtain ⟨owner, indirect⟩ := (p.mem_ordinaryIndirectPositions_iff item terminal).mp member
  exact (p.ordinary_indirect_terminal_lt_fifth item small r smallB ⟨terminal.val, indirect⟩ owner).le

private theorem caseII_B_direct (noC : ¬HasResidualC S) (b d₂ d₃ : NonLargePosition S)
    (large : (1 / 3 : ℝ) < size b) (d₂Small : size d₂ ≤ 1 / 3) (d₃Small : size d₃ ≤ 1 / 3) :
    (p.ordinaryWeights b).direct ≤ 1 / 4 ∨
      ∃ directB : ℝ, directB ≤ size b ∧ (directB ≤ 2 / 5 →
        (p.ordinaryWeights d₂).indirect ≤ ((p.ordinaryWeights d₂).count : ℝ) / 5 ∧
        (p.ordinaryWeights d₃).indirect ≤ ((p.ordinaryWeights d₃).count : ℝ) / 5) := by
  cases observed : p.ordinaryDirect b with
  | none =>
    exact .inl (by simp [ordinaryWeights, ordinaryDirectWeight, observed])
  | some r =>
    have member := (p.ordinaryDirect_eq_some_iff b r).mp observed
    by_cases retained : (1 / 3 : ℝ) < residualSize r
    · refine Or.inr ⟨residualSize r, ?_, fun upper => ?_⟩
      · exact (p.direct_size_le_max_of_mem b r member).trans (max_le le_rfl (by linarith))
      · exact ⟨p.indirectWeight_le_fifth_of_small_residual_B d₂ d₂Small r ⟨retained, upper⟩,
          p.indirectWeight_le_fifth_of_small_residual_B d₃ d₃Small r ⟨retained, upper⟩⟩
    · left
      change p.ordinaryDirectWeight b ≤ 1 / 4
      simpa [ordinaryDirectWeight, observed, residualSize] using w1_le_inverse_of_le
        (p.valid _ (List.get_mem S r.val.val)).1 (k := 4) (by decide)
        (residual_size_le_quarter_of_le_third noC r (le_of_not_gt retained))

private theorem ordinaryGroupCost_ofFn_le {n : ℕ} (owners : Fin n → NonLargePosition S)
    (bound : (∑ j, (p.ordinaryWeights (owners j)).weightedCost 1) ≤ 11 / 9) :
    p.ordinaryGroupCost (List.ofFn owners) ≤ 11 / 9 := by
  apply (p.ordinaryGroupCost_le_singleton_costs (List.ofFn owners)).trans
  rwa [List.map_ofFn, List.sum_ofFn]

private theorem ordinaryGroupCost_BDDE_le (noC : ¬HasResidualC S)
    (residualCD : ∃ r : ResidualPosition S, (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3)
    (b d₂ d₃ e : NonLargePosition S)
    (bClass : classOf b = .B) (d₂Class : classOf d₂ = .D)
    (d₃Class : classOf d₃ = .D) (eClass : classOf e = .E)
    (fits : size b + size d₂ + size d₃ + size e ≤ 1) :
    p.ordinaryGroupCost [b, d₂, d₃, e] ≤ 11 / 9 := by
  let owners : Fin 4 → NonLargePosition S := ![b, d₂, d₃, e]
  let r := p.ordinaryWeights ∘ owners
  have admissible : ∀ i, (r i).Admissible false (![.B, .D, .D, .E] i) := by
    intro i
    apply p.admissible_caseII noC residualCD
    fin_cases i
    · exact bClass
    · exact d₂Class
    · exact d₃Class
    · exact eClass
  have d₂Bounds := p.bounds_of_D d₂ d₂Class
  have d₃Bounds := p.bounds_of_D d₃ d₃Class
  have d₂Small : size d₂ ≤ 1 / 3 := d₂Bounds.2.trans (by norm_num)
  have d₃Small : size d₃ ≤ 1 / 3 := d₃Bounds.2.trans (by norm_num)
  have budget := caseII_BDDE_singleton_budget (size b) (size d₂) (size d₃) (size e) r
    (p.directSize e) d₂Bounds.1 d₃Bounds.1 fits admissible (fun i => p.ordinary_extra_discrete (owners i))
    (p.caseII_B_direct noC b d₂ d₃ (p.lower_of_B b bClass) d₂Small d₃Small)
    (p.direct_weight_eq_zero e) (p.directSize_le_of_no_charge e)
    (p.indirectWeight_le_fifth_of_direct_gap d₂ e d₂Small)
    (p.indirectWeight_le_fifth_of_direct_gap d₃ e d₃Small)
  simpa [owners, List.ofFn_succ] using p.ordinaryGroupCost_ofFn_le owners budget

private theorem ordinaryGroupCost_DDDEE_le (noC : ¬HasResidualC S)
    (residualCD : ∃ r : ResidualPosition S, (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3)
    (d₁ d₂ d₃ e₄ e₅ : NonLargePosition S)
    (d₁Class : classOf d₁ = .D) (d₂Class : classOf d₂ = .D) (d₃Class : classOf d₃ = .D)
    (e₄Class : classOf e₄ = .E) (e₅Class : classOf e₅ = .E)
    (fits : size d₁ + size d₂ + size d₃ + size e₄ + size e₅ ≤ 1) :
    p.ordinaryGroupCost [d₁, d₂, d₃, e₄, e₅] ≤ 11 / 9 := by
  let owners : Fin 5 → NonLargePosition S := ![d₁, d₂, d₃, e₄, e₅]
  let r := p.ordinaryWeights ∘ owners
  have admissible : ∀ i, (r i).Admissible false (![.D, .D, .D, .E, .E] i) := by
    intro i
    apply p.admissible_caseII noC residualCD
    fin_cases i
    · exact d₁Class
    · exact d₂Class
    · exact d₃Class
    · exact e₄Class
    · exact e₅Class
  have d₁Small : size d₁ ≤ 1 / 3 := (p.bounds_of_D d₁ d₁Class).2.trans (by norm_num)
  have d₂Small : size d₂ ≤ 1 / 3 := (p.bounds_of_D d₂ d₂Class).2.trans (by norm_num)
  have budget := caseII_DDDEE_singleton_budget (size d₁) (size d₂) (size d₃) (size e₄) (size e₅)
    r (p.directSize e₄) (p.directSize e₅) (p.bounds_of_D d₃ d₃Class).1 fits admissible
    (fun i => p.ordinary_extra_discrete (owners i))
    (p.direct_weight_eq_zero e₄) (p.direct_weight_eq_zero e₅)
    (p.directSize_le_of_no_charge e₄) (p.directSize_le_of_no_charge e₅)
    (p.indirectWeight_le_fifth_of_direct_gap d₁ e₄ d₁Small)
    (p.indirectWeight_le_fifth_of_direct_gap d₂ e₅ d₂Small)
  simpa [owners, List.ofFn_succ] using p.ordinaryGroupCost_ofFn_le owners budget

private theorem ordinaryGroupCost_DDDDE_le (noC : ¬HasResidualC S)
    (residualCD : ∃ r : ResidualPosition S, (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3)
    (d₁ d₂ d₃ d₄ e : NonLargePosition S)
    (d₁Class : classOf d₁ = .D) (d₂Class : classOf d₂ = .D)
    (d₃Class : classOf d₃ = .D) (d₄Class : classOf d₄ = .D) (eClass : classOf e = .E)
    (fits : size d₁ + size d₂ + size d₃ + size d₄ + size e ≤ 1) :
    p.ordinaryGroupCost [d₁, d₂, d₃, d₄, e] ≤ 11 / 9 := by
  let owners : Fin 5 → NonLargePosition S := ![d₁, d₂, d₃, d₄, e]
  let r := p.ordinaryWeights ∘ owners
  have admissible : ∀ i, (r i).Admissible false (![.D, .D, .D, .D, .E] i) := by
    intro i
    apply p.admissible_caseII noC residualCD
    fin_cases i
    · exact d₁Class
    · exact d₂Class
    · exact d₃Class
    · exact d₄Class
    · exact eClass
  have dBounds (i : Fin 4) : 1 / 5 < size (owners i.castSucc) ∧ size (owners i.castSucc) ≤ 1 / 4 := by
    apply p.bounds_of_D
    fin_cases i
    · exact d₁Class
    · exact d₂Class
    · exact d₃Class
    · exact d₄Class
  let dSizes (i : Fin 4) := size (owners i.castSucc)
  have hfit : (∑ i, dSizes i) + size e ≤ 1 := by
    rw [Fin.sum_univ_four]
    exact fits
  have budget := caseII_DDDDE_singleton_budget dSizes (size e) r (p.directSize e)
    (fun i => (dBounds i).1) hfit admissible (fun i => p.ordinary_extra_discrete (owners i))
    (p.direct_weight_eq_zero e) (p.directSize_le_of_no_charge e)
    (fun i => p.indirectWeight_le_fifth_of_direct_gap (owners i.castSucc) e
      ((dBounds i).2.trans (by norm_num)))
  simpa [owners, List.ofFn_succ] using p.ordinaryGroupCost_ofFn_le owners budget

/-- The BDDE Case II configuration fits the ordinary-bin budget. -/
theorem ordinaryGroupCost_le_of_BDDE (noC : ¬HasResidualC S)
    (residualCD : ∃ r : ResidualPosition S, (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3)
    (owners : List (NonLargePosition S)) (shape : owners.map classOf = [.B, .D, .D, .E])
    (fits : (owners.map size).sum ≤ 1) : p.ordinaryGroupCost owners ≤ 11 / 9 := by
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  obtain ⟨b, _, rfl, bClass, d₂, _, rfl, d₂Class, d₃, _, rfl, d₃Class, e, _, rfl, eClass, rfl⟩ := shape
  exact p.ordinaryGroupCost_BDDE_le noC residualCD b d₂ d₃ e bClass d₂Class d₃Class eClass
    (by simpa [add_assoc] using fits)

/-- The DDDEE Case II configuration fits the ordinary-bin budget. -/
theorem ordinaryGroupCost_le_of_DDDEE (noC : ¬HasResidualC S)
    (residualCD : ∃ r : ResidualPosition S, (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3)
    (owners : List (NonLargePosition S)) (shape : owners.map classOf = [.D, .D, .D, .E, .E])
    (fits : (owners.map size).sum ≤ 1) : p.ordinaryGroupCost owners ≤ 11 / 9 := by
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  obtain ⟨d₁, _, rfl, d₁Class, d₂, _, rfl, d₂Class, d₃, _, rfl, d₃Class,
    e₄, _, rfl, e₄Class, e₅, _, rfl, e₅Class, rfl⟩ := shape
  exact p.ordinaryGroupCost_DDDEE_le noC residualCD d₁ d₂ d₃ e₄ e₅
    d₁Class d₂Class d₃Class e₄Class e₅Class (by simpa [add_assoc] using fits)

/-- The DDDDE Case II configuration fits the ordinary-bin budget. -/
theorem ordinaryGroupCost_le_of_DDDDE (noC : ¬HasResidualC S)
    (residualCD : ∃ r : ResidualPosition S, (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3)
    (owners : List (NonLargePosition S)) (shape : owners.map classOf = [.D, .D, .D, .D, .E])
    (fits : (owners.map size).sum ≤ 1) : p.ordinaryGroupCost owners ≤ 11 / 9 := by
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  obtain ⟨d₁, _, rfl, d₁Class, d₂, _, rfl, d₂Class, d₃, _, rfl, d₃Class,
    d₄, _, rfl, d₄Class, e, _, rfl, eClass, rfl⟩ := shape
  exact p.ordinaryGroupCost_DDDDE_le noC residualCD d₁ d₂ d₃ d₄ e
    d₁Class d₂Class d₃Class d₄Class eClass (by simpa [add_assoc] using fits)

/-- The three exceptional Case II configurations fit the ordinary-bin budget. -/
theorem ordinaryGroupCost_le_of_caseII_exception (noC : ¬HasResidualC S)
    (residualCD : ∃ r : ResidualPosition S, (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3)
    (owners : List (NonLargePosition S)) (shape : owners.map classOf ∈ exceptionalConfigurations false)
    (fits : (owners.map size).sum ≤ 1) : p.ordinaryGroupCost owners ≤ 11 / 9 := by
  simp only [exceptionalConfigurations, List.mem_cons, List.not_mem_nil, or_false] at shape
  rcases shape with bdde | dddee | dddde
  · exact p.ordinaryGroupCost_le_of_BDDE noC residualCD owners bdde fits
  · exact p.ordinaryGroupCost_le_of_DDDEE noC residualCD owners dddee fits
  · exact p.ordinaryGroupCost_le_of_DDDDE noC residualCD owners dddde fits

end

end BinPacking.Decreasing.AlignedPacking

end

/- small-only/OrdinaryPair.lean -/
section

set_option autoImplicit false

namespace BinPacking.Decreasing.AlignedPacking

noncomputable section

variable {S : List ℝ} (p : AlignedPacking S)

private def classLower : SmallPieceClass → ℝ
  | .B => 1 / 3
  | .C => 1 / 4
  | .D => 1 / 5
  | .E => 2 / 11

private def classUpper : SmallPieceClass → ℝ
  | .B => 1 / 2
  | .C => 1 / 3
  | .D => 1 / 4
  | .E => 1 / 5

private def classPieceNum : SmallPieceClass → ℤ
  | .B => 2
  | .C => 3
  | .D => 4
  | .E => 5

include p in
private theorem owner_class_bounds (i : NonLargePosition S) :
    classLower (smallPieceClass (S.get i.val)) < S.get i.val ∧
      S.get i.val ≤ classUpper (smallPieceClass (S.get i.val)) := by
  have bounds := smallPieceClass_bounds (p.threshold _ (List.get_mem S i.val))
    (p.ordinary_size_le_half i)
  cases h : smallPieceClass (S.get i.val) <;> rw [h] at bounds <;> exact bounds

private theorem row_class_order {hasC : Bool} {left right : SmallPieceClass} {allowance : ℝ}
    (row : pairAllowance hasC left right = some allowance) :
    left ≠ .E ∧ classUpper right ≤ classLower left := by
  cases hasC <;> cases left <;> cases right <;> simp [pairAllowance] at row
  all_goals exact ⟨by decide, by norm_num [classLower, classUpper]⟩

private theorem pieceNum_of_class_bounds {kind : SmallPieceClass} {x : ℝ}
    (eligible : kind ≠ .E) (lower : classLower kind < x) (upper : x ≤ classUpper kind) :
    pieceNum x = classPieceNum kind := by
  cases kind with
  | B => exact pieceNum_B lower upper
  | C => exact pieceNum_C lower upper
  | D => exact pieceNum_D lower upper
  | E => contradiction

private theorem pairFactor_eq_classPieceNum (kind : SmallPieceClass) :
    pairFactor kind = ((classPieceNum kind : ℝ) - 1) / (classPieceNum kind : ℝ) := by
  cases kind <;> norm_num [pairFactor, classPieceNum]

private theorem ordinary_direct_eq_of_some (i : NonLargePosition S) (r : ResidualPosition S)
    (direct : p.ordinaryDirect i = some r) : (p.ordinaryWeights i).direct = w1 (residualSize r) := by
  simp [ordinaryWeights, ordinaryDirectWeight, direct]

private theorem ordinary_direct_eq_zero_of_none (i : NonLargePosition S)
    (direct : p.ordinaryDirect i = none) : (p.ordinaryWeights i).direct = 0 := by
  simp [ordinaryWeights, ordinaryDirectWeight, direct]

private theorem direct_size_le_owner_or_charged (i : NonLargePosition S) (r : ResidualPosition S)
    (direct : r ∈ p.ordinaryDirectPositions i) : residualSize r ≤ S.get i.val ∨
      ((smallPieceClass (S.get i.val) = .D ∨ smallPieceClass (S.get i.val) = .E) ∧
        (2 / 3 : ℝ) ≤ (p.ordinaryWeights i).extra) := by
  by_cases within : residualSize r ≤ S.get i.val
  · exact .inl within
  have tooLarge := lt_of_not_ge within
  have belowQuarter : S.get i.val < 1 / 4 := by
    rcases le_max_iff.mp (p.direct_size_le_max_of_mem i r direct) with bound | bound
    · exact (within bound).elim
    · exact tooLarge.trans_le bound
  have notB : ¬(1 / 3 : ℝ) < S.get i.val := by linarith only [belowQuarter]
  have notC : ¬(1 / 4 : ℝ) < S.get i.val := by linarith only [belowQuarter]
  right
  refine ⟨?_, (p.ordinary_extra_discrete i).resolve_left (fun zero =>
    within (p.direct_size_le_of_extra_eq_zero i r direct zero))⟩
  rw [smallPieceClass, if_neg notB, if_neg notC]
  split <;> simp

include p in
private theorem weight_le_unpromoted (hasC : Bool) (kind : SmallPieceClass)
    (noC : hasC = false → ¬HasResidualC S) (r : ResidualPosition S)
    (small : residualSize r ≤ classUpper kind) :
    w1 (residualSize r) ≤ unpromotedWeightLimit hasC kind := by
  have pos : 0 < residualSize r := (p.valid _ (List.get_mem S r.val.val)).1
  cases kind with
  | B => simpa [unpromotedWeightLimit, directWeightLimit] using
      w1_le_inverse_of_le pos (k := 2) (by decide) (by simpa [classUpper] using small)
  | C =>
    cases h : hasC
    · simpa [unpromotedWeightLimit, directWeightLimit] using
        w1_le_inverse_of_le pos (k := 4) (by decide) (by
          simpa using residual_size_le_quarter_of_le_third (noC h) r small)
    · simpa [unpromotedWeightLimit, directWeightLimit] using
        w1_le_inverse_of_le pos (k := 3) (by decide) (by simpa [classUpper] using small)
  | D => simpa [unpromotedWeightLimit, directWeightLimit] using
      w1_le_inverse_of_le pos (k := 4) (by decide) (by simpa [classUpper] using small)
  | E => simpa [unpromotedWeightLimit] using
      w1_le_inverse_of_le pos (k := 5) (by decide) (by simpa [classUpper] using small)

include p in
private theorem weight_le_demoted (hasC : Bool) (kind : SmallPieceClass)
    (noC : hasC = false → ¬HasResidualC S) (eligible : kind ≠ .E)
    (r : ResidualPosition S) (small : residualSize r ≤ classLower kind) :
    w1 (residualSize r) ≤ demotedWeightLimit hasC kind := by
  cases kind with
  | B => simpa [demotedWeightLimit, unpromotedWeightLimit, directWeightLimit] using
      p.weight_le_unpromoted hasC .C noC r small
  | C => simpa [demotedWeightLimit, unpromotedWeightLimit, directWeightLimit] using
      p.weight_le_unpromoted hasC .D noC r small
  | D => simpa [demotedWeightLimit, unpromotedWeightLimit] using
      p.weight_le_unpromoted hasC .E noC r small
  | E => contradiction

private theorem retained_count_le (hasC : Bool) (a : NonLargePosition S)
    (count : (p.ordinaryWeights a).count ≤ indirectCountLimit hasC (smallPieceClass (S.get a.val)))
    (r : ResidualPosition S) (direct : r ∈ p.ordinaryDirectPositions a)
    (retained : classLower (smallPieceClass (S.get a.val)) < residualSize r) :
    (p.ordinaryWeights a).count ≤ matchingCountLimit hasC (smallPieceClass (S.get a.val)) := by
  cases h : smallPieceClass (S.get a.val) with
  | B =>
    have zero : (p.ordinaryWeights a).count = 0 := by
      by_contra positive
      have positiveCard : 0 < (p.ordinaryIndirectPositions a).card := Nat.pos_of_ne_zero positive
      obtain ⟨indirect, mem⟩ := Finset.card_pos.mp positiveCard
      have small := p.ordinary_direct_lt_third_of_indirect a direct mem
      rw [h] at retained
      exact (not_lt_of_ge small.le) retained
    simp [matchingCountLimit, zero]
  | C | D | E => simpa only [matchingCountLimit, h] using count

private theorem classified_ordinaryWeights_admissible (i : NonLargePosition S) (hasC : Bool)
    (case_iff : hasC = true ↔ HasResidualC S)
    (residualCD : ∃ r : ResidualPosition S, (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3) :
    (p.ordinaryWeights i).Admissible hasC (smallPieceClass (S.get i.val)) :=
  p.ordinaryWeights_admissible i hasC _ case_iff residualCD
    (smallPieceClass_bounds (p.threshold _ (List.get_mem S i.val)) (p.ordinary_size_le_half i))

/-- The four outcomes of a discount for a pair of actual ordinary owners. -/
theorem ordinary_pair_alternatives (a b : NonLargePosition S) (hasC : Bool) (allowance : ℝ)
    (case_iff : hasC = true ↔ HasResidualC S)
    (residualCD : ∃ r : ResidualPosition S, (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3)
    (row : pairAllowance hasC (smallPieceClass (S.get a.val)) (smallPieceClass (S.get b.val)) = some allowance)
    (relation : ObeysRelation (S.get a.val) (S.get b.val)) :
    let left := smallPieceClass (S.get a.val)
    let right := smallPieceClass (S.get b.val)
    let x := p.ordinaryWeights a
    let y := p.ordinaryWeights b
    (W (p.ordinaryDirectPieces a ++ p.ordinaryDirectPieces b) ≤ x.direct + pairFactor left * y.direct ∧
      x.direct ≤ unpromotedWeightLimit hasC left ∧ y.direct ≤ unpromotedWeightLimit hasC right ∧
      x.count ≤ matchingCountLimit hasC left) ∨
    x.direct ≤ demotedWeightLimit hasC left ∨
    ((left = .D ∨ left = .E) ∧ 2 / 3 ≤ x.extra) ∨
    ((right = .D ∨ right = .E) ∧ 2 / 3 ≤ y.extra) := by
  intro left right x y
  have noC (h : hasC = false) : ¬HasResidualC S := fun yes => by
    simpa only [h, Bool.false_eq_true] using case_iff.mpr yes
  obtain ⟨eligible, classOrder⟩ := row_class_order row
  cases ha : p.ordinaryDirect a with
  | none =>
    refine .inr (.inl ?_)
    rw [show x.direct = 0 from p.ordinary_direct_eq_zero_of_none a ha]
    cases hasC <;> cases left <;> norm_num [demotedWeightLimit]
  | some u =>
    by_cases demoted : residualSize u ≤ classLower left
    · refine .inr (.inl ?_)
      rw [show x.direct = w1 (residualSize u) from p.ordinary_direct_eq_of_some a u ha]
      exact p.weight_le_demoted hasC left noC eligible u demoted
    · have memU := (p.ordinaryDirect_eq_some_iff a u).mp ha
      rcases p.direct_size_le_owner_or_charged a u memU with unpromotedU | charged
      · have aBounds := p.owner_class_bounds a
        have weightU : x.direct = w1 (residualSize u) := p.ordinary_direct_eq_of_some a u ha
        have leftLimit : x.direct ≤ unpromotedWeightLimit hasC left := by
          rw [weightU]
          exact p.weight_le_unpromoted hasC left noC u (unpromotedU.trans aBounds.2)
        have count := p.retained_count_le hasC a
          (p.classified_ordinaryWeights_admissible a hasC case_iff residualCD).count_le u memU
          (lt_of_not_ge demoted)
        cases hb : p.ordinaryDirect b with
        | none =>
          have zero : y.direct = 0 := p.ordinary_direct_eq_zero_of_none b hb
          refine .inl ⟨?_, leftLimit, ?_, count⟩
          · rw [weightU, zero]
            simpa [ordinaryDirectPieces, ha, hb] using weight_le_singleton_sum [residualSize u]
          · rw [zero]
            cases hasC <;> cases right <;> norm_num [unpromotedWeightLimit, directWeightLimit]
        | some v =>
          have memV := (p.ordinaryDirect_eq_some_iff b v).mp hb
          rcases p.direct_size_le_owner_or_charged b v memV with unpromotedV | charged
          · have bBounds := p.owner_class_bounds b
            have weightV : y.direct = w1 (residualSize v) := p.ordinary_direct_eq_of_some b v hb
            refine .inl ⟨?_, leftLimit, ?_, count⟩
            · rw [weightU, weightV]
              simp only [ordinaryDirectPieces, ha, hb, Option.toList_some, List.map_cons,
                List.map_nil, List.cons_append, List.nil_append]
              have leftNum := pieceNum_of_class_bounds eligible aBounds.1 aBounds.2
              rw [pairFactor_eq_classPieceNum, ← leftNum]
              apply weight_pair_le_of_preserved_relation (S.get a.val) (S.get b.val)
                (residualSize u) (residualSize v) relation
              · exact (pieceNum_of_class_bounds eligible (lt_of_not_ge demoted)
                  (unpromotedU.trans aBounds.2)).trans leftNum.symm
              · rw [leftNum]
                change (0 : ℝ) ≤ (classPieceNum left : ℝ)
                cases left <;> norm_num [classPieceNum]
              · exact unpromotedU
              · exact unpromotedV
              · exact (unpromotedV.trans (bBounds.2.trans classOrder)).trans (lt_of_not_ge demoted).le
            · rw [weightV]
              exact p.weight_le_unpromoted hasC right noC v (unpromotedV.trans bBounds.2)
          · exact .inr (.inr (.inr charged))
      · exact .inr (.inr (.inl charged))

/-- Claim 5.9.26 for the actual residual responsibilities of two owners. -/
theorem ordinaryGroupCost_pair_le_allowance (a b : NonLargePosition S) (hasC : Bool) (allowance : ℝ)
    (case_iff : hasC = true ↔ HasResidualC S)
    (residualCD : ∃ r : ResidualPosition S, (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3)
    (row : pairAllowance hasC (smallPieceClass (S.get a.val)) (smallPieceClass (S.get b.val)) = some allowance)
    (relation : ObeysRelation (S.get a.val) (S.get b.val)) : p.ordinaryGroupCost [a, b] ≤ allowance :=
  (p.ordinaryGroupCost_pair_le_of_direct a b).trans
    (pair_cost_le_allowance hasC _ _ _ _ _ allowance row
      (p.classified_ordinaryWeights_admissible a hasC case_iff residualCD)
      (p.classified_ordinaryWeights_admissible b hasC case_iff residualCD)
      (p.direct_pair_weight_le_plain a b)
      (p.ordinary_pair_alternatives a b hasC allowance case_iff residualCD row relation))

end

end BinPacking.Decreasing.AlignedPacking

end

/- FinalBudget.lean -/
section

namespace BinPacking.Decreasing.AlignedPacking

variable {S : List ℝ} (p : AlignedPacking S)

private theorem ordinaryGroupCost_le_of_caseI_exception (hasC : HasResidualC S)
    (residualCD : ∃ r : ResidualPosition S, (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3)
    (owners : List (NonLargePosition S))
    (shape : (owners.map fun i => smallPieceClass (S.get i.val)) ∈ exceptionalConfigurations true)
    (sorted : owners.Pairwise (fun a b => S.get b.val ≤ S.get a.val))
    (fits : (owners.map fun i => S.get i.val).sum ≤ 1) : p.ordinaryGroupCost owners ≤ 11 / 9 := by
  have case_iff : true = true ↔ HasResidualC S := iff_of_true rfl hasC
  have intervals (a : NonLargePosition S) := smallPieceClass_bounds
    (p.threshold _ (List.get_mem S a.val)) (p.ordinary_size_le_half a)
  have allowed (a : NonLargePosition S) :=
    p.ordinaryWeights_admissible a true _ case_iff residualCD (intervals a)
  simp only [exceptionalConfigurations, List.mem_cons, List.mem_nil_iff, or_false] at shape
  rcases shape with bbc | cccd
  · simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at bbc
    obtain ⟨b₁, _, rfl, b₁Class, b₂, _, rfl, b₂Class, c, _, rfl, cClass, rfl⟩ := bbc
    refine p.ordinary_BBC_budget b₁ b₂ c (by simpa only [b₂Class] using intervals b₂)
      (by simpa only [cClass] using intervals c) ((List.pairwise_cons.mp sorted).1 b₂ (by simp))
      (by simpa [add_assoc] using fits) (by simpa only [b₁Class] using allowed b₁)
      (by simpa only [b₂Class] using allowed b₂) (by simpa only [cClass] using allowed c) ?_
    intro relation
    have row : pairAllowance true (smallPieceClass (S.get b₂.val)) (smallPieceClass (S.get c.val)) =
        some (3 / 4) := by rw [b₂Class, cClass]; rfl
    have alternatives := p.ordinary_pair_alternatives b₂ c true (3 / 4) case_iff residualCD row relation
    dsimp only at alternatives
    rw [b₂Class, cClass] at alternatives
    rcases alternatives with ⟨discount, _, _, count⟩ | demoted | left | right
    · exact .inl ⟨discount, Nat.eq_zero_of_le_zero count⟩
    · exact .inr demoted
    · rcases left.1 with h | h <;> cases h
    · rcases right.1 with h | h <;> cases h
  · simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at cccd
    obtain ⟨c₁, _, rfl, c₁Class, c₂, _, rfl, c₂Class, c₃, _, rfl, c₃Class, d, _, rfl, dClass, rfl⟩ := cccd
    have c₁Size : (1 / 4 : ℝ) < S.get c₁.val ∧ S.get c₁.val ≤ 1 / 3 := by
      simpa only [c₁Class] using intervals c₁
    have c₂Size : (1 / 4 : ℝ) < S.get c₂.val ∧ S.get c₂.val ≤ 1 / 3 := by
      simpa only [c₂Class] using intervals c₂
    have dSize : (1 / 5 : ℝ) < S.get d.val ∧ S.get d.val ≤ 1 / 4 := by
      simpa only [dClass] using intervals d
    refine p.ordinary_CCCD_budget c₁ c₂ c₃ d c₁Size.2 c₂Size.2
      (by simpa only [c₃Class] using intervals c₃) dSize.2
      ((List.pairwise_cons.mp sorted).1 c₃ (by simp))
      ((List.pairwise_cons.mp (List.pairwise_cons.mp sorted).2).1 c₃ (by simp))
      (by simpa [add_assoc] using fits) (by simpa only [c₁Class] using allowed c₁)
      (by simpa only [c₂Class] using allowed c₂) (by simpa only [c₃Class] using allowed c₃)
      (by simpa only [dClass] using allowed d) ?_
    intro relation
    have row : pairAllowance true (smallPieceClass (S.get c₃.val)) (smallPieceClass (S.get d.val)) =
        some (19 / 36) := by rw [c₃Class, dClass]; rfl
    have alternatives := p.ordinary_pair_alternatives c₃ d true (19 / 36) case_iff residualCD row relation
    dsimp only at alternatives
    rw [c₃Class, dClass] at alternatives
    rcases alternatives with ⟨discount, _, _, _⟩ | demoted | left | right
    · exact .inl discount
    · exact .inr (.inl demoted)
    · rcases left.1 with h | h <;> cases h
    · exact .inr (.inr right.2)

theorem nonLarge_bin_budget (bin : Fin (optBins S)) (nonLarge : bin ∉ binsWithLargeItems p.assign)
    (residualCD : ∃ r : ResidualPosition S, (1 / 5 : ℝ) < residualSize r ∧ residualSize r ≤ 1 / 3) :
    W (p.responsiblePieces bin) + p.credit bin ≤ (11 / 9 : ℝ) * (1 + p.credit bin) := by
  classical
  have outside : ¬isLargeBin S bin.val := fun inside =>
    nonLarge ((mem_aligned_binsWithLargeItems_iff_lt_count p.sorted p.assign p.aligned bin).mpr inside)
  let owners := p.ordinaryOwners bin outside
  have fits : (owners.map fun a => S.get a.val).sum ≤ 1 := by
    rw [p.ordinaryOwners_sizes bin outside, assignmentBin_sum]
    exact p.fits bin
  have sorted : owners.Pairwise (fun a b => S.get b.val ≤ S.get a.val) := by
    have sizesSorted := assignmentBin_sorted p.assign bin p.sorted
    rw [← p.ordinaryOwners_sizes bin outside] at sizesSorted
    exact List.pairwise_map.mp sizesSorted
  let hasC : Bool := decide (HasResidualC S)
  have case_iff : hasC = true ↔ HasResidualC S := Iff.of_eq decide_eq_true_eq
  apply p.nonLarge_bin_budget_of_configurations hasC bin outside case_iff residualCD
  · exact fun a _ b _ allowance => p.ordinaryGroupCost_pair_le_allowance a b hasC allowance case_iff residualCD
  · intro shape
    cases parity : hasC
    · have noC : ¬HasResidualC S := fun present => by simpa [parity] using case_iff.mpr present
      rw [parity] at shape
      exact p.ordinaryGroupCost_le_of_caseII_exception noC residualCD owners shape fits
    · rw [parity] at shape
      exact p.ordinaryGroupCost_le_of_caseI_exception (case_iff.mp parity) residualCD owners shape sorted fits

end BinPacking.Decreasing.AlignedPacking

open BinPacking.Decreasing in
theorem solution (L : List ℝ) (hL : IsList L) (h211 : ∀ a ∈ L, (2 / 11 : ℝ) < a) :
    (FFD L : ℝ) ≤ (11 / 9 : ℝ) * (optBins L : ℝ) + 4 :=
  ffd_le_of_nonLarge_bin_budget (fun _ p residualCD j nonLarge =>
    p.nonLarge_bin_budget j nonLarge residualCD) L hL h211

end

#print axioms solution
