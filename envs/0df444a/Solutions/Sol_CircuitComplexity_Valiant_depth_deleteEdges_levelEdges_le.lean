-- Prove2me | solution 1 for CircuitComplexity.Valiant.depth_deleteEdges_levelEdges_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:30.776501+00:00
-- url     : https://prove2.me/submissions/8beaec3c-414a-4430-a67a-a806ed4335fb

module
public import Definitions.Def_LeanPool_CircuitComplexity_Digraph_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Valiant
public import Theorems.Thm_CircuitComplexity_Valiant_one_le_canonicalLabel
public import Theorems.Thm_CircuitComplexity_Valiant_canonicalLabel_le_depth
public import Theorems.Thm_CircuitComplexity_Valiant_canonicalLabel_isLegal
public import Theorems.Thm_CircuitComplexity_Valiant_depth_le_image_card
public import Theorems.Thm_Digraph_mem_edgeFinset

section
@[expose] public section
namespace Digraph
end Digraph
namespace CircuitComplexity.Valiant
open Digraph
variable {V : Type*} [Fintype V]
private lemma canonicalLabel_sub_one_lt_two_pow
    (G : Digraph V) (hac : IsAcyclic G) {k : ℕ} (hd : G.depth ≤ 2 ^ k)
    (v : V) : G.canonicalLabel v - 1 < 2 ^ k := by
  have h1 := (canonicalLabel_le_depth G hac v).trans hd
  have h2 := one_le_canonicalLabel G v
  omega
section LegalLabelHelpers
variable {V : Type*}
end LegalLabelHelpers
private lemma testBit_eq_of_xor_testBit_false
    {x y m : ℕ} (hxor_m : (x ^^^ y).testBit m = false) :
    x.testBit m = y.testBit m := by
  simp_all
omit [Fintype V] in
/-- For `x ≠ y` both below `2 ^ k`, `firstDifferBit k x y` lies in
`{1,...,k}` and `k - firstDifferBit k x y = Nat.log2 (x ^^^ y)`. -/
private lemma firstDifferBit_of_ne
    {k x y : ℕ} (hxne : x ≠ y) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    1 ≤ firstDifferBit k x y ∧
    firstDifferBit k x y ≤ k ∧
    k - firstDifferBit k x y = Nat.log2 (x ^^^ y) := by
  have hxor_ne : x ^^^ y ≠ 0 := Nat.xor_ne_zero_iff.mpr hxne
  have hxor_lt : x ^^^ y < 2 ^ k := Nat.xor_lt_two_pow hx hy
  have hlog_lt : Nat.log2 (x ^^^ y) < k := (Nat.log2_lt hxor_ne).mpr hxor_lt
  simp only [firstDifferBit, if_neg hxne]
  omega
omit [Fintype V] in
/-- Above the pivot `k - firstDifferBit k x y`, bits of `x` and `y` agree. -/
private lemma testBit_eq_above_firstDifferBit
    {k x y : ℕ} (hxne : x ≠ y) (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    {m : ℕ} (hm : k - firstDifferBit k x y < m) :
    x.testBit m = y.testBit m := by
  have hxor_ne : x ^^^ y ≠ 0 := Nat.xor_ne_zero_iff.mpr hxne
  obtain ⟨_, _, hkj_eq⟩ := firstDifferBit_of_ne hxne hx hy
  rw [hkj_eq] at hm
  exact testBit_eq_of_xor_testBit_false
    (Nat.testBit_lt_two_pow ((Nat.log2_lt hxor_ne).mp hm))
omit [Fintype V] in
/-- At the pivot position, if `x < y` then `x`'s bit is `false` and `y`'s
is `true`: `x` must have the 0 and `y` the 1 for the strict inequality. -/
private lemma testBit_firstDifferBit_pivot_of_lt
    {k x y : ℕ} (hxy : x < y) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    x.testBit (k - firstDifferBit k x y) = false ∧
    y.testBit (k - firstDifferBit k x y) = true := by
  set j := firstDifferBit k x y
  have hxne : x ≠ y := hxy.ne
  have hxor_ne : x ^^^ y ≠ 0 := Nat.xor_ne_zero_iff.mpr hxne
  obtain ⟨_, _, hkj_eq⟩ := firstDifferBit_of_ne hxne hx hy
  have hxor_bit : (x ^^^ y).testBit (k - j) = true := by
    rw [hkj_eq]; exact Nat.testBit_log2 hxor_ne
  have hagree : ∀ m, k - j < m → x.testBit m = y.testBit m :=
    fun m hm => testBit_eq_above_firstDifferBit hxne hx hy hm
  rw [Nat.testBit_xor] at hxor_bit
  cases hxb : x.testBit (k - j) <;> cases hyb : y.testBit (k - j)
  · simp [hxb, hyb] at hxor_bit
  · exact ⟨rfl, rfl⟩
  · exfalso
    have : y < x := Nat.lt_of_testBit (k - j) hyb hxb
      (fun m hm => (hagree m hm).symm)
    omega
  · simp [hxb, hyb] at hxor_bit
variable [DecidableEq V]
omit [Fintype V] [DecidableEq V] in
/-- Geometric series: `∑ m ∈ range n, 2^m = 2^n - 1`. -/
private lemma sum_range_pow_two (n : ℕ) :
    ∑ m ∈ Finset.range n, (2 : ℕ) ^ m = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
omit [Fintype V] [DecidableEq V] in
/-- **Split the mask sum at a pivot.** For `j ∈ (Ioc 0 k) \ I`, the
`maskOutI` sum decomposes into contributions above `j`, at `j`, and below. -/
private lemma maskOutI_split_at_pivot
    {k : ℕ} {I : Finset ℕ} {j : ℕ}
    (hj : j ∈ (Finset.Ioc 0 k) \ I) (z : ℕ) :
    maskOutI k I z =
      (∑ i ∈ ((Finset.Ioc 0 k) \ I).filter (· < j),
        if z.testBit (k - i) then 2 ^ (k - i) else 0) +
      (if z.testBit (k - j) then 2 ^ (k - j) else 0) +
      (∑ i ∈ ((Finset.Ioc 0 k) \ I).filter (j < ·),
        if z.testBit (k - i) then 2 ^ (k - i) else 0) := by
  set D : Finset ℕ := (Finset.Ioc 0 k) \ I
  have hmask : maskOutI k I z =
      (if z.testBit (k - j) then 2 ^ (k - j) else 0) +
      ∑ i ∈ D.erase j, (if z.testBit (k - i) then 2 ^ (k - i) else 0) := by
    change (∑ i ∈ D, if z.testBit (k - i) then 2 ^ (k - i) else 0) = _
    conv_lhs => rw [(Finset.insert_erase hj).symm]
    rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  have h_filt_lt : (D.erase j).filter (· < j) = D.filter (· < j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_erase]
    refine ⟨fun ⟨⟨_, hD⟩, hlt⟩ => ⟨hD, hlt⟩, fun ⟨hD, hlt⟩ => ⟨⟨?_, hD⟩, hlt⟩⟩
    omega
  have h_filt_gt : (D.erase j).filter (fun i => ¬ i < j) = D.filter (j < ·) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_erase]
    refine ⟨fun ⟨⟨_, hD⟩, hnlt⟩ => ⟨hD, ?_⟩, fun ⟨hD, hgt⟩ => ⟨⟨?_, hD⟩, ?_⟩⟩ <;> omega
  rw [hmask, ← (Finset.sum_filter_add_sum_filter_not (D.erase j) (· < j) _),
      h_filt_lt, h_filt_gt]
  ring
omit [Fintype V] [DecidableEq V] in
/-- **Below-pivot bound.** The sum of mask contributions at positions below
the pivot `j` is strictly less than `2 ^ (k - j)` (geometric-series bound). -/
private lemma maskOutI_sum_below_lt
    {k : ℕ} (I : Finset ℕ) {j : ℕ} (hj_le : j ≤ k) (z : ℕ) :
    (∑ i ∈ ((Finset.Ioc 0 k) \ I).filter (j < ·),
      if z.testBit (k - i) then 2 ^ (k - i) else 0) < 2 ^ (k - j) := by
  have h1 :
      (∑ i ∈ ((Finset.Ioc 0 k) \ I).filter (j < ·),
        if z.testBit (k - i) then 2 ^ (k - i) else 0) ≤
      ∑ i ∈ Finset.Ioc j k, 2 ^ (k - i) := by
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) (fun _ _ _ => Nat.zero_le _))
    · split_ifs
      · rfl
      · exact Nat.zero_le _
    · simp_all
  have h2 : (∑ i ∈ Finset.Ioc j k, (2 : ℕ) ^ (k - i)) = 2 ^ (k - j) - 1 := by
    rw [show (∑ i ∈ Finset.Ioc j k, (2:ℕ) ^ (k - i)) =
            ∑ m ∈ Finset.range (k - j), (2:ℕ) ^ m from ?_, sum_range_pow_two]
    apply Finset.sum_nbij (fun i => k - i)
    · intro i hi; simp only [Finset.mem_Ioc, Finset.mem_range] at hi ⊢; omega
    · intro a ha b hb hab
      simp only [Finset.coe_Ioc, Set.mem_Ioc] at ha hb
      dsimp at hab; omega
    · intro m hm
      simp only [Finset.coe_range, Set.mem_Iio] at hm
      exact ⟨k - m, by simp only [Finset.coe_Ioc, Set.mem_Ioc]; omega, by dsimp; omega⟩
    · intros; rfl
  have h3 : 0 < 2 ^ (k - j) := Nat.two_pow_pos _
  omega
omit [Fintype V] [DecidableEq V] in
/-- **Key legality.** If `x < y < 2 ^ k` and their first MSB disagreement
is *not* in `I`, then `maskOutI k I x < maskOutI k I y`.

**Proof.** Let `j = firstDifferBit k x y ∈ {1,...,k}`. Split `maskOutI`
at the pivot `j`: upper terms (`i < j`) agree between `x` and `y`; the
pivot term contributes `0` for `x` and `2^(k-j)` for `y`; the lower sum
is bounded by `2^(k-j) - 1`. So `mask(y) - mask(x) ≥ 1`. -/
private lemma maskOutI_lt_of_firstDifferBit_not_mem
    {k : ℕ} {I : Finset ℕ}
    {x y : ℕ} (hxy : x < y) (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (hfd : firstDifferBit k x y ∉ I) :
    maskOutI k I x < maskOutI k I y := by
  obtain ⟨hj_pos, hj_le, _⟩ := firstDifferBit_of_ne hxy.ne hx hy
  obtain ⟨hx_bit_false, hy_bit_true⟩ := testBit_firstDifferBit_pivot_of_lt hxy hx hy
  set j := firstDifferBit k x y
  have hj_mem_D : j ∈ (Finset.Ioc 0 k) \ I :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_Ioc.mpr ⟨hj_pos, hj_le⟩, hfd⟩
  have hup_eq :
      (∑ i ∈ ((Finset.Ioc 0 k) \ I).filter (· < j),
        if x.testBit (k - i) then 2 ^ (k - i) else 0) =
      (∑ i ∈ ((Finset.Ioc 0 k) \ I).filter (· < j),
        if y.testBit (k - i) then 2 ^ (k - i) else 0) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi_lt : i < j := (Finset.mem_filter.mp hi).2
    have hi_le_k : i ≤ k :=
      (Finset.mem_Ioc.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).1).1).2
    rw [testBit_eq_above_firstDifferBit hxy.ne hx hy (by omega : k - j < k - i)]
  have hmask_x := maskOutI_split_at_pivot hj_mem_D x
  have hmask_y := maskOutI_split_at_pivot hj_mem_D y
  rw [hx_bit_false] at hmask_x
  rw [hy_bit_true] at hmask_y
  simp only [Bool.false_eq_true, ite_false, add_zero, ite_true] at hmask_x hmask_y
  have hlow_x_lt := maskOutI_sum_below_lt I hj_le x
  rw [hmask_x, hmask_y, ← hup_eq]
  omega
omit [DecidableEq V] in
/-- **Image bound.** The image of `maskOutI k I` over any function `f : V → ℕ`
has at most `2 ^ (k - |I|)` elements, because `maskOutI k I x` is determined
by the `k - |I|` bits of `x` at positions outside `I`. -/
private lemma maskOutI_image_card_le
    {k : ℕ} {I : Finset ℕ} (hI : I ⊆ Finset.Ioc 0 k)
    (f : V → ℕ) :
    (Finset.univ.image (fun v => maskOutI k I (f v))).card ≤ 2 ^ (k - I.card) := by
  let D : Finset ℕ := (Finset.Ioc 0 k) \ I
  have hD_card : D.card = k - I.card := by
    change ((Finset.Ioc 0 k) \ I).card = k - I.card
    rw [Finset.card_sdiff_of_subset hI]
    simp
  let gbar : V → ({i // i ∈ D} → Bool) := fun v i => (f v).testBit (k - i.val)
  let φ : ({i // i ∈ D} → Bool) → ℕ := fun b =>
    ∑ i ∈ D.attach, if b i then 2 ^ (k - i.val) else 0
  have heq : ∀ v, maskOutI k I (f v) = φ (gbar v) := by
    intro v
    change (∑ i ∈ (Finset.Ioc 0 k) \ I,
            if (f v).testBit (k - i) then 2 ^ (k - i) else 0) =
         (∑ i ∈ D.attach,
            if (gbar v) i then 2 ^ (k - i.val) else 0)
    exact (Finset.sum_attach D
      (fun i => if (f v).testBit (k - i) then 2 ^ (k - i) else 0)).symm
  calc (Finset.univ.image (fun v => maskOutI k I (f v))).card
      = (Finset.univ.image (fun v => φ (gbar v))).card := by
          simp_all
    _ = ((Finset.univ.image gbar).image φ).card := by
          rw [show (fun v => φ (gbar v)) = φ ∘ gbar from rfl, ← Finset.image_image]
    _ ≤ (Finset.univ.image gbar).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset ({i // i ∈ D} → Bool)).card :=
          Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card ({i // i ∈ D} → Bool) := Finset.card_univ
    _ = 2 ^ D.card := by
          rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    _ = 2 ^ (k - I.card) := by rw [hD_card]
end CircuitComplexity.Valiant
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity CircuitComplexity.Valiant
open Digraph
variable {V : Type*} [Fintype V]
variable [DecidableEq V]
namespace CircuitComplexity.Valiant
theorem _root_.solution
    (G : Digraph V) [DecidableRel G.Adj] {k : ℕ}
    (hac : IsAcyclic G) (hd : G.depth ≤ 2 ^ k)
    (I : Finset ℕ) (hI : I ⊆ Finset.Ioc 0 k) :
    (G.deleteEdges (I.biUnion fun i => levelEdges G k i)).depth
      ≤ 2 ^ (k - I.card) := by
  set G' := G.deleteEdges (I.biUnion fun i => levelEdges G k i)
  let ℓ : V → ℕ := fun v => maskOutI k I (G.canonicalLabel v - 1)
  have hlegal : IsLegalLabeling G' ℓ := by
    intro u v huv
    have huv_G : G.Adj u v := huv.1
    have huv_not_I : (u, v) ∉ I.biUnion fun i => levelEdges G k i := huv.2
    have hedge : (u, v) ∈ G.edgeFinset := Digraph.mem_edgeFinset.mpr huv_G
    have hfd_not_in_I :
        firstDifferBit k (G.canonicalLabel u - 1) (G.canonicalLabel v - 1) ∉ I := by
      intro h
      apply huv_not_I
      rw [Finset.mem_biUnion]
      exact ⟨_, h, Finset.mem_filter.mpr ⟨hedge, rfl⟩⟩
    have hcanon_lt : G.canonicalLabel u < G.canonicalLabel v :=
      canonicalLabel_isLegal G hac _ _ huv_G
    have hcu_pos : 1 ≤ G.canonicalLabel u := one_le_canonicalLabel G _
    have hu_lt : G.canonicalLabel u - 1 < 2 ^ k :=
      canonicalLabel_sub_one_lt_two_pow G hac hd _
    have hv_lt : G.canonicalLabel v - 1 < 2 ^ k :=
      canonicalLabel_sub_one_lt_two_pow G hac hd _
    have hxy : G.canonicalLabel u - 1 < G.canonicalLabel v - 1 := by omega
    exact maskOutI_lt_of_firstDifferBit_not_mem hxy hu_lt hv_lt hfd_not_in_I
  have himg : (Finset.univ.image ℓ).card ≤ 2 ^ (k - I.card) :=
    maskOutI_image_card_le hI _
  exact (depth_le_image_card G' hlegal).trans himg
end CircuitComplexity.Valiant
