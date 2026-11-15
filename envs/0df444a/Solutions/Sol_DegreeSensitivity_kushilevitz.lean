-- Prove2me | solution 1 for DegreeSensitivity.kushilevitz
-- status  : ACCEPTED   (prove)
-- author  : @RiemannHorizon
-- created : 2026-11-14T06:21:37.53142+00:00
-- url     : https://prove2.me/submissions/f3e930f6-5fd9-4e54-8790-a64cd52e177e

import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Definitions.Def_polyDegree
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Find
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Ring

/-!
# Kushilevitz's six-variable function

We construct an explicit Boolean function `kush` on six bits with
`polyDegree kush = 3`, `kush 0 = false`, and `sensitivityAt kush 0 = 6`,
following Example 5.4 of Hatami, Kulkarni and Pankratov, *Variations on
the Sensitivity Conjecture*; the function is attributed to E. Kushilevitz
via footnote 1 on p. 560 of Nisan and Wigderson, Combinatorica 15 (1995).

Its algebraic normal form has six linear terms with coefficient `1`,
fifteen quadratic terms with coefficient `-1`, and ten cubic terms with
coefficient `1`:

`h(z) = Σ z_i - Σ_{i<j} z_i z_j + Σ_{(a,b,c)} z_a z_b z_c`.

A finite computation over the 64 cube points shows the count only takes
the values 0 and 1, so `h` is Boolean; the same normal form (as a real
polynomial) then represents it with total degree 3, and the nonzero
third finite difference over `{0, 2, 3}` rules out degree ≤ 2.
-/

namespace DegreeSensitivity

open MvPolynomial

/-! ### The function -/

/-- The ten cubic index triples of the algebraic normal form. -/
def cubicTriples : Finset (Fin 6 × Fin 6 × Fin 6) :=
  {(0, 2, 3), (0, 1, 4), (0, 3, 4), (1, 2, 3), (1, 2, 4),
    (0, 1, 5), (0, 2, 5), (1, 3, 5), (2, 4, 5), (3, 4, 5)}

/-- The fifteen index pairs, i.e. all pairs `a < b`. -/
def pairs6 : Finset (Fin 6 × Fin 6) :=
  Finset.univ.filter fun t : Fin 6 × Fin 6 => t.1 < t.2

/-- Value of one bit as an integer. -/
def kushBit (z : Fin 6 → Bool) (i : Fin 6) : ℤ := if z i then 1 else 0

/-- The algebraic-normal-form count of the Kushilevitz function. -/
def kushCount (z : Fin 6 → Bool) : ℤ :=
  (∑ i : Fin 6, kushBit z i)
    - ∑ t ∈ pairs6, kushBit z t.1 * kushBit z t.2
    + ∑ t ∈ cubicTriples, kushBit z t.1 * kushBit z t.2.1 * kushBit z t.2.2

/-- The Kushilevitz function. -/
def kush (z : Fin 6 → Bool) : Bool := decide (kushCount z = 1)

/-- The count only takes the values 0 and 1 (finite check over the
64 cube points). -/
lemma kushCount_cube : ∀ (z : Fin 6 → Bool), kushCount z = 0 ∨ kushCount z = 1 := by
  decide

lemma kushCount_zero : kushCount (fun _ => false) = 0 := by decide

lemma kush_zero : kush (fun _ => false) = false := by decide

lemma kush_true_flip : ∀ i : Fin 6, kush (flipBit (fun _ => false) i) = true := by
  decide

lemma sensitivityAt_kush_zero : sensitivityAt kush (fun _ => false) = 6 := by
  decide

/-! ### Cast helpers -/

lemma cast_sum_fin {β : Type*} (s : Finset β) (f : β → ℤ) :
    (((∑ i ∈ s, f i) : ℤ) : ℝ) = ∑ i ∈ s, (((f i : ℤ) : ℝ)) :=
  map_sum (Int.castRingHom ℝ) _ _

lemma cast_mul6 (a b : ℤ) : (((a * b) : ℤ) : ℝ) = (((a : ℤ) : ℝ)) * (((b : ℤ) : ℝ)) :=
  map_mul (Int.castRingHom ℝ) a b

/-! ### The representing polynomial -/

/-- The algebraic normal form as a real multilinear polynomial. -/
noncomputable def kushPoly : MvPolynomial (Fin 6) ℝ :=
  (∑ i : Fin 6, (X i : MvPolynomial (Fin 6) ℝ))
    - ∑ t ∈ pairs6, (X t.1 * X t.2 : MvPolynomial (Fin 6) ℝ)
    + ∑ t ∈ cubicTriples, (X t.1 * X t.2.1 * X t.2.2 : MvPolynomial (Fin 6) ℝ)

/-- The count read as a real number, with casted integer atoms. -/
noncomputable def kushCountR (z : Fin 6 → Bool) : ℝ :=
  (∑ i : Fin 6, ((kushBit z i : ℤ) : ℝ))
    - ∑ t ∈ pairs6, ((kushBit z t.1 : ℤ) : ℝ) * ((kushBit z t.2 : ℤ) : ℝ)
    + ∑ t ∈ cubicTriples, ((kushBit z t.1 : ℤ) : ℝ) * ((kushBit z t.2.1 : ℤ) : ℝ)
        * ((kushBit z t.2.2 : ℤ) : ℝ)

lemma cast_kushBit (z : Fin 6 → Bool) (i : Fin 6) :
    ((kushBit z i : ℤ) : ℝ) = if z i then (1 : ℝ) else 0 := by
  unfold kushBit
  cases h : z i <;> simp [h]

lemma eval_kushPoly (z : Fin 6 → Bool) :
    eval (fun i => if z i then (1 : ℝ) else 0) kushPoly = kushCountR z := by
  simp only [kushPoly, kushCountR, cast_kushBit, map_add, map_sub, map_sum, map_mul, eval_X]

lemma kushCountR_eq (z : Fin 6 → Bool) : kushCountR z = ((kushCount z : ℤ) : ℝ) := by
  simp only [kushCountR, kushCount, Int.cast_add, Int.cast_sub, cast_sum_fin, cast_mul6,
    cast_kushBit]

lemma kushPoly_agree (z : Fin 6 → Bool) :
    eval (fun i => if z i then (1 : ℝ) else 0) kushPoly =
      if kush z then (1 : ℝ) else 0 := by
  rw [eval_kushPoly, kushCountR_eq]
  rcases kushCount_cube z with h | h
  · have hk : kush z = false := by simp only [kush, h]; decide
    rw [hk]; norm_num [h]
  · have hk : kush z = true := by simp only [kush, h]; decide
    rw [hk]; norm_num [h, Int.cast_one]

lemma kushPoly_totalDegree : kushPoly.totalDegree ≤ 3 := by
  have hX : ∀ i : Fin 6, (X i : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 3 := fun i => by
    have hx : (X i : MvPolynomial (Fin 6) ℝ).totalDegree = 1 := totalDegree_X (R := ℝ) i
    omega
  have hp : ∀ t ∈ pairs6,
      ((X t.1 * X t.2 : MvPolynomial (Fin 6) ℝ)).totalDegree ≤ 3 := by
    intro t _
    have h1 : ((X t.1 * X t.2 : MvPolynomial (Fin 6) ℝ)).totalDegree
        ≤ (X t.1 : MvPolynomial (Fin 6) ℝ).totalDegree
          + (X t.2 : MvPolynomial (Fin 6) ℝ).totalDegree :=
      totalDegree_mul _ _
    have h2 : (X t.1 : MvPolynomial (Fin 6) ℝ).totalDegree = 1 := totalDegree_X (R := ℝ) t.1
    have h3 : (X t.2 : MvPolynomial (Fin 6) ℝ).totalDegree = 1 := totalDegree_X (R := ℝ) t.2
    omega
  have hc : ∀ t ∈ cubicTriples,
      ((X t.1 * X t.2.1 * X t.2.2 : MvPolynomial (Fin 6) ℝ)).totalDegree ≤ 3 := by
    intro t _
    have h12 : ((X t.1 * X t.2.1 : MvPolynomial (Fin 6) ℝ)).totalDegree ≤ 2 := by
      have hm : ((X t.1 * X t.2.1 : MvPolynomial (Fin 6) ℝ)).totalDegree
          ≤ (X t.1 : MvPolynomial (Fin 6) ℝ).totalDegree
            + (X t.2.1 : MvPolynomial (Fin 6) ℝ).totalDegree :=
        totalDegree_mul _ _
      have h2 : (X t.1 : MvPolynomial (Fin 6) ℝ).totalDegree = 1 := totalDegree_X (R := ℝ) t.1
      have h3 : (X t.2.1 : MvPolynomial (Fin 6) ℝ).totalDegree = 1 := totalDegree_X (R := ℝ) t.2.1
      omega
    have h4 : (X t.2.2 : MvPolynomial (Fin 6) ℝ).totalDegree = 1 := totalDegree_X (R := ℝ) t.2.2
    have hm : ((X t.1 * X t.2.1 * X t.2.2 : MvPolynomial (Fin 6) ℝ)).totalDegree
        ≤ ((X t.1 * X t.2.1 : MvPolynomial (Fin 6) ℝ)).totalDegree
          + (X t.2.2 : MvPolynomial (Fin 6) ℝ).totalDegree :=
      totalDegree_mul _ _
    omega
  have hA : (((∑ i : Fin 6, (X i : MvPolynomial (Fin 6) ℝ))
      - ∑ t ∈ pairs6, (X t.1 * X t.2 : MvPolynomial (Fin 6) ℝ)).totalDegree) ≤ 3 := by
    refine le_trans (totalDegree_sub _ _) (max_le_iff.mpr
      ⟨totalDegree_finsetSum_le (fun i _ => hX i), totalDegree_finsetSum_le hp⟩)
  have hB : (∑ t ∈ cubicTriples,
      (X t.1 * X t.2.1 * X t.2.2 : MvPolynomial (Fin 6) ℝ)).totalDegree ≤ 3 :=
    totalDegree_finsetSum_le hc
  calc kushPoly.totalDegree
      = (((∑ i : Fin 6, (X i : MvPolynomial (Fin 6) ℝ))
          - ∑ t ∈ pairs6, (X t.1 * X t.2 : MvPolynomial (Fin 6) ℝ))
          + ∑ t ∈ cubicTriples,
            (X t.1 * X t.2.1 * X t.2.2 : MvPolynomial (Fin 6) ℝ)).totalDegree := rfl
    _ ≤ max (((∑ i : Fin 6, (X i : MvPolynomial (Fin 6) ℝ))
          - ∑ t ∈ pairs6, (X t.1 * X t.2 : MvPolynomial (Fin 6) ℝ)).totalDegree)
          (∑ t ∈ cubicTriples,
            (X t.1 * X t.2.1 * X t.2.2 : MvPolynomial (Fin 6) ℝ)).totalDegree :=
        totalDegree_add _ _
    _ ≤ 3 := max_le_iff.mpr ⟨hA, hB⟩

/-! ### The signed cube functional -/

/-- The signed evaluation of `p` over the subcube indexed by `S`. -/
noncomputable def altEval (S : Finset (Fin 6)) (p : MvPolynomial (Fin 6) ℝ) : ℝ :=
  ∑ T ∈ S.powerset,
    (if (S.card - T.card) % 2 = 0 then (1 : ℝ) else -1) *
      eval (fun i => if decide (i ∈ T) then (1 : ℝ) else 0) p

lemma altEval_add (S : Finset (Fin 6)) (p q : MvPolynomial (Fin 6) ℝ) :
    altEval S (p + q) = altEval S p + altEval S q := by
  unfold altEval
  rw [Finset.sum_congr rfl (fun T _ => by rw [eval_add, mul_add]), Finset.sum_add_distrib]

lemma altEval_smul (S : Finset (Fin 6)) (c : ℝ) (p : MvPolynomial (Fin 6) ℝ) :
    altEval S (c • p) = c * altEval S p := by
  unfold altEval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [smul_eval]
  ring

lemma altEval_sum (S : Finset (Fin 6)) {ι : Type*} (s : Finset ι)
    (g : ι → MvPolynomial (Fin 6) ℝ) :
    altEval S (∑ v ∈ s, g v) = ∑ v ∈ s, altEval S (g v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [altEval, map_zero]
  | insert v s hv ih =>
    rw [Finset.sum_insert hv, Finset.sum_insert hv, altEval_add, ih]

lemma neg_one_pow_two_mul (m : ℕ) : (-1 : ℝ) ^ (2 * m) = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h2m : 2 * (m + 1) = 2 * m + 2 := by ring
    rw [h2m, pow_add, ih, one_mul]
    norm_num

lemma parityWeight (k : ℕ) : ((if k % 2 = 0 then (1 : ℝ) else -1) : ℝ) = (-1) ^ k := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · rw [if_pos h]
    obtain ⟨m, hm⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
    rw [hm, neg_one_pow_two_mul]
  · rw [if_neg (by omega : ¬ (k % 2 = 0))]
    obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨(k - 1) / 2, by omega⟩
    rw [hm, pow_add, neg_one_pow_two_mul, one_mul, pow_one]

/-- The signed evaluation of a monomial over the `S`-subcube vanishes when
the monomial involves fewer than `S.card` coordinates. -/
lemma altEval_monomial_zero (S : Finset (Fin 6)) (u : Fin 6 →₀ ℕ)
    (hdeg : u.support.card < S.card) : altEval S (monomial u (1 : ℝ)) = 0 := by
  classical
  have hterm : ∀ T ∈ S.powerset,
      (if (S.card - T.card) % 2 = 0 then (1 : ℝ) else -1) *
        eval (fun i => if decide (i ∈ T) then (1 : ℝ) else 0) (monomial u (1 : ℝ))
      = if u.support ⊆ T then (if (S.card - T.card) % 2 = 0 then (1 : ℝ) else -1) else 0 := by
    intro T hT
    rw [eval_monomial, one_mul]
    by_cases hUT : u.support ⊆ T
    · rw [if_pos hUT]
      have hprod : u.prod (fun i e => (if decide (i ∈ T) then (1 : ℝ) else 0) ^ e) = 1 := by
        show ∏ i ∈ u.support, (if decide (i ∈ T) then (1 : ℝ) else 0) ^ u i = 1
        refine Finset.prod_eq_one fun i hi => ?_
        have hiT : i ∈ T := hUT hi
        rw [if_pos (decide_eq_true hiT), one_pow]
      rw [hprod, mul_one]
    · obtain ⟨i₀, hi₀mem, hi₀T⟩ := Finset.not_subset.mp hUT
      have hne : u i₀ ≠ 0 := Finsupp.mem_support_iff.mp hi₀mem
      rw [if_neg hUT]
      show (if (S.card - T.card) % 2 = 0 then (1 : ℝ) else -1) *
        ∏ i ∈ u.support, (if decide (i ∈ T) then (1 : ℝ) else 0) ^ u i = 0
      rw [Finset.prod_eq_zero hi₀mem ?_]
      · exact mul_zero _
      · rw [if_neg (by simp [hi₀T]), zero_pow hne]
  calc altEval S (monomial u (1 : ℝ))
      = ∑ T ∈ S.powerset, (if (S.card - T.card) % 2 = 0 then (1 : ℝ) else -1) *
          eval (fun i => if decide (i ∈ T) then (1 : ℝ) else 0) (monomial u (1 : ℝ)) := rfl
    _ = ∑ T ∈ S.powerset,
          (if u.support ⊆ T then (if (S.card - T.card) % 2 = 0 then (1 : ℝ) else -1) else 0) := by
        rw [Finset.sum_congr rfl hterm]
    _ = 0 := by
        by_cases hUS : u.support ⊆ S
        · have hex : ∃ a₀, a₀ ∈ S ∧ a₀ ∉ u.support := by
            by_contra hcon
            have hsub : S ⊆ u.support := fun a ha => by
              by_contra han
              exact hcon ⟨a, ha, han⟩
            have hcard2 := Finset.card_le_card hsub
            omega
          obtain ⟨a₀, ha₀S, ha₀U⟩ := hex
          refine Finset.sum_involution
            (fun (T : Finset (Fin 6)) (_ : T ∈ S.powerset) =>
              if a₀ ∈ T then T.erase a₀ else insert a₀ T) ?_ ?_ ?_ ?_
          · -- paired terms cancel
            intro T hT
            have hTS := Finset.mem_powerset.mp hT
            have hTSU : T.card ≤ S.card := Finset.card_le_card hTS
            by_cases ha₀T : a₀ ∈ T
            · rw [if_pos ha₀T]
              have hiff : u.support ⊆ T ↔ u.support ⊆ T.erase a₀ := by
                constructor
                · intro h x hx
                  have hne : x ≠ a₀ := fun hh => ha₀U (by rw [← hh]; exact hx)
                  exact Finset.mem_erase.mpr ⟨hne, h hx⟩
                · intro h x hx
                  have hne : x ≠ a₀ := fun hh => ha₀U (by rw [← hh]; exact hx)
                  exact (Finset.mem_erase.mp (h hx)).2
              have hce : (T.erase a₀).card = T.card - 1 := Finset.card_erase_of_mem ha₀T
              have hT1 : 0 < T.card := Finset.card_pos.mpr ⟨a₀, ha₀T⟩
              by_cases hUT : u.support ⊆ T
              · rw [if_pos hUT, if_pos (hiff.mp hUT), parityWeight, parityWeight]
                have hex' : S.card - (T.erase a₀).card = (S.card - T.card) + 1 := by omega
                rw [hex', pow_succ]
                ring
              · rw [if_neg hUT, if_neg (fun hh => hUT (hiff.mpr hh))]
                simp
            · rw [if_neg ha₀T]
              have hiff : u.support ⊆ T ↔ u.support ⊆ insert a₀ T := by
                constructor
                · intro h x hx
                  exact Finset.mem_insert_of_mem (h hx)
                · intro h x hx
                  rcases Finset.mem_insert.mp (h hx) with hx' | hx'
                  · subst hx'
                    exact (ha₀U hx).elim
                  · exact hx'
              have hci : (insert a₀ T).card = T.card + 1 :=
                Finset.card_insert_of_notMem ha₀T
              have hle : T.card + 1 ≤ S.card := by
                have hmem2 : insert a₀ T ⊆ S := by
                  intro x hx
                  rcases Finset.mem_insert.mp hx with hx' | hx'
                  · rw [hx']; exact ha₀S
                  · exact hTS hx'
                have hcard2 := Finset.card_le_card hmem2
                omega
              by_cases hUT : u.support ⊆ T
              · rw [if_pos hUT, if_pos (hiff.mp hUT), parityWeight, parityWeight]
                have hex' : S.card - T.card = S.card - (insert a₀ T).card + 1 := by omega
                rw [hex', pow_succ]
                ring
              · rw [if_neg hUT, if_neg (fun hh => hUT (hiff.mpr hh))]
                simp
          · -- a fixed point would carry a nonzero summand
            intro T hT hF
            have hUT : u.support ⊆ T := by
              by_contra hn
              rw [if_neg hn] at hF
              exact absurd rfl hF
            by_cases ha₀T : a₀ ∈ T
            · rw [if_pos ha₀T]
              intro hh
              rw [← hh] at ha₀T
              exact Finset.notMem_erase a₀ T ha₀T
            · rw [if_neg ha₀T]
              exact Finset.insert_ne_self.mpr ha₀T
          · -- the involution stays inside the powerset
            intro T hT
            have hTS := Finset.mem_powerset.mp hT
            by_cases ha₀T : a₀ ∈ T
            · rw [if_pos ha₀T]
              refine Finset.mem_powerset.mpr (fun x hx => hTS ?_)
              exact (Finset.mem_erase.mp hx).2
            · rw [if_neg ha₀T]
              refine Finset.mem_powerset.mpr (fun x hx => ?_)
              rcases Finset.mem_insert.mp hx with hx' | hx'
              · rw [hx']; exact ha₀S
              · exact hTS hx'
          · -- involutivity
            intro T hT
            by_cases ha₀T : a₀ ∈ T
            · rw [if_pos ha₀T, if_neg (Finset.notMem_erase a₀ T), Finset.insert_erase ha₀T]
            · rw [if_neg ha₀T, if_pos (Finset.mem_insert_self a₀ T), Finset.erase_insert ha₀T]
        · refine Finset.sum_eq_zero fun T hT => ?_
          rw [if_neg (fun hmem => hUS (fun x hx => (Finset.mem_powerset.mp hT) (hmem hx)))]

lemma altEval_zero (S : Finset (Fin 6)) (p : MvPolynomial (Fin 6) ℝ)
    (h : ∀ u ∈ p.support, u.support.card < S.card) : altEval S p = 0 := by
  have has := as_sum p
  rw [has, altEval_sum]
  refine Finset.sum_eq_zero fun u hu => ?_
  rcases eq_or_ne (coeff u p) 0 with h0 | hne
  · rw [h0, map_zero]
    simp only [altEval, map_zero]
    exact Finset.sum_eq_zero fun T _ => mul_zero _
  · have hdeg := h u hu
    have hrw : monomial u (coeff u p) = coeff u p • monomial u (1 : ℝ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hrw, altEval_smul, altEval_monomial_zero S u hdeg, mul_zero]

lemma card_le_sum_nat {β : Type*} (f : β → ℕ) (s : Finset β)
    (hf : ∀ i ∈ s, 1 ≤ f i) : s.card ≤ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have hih := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a s)
    omega

/-! ### The degree lower bound -/

/-- The signed sum of the Kushilevitz values over `{0, 2, 3}` (finite
check: it is the coefficient `+1` of `z₀ z₂ z₃` in the normal form). -/
lemma altSum_kush_values_int :
    (∑ T ∈ ({0, 2, 3} : Finset (Fin 6)).powerset,
        (if (({0, 2, 3} : Finset (Fin 6)).card - T.card) % 2 = 0 then (1 : ℤ) else -1) *
          (if kush (fun i => decide (i ∈ T)) then (1 : ℤ) else 0)) = 1 := by
  decide

lemma altSum_kush_values :
    (∑ T ∈ ({0, 2, 3} : Finset (Fin 6)).powerset,
        (if (({0, 2, 3} : Finset (Fin 6)).card - T.card) % 2 = 0 then (1 : ℝ) else -1) *
          (if kush (fun i => decide (i ∈ T)) then (1 : ℝ) else 0)) = 1 := by
  have hcast : (((∑ T ∈ ({0, 2, 3} : Finset (Fin 6)).powerset,
      (if (({0, 2, 3} : Finset (Fin 6)).card - T.card) % 2 = 0 then (1 : ℤ) else -1) *
        (if kush (fun i => decide (i ∈ T)) then (1 : ℤ) else 0) : ℤ)) : ℝ)
      = (∑ T ∈ ({0, 2, 3} : Finset (Fin 6)).powerset,
        (if (({0, 2, 3} : Finset (Fin 6)).card - T.card) % 2 = 0 then (1 : ℝ) else -1) *
          (if kush (fun i => decide (i ∈ T)) then (1 : ℝ) else 0)) := by
    rw [cast_sum_fin]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases hpar : (({0, 2, 3} : Finset (Fin 6)).card - T.card) % 2 = 0
    · rw [if_pos hpar, if_pos hpar, cast_mul6]
      by_cases hk : kush (fun i => decide (i ∈ T))
      · rw [if_pos hk, if_pos hk]; norm_num [Int.cast_one]
      · rw [if_neg hk, if_neg hk]; norm_num [Int.cast_zero]
    · rw [if_neg hpar, if_neg hpar, cast_mul6]
      by_cases hk : kush (fun i => decide (i ∈ T))
      · rw [if_pos hk, if_pos hk]; norm_num [Int.cast_one, Int.cast_neg]
      · rw [if_neg hk, if_neg hk]; norm_num [Int.cast_zero, Int.cast_neg]
  rw [← hcast]
  exact_mod_cast altSum_kush_values_int

lemma altSum_kush_kills (d : ℕ) (hd : d ≤ 2) : ¬ HasPolyRep kush d := by
  intro ⟨p, hp, hag⟩
  have hagh : ∀ T : Finset (Fin 6),
      eval (fun i => if decide (i ∈ T) then (1 : ℝ) else 0) p
        = if kush (fun i => decide (i ∈ T)) then (1 : ℝ) else 0 := fun T => hag _
  have hsup : ∀ u ∈ p.support, u.support.card < 3 := fun u hu => by
    have h1 := le_totalDegree (p := p) (s := u) hu
    rw [Finsupp.sum_fintype u (fun _ e => e) (fun _ => rfl)] at h1
    have h2 : u.support.card ≤ ∑ i, u i := by
      calc u.support.card ≤ ∑ i ∈ u.support, u i :=
          card_le_sum_nat u u.support
            (fun i hi => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))
        _ ≤ ∑ i, u i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega
  have hvan : altEval ({0, 2, 3} : Finset (Fin 6)) p = 0 := by
    have hcard : ({0, 2, 3} : Finset (Fin 6)).card = 3 := by decide
    refine altEval_zero ({0, 2, 3} : Finset (Fin 6)) p (fun u hu => ?_)
    have hthis := hsup u hu
    omega
  have hK : altEval ({0, 2, 3} : Finset (Fin 6)) p
      = (∑ T ∈ ({0, 2, 3} : Finset (Fin 6)).powerset,
          (if (({0, 2, 3} : Finset (Fin 6)).card - T.card) % 2 = 0 then (1 : ℝ) else -1) *
            (if kush (fun i => decide (i ∈ T)) then (1 : ℝ) else 0)) := by
    unfold altEval
    exact Finset.sum_congr rfl fun T _ => by rw [hagh T]
  have hK0 : (∑ T ∈ ({0, 2, 3} : Finset (Fin 6)).powerset,
      (if (({0, 2, 3} : Finset (Fin 6)).card - T.card) % 2 = 0 then (1 : ℝ) else -1) *
        (if kush (fun i => decide (i ∈ T)) then (1 : ℝ) else 0)) = 0 := by
    rw [← hK]; exact hvan
  exact absurd (altSum_kush_values.symm.trans hK0) (by simp)

/-! ### The theorem -/

end DegreeSensitivity

open DegreeSensitivity

theorem solution :
    ∃ f : BoolFunc 6, polyDegree f = 3 ∧ f (fun _ => false) = false ∧
      sensitivityAt f (fun _ => false) = 6 := by
  refine ⟨kush, ?_, kush_zero, sensitivityAt_kush_zero⟩
  have hiff : (@Nat.find (fun d => HasPolyRep kush d)
      (fun d => Classical.propDecidable (HasPolyRep kush d))
      ⟨6, hasPolyRep_card kush⟩ = 3) ↔
      (HasPolyRep kush 3 ∧ ∀ n < 3, ¬ HasPolyRep kush n) :=
    @Nat.find_eq_iff 3 (fun d => HasPolyRep kush d)
      (fun d => Classical.propDecidable (HasPolyRep kush d))
      ⟨6, hasPolyRep_card kush⟩
  show (@Nat.find (fun d => HasPolyRep kush d)
      (fun d => Classical.propDecidable (HasPolyRep kush d))
      ⟨6, hasPolyRep_card kush⟩) = 3
  rw [hiff]
  refine ⟨⟨kushPoly, kushPoly_totalDegree, kushPoly_agree⟩, fun d hd => ?_⟩
  exact match d with
    | 0 => altSum_kush_kills 0 (by omega)
    | 1 => altSum_kush_kills 1 (by omega)
    | 2 => altSum_kush_kills 2 (by omega)
    | m + 3 => absurd hd (by omega)
