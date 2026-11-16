-- Prove2me | solution 1 for DegreeSensitivity.amano_no_fully_sensitive_ten_variables_degree_four
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-15T21:48:15.190567+00:00
-- url     : https://prove2.me/submissions/93ea3d13-5b6a-4fdd-871f-827237197747

import Mathlib
import Definitions.Def_BoolFunc
import Definitions.Def_polyDegree
import Definitions.Def_sensitivity

namespace CarriedDerivative
section
namespace SymmetrizationReplay
/-!
# Minsky–Papert symmetrization

For any multivariate real polynomial `p : ℝ[X_1, …, X_b]` of total degree
`≤ d`, the function obtained by *averaging* `p` over the Hamming-weight-`t`
slice of the Boolean cube `{0,1}^b` extends to a univariate polynomial of
degree `≤ d`. This is the crucial dimensionality-reduction step in the
Nisan–Szegedy proof of `bs(f) ≤ 2 · deg(f)²`.

Stated multiplicatively (`Q(t) · (b choose t) = sum`) to avoid the division-by-
zero pathology when `t > b` (`b.choose t = 0`); for `t ≤ b`, `b.choose t > 0`
and so `Q(t)` is determined by the sum.

Left as a platform leaf — DEFERRED. Will be tackled in a separate session.
-/

open MvPolynomial


open Polynomial Finset

namespace MPsym

/-! ### The binomial-coefficient polynomial `X ↦ C(X, k)` -/

noncomputable def cpoly (k : ℕ) : Polynomial ℝ :=
  Polynomial.C ((k.factorial : ℝ)⁻¹) * descPochhammer ℝ k

lemma cpoly_natDegree_le (k : ℕ) : (cpoly k).natDegree ≤ k := by
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C, descPochhammer_natDegree, zero_add]

lemma cpoly_eval (n k : ℕ) : (cpoly k).eval (n : ℝ) = (n.choose k : ℝ) := by
  have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
  have hdp : (descPochhammer ℝ k).eval (n : ℝ) = (n.descFactorial k : ℝ) := by
    exact_mod_cast descPochhammer_eval_eq_descFactorial ℝ n k
  rw [cpoly, Polynomial.eval_mul, Polynomial.eval_C, hdp, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

/-! ### Vandermonde-type binomial identity -/

lemma choose_mul_eq {b t k : ℕ} (hk : k ≤ t) (ht : t ≤ b) :
    t.choose k * b.choose t = b.choose k * (b - k).choose (t - k) := by
  have hkb : k ≤ b := hk.trans ht
  have htk : t - k ≤ b - k := Nat.sub_le_sub_right ht k
  have hbkt : b - k - (t - k) = b - t := by omega
  apply Nat.eq_of_mul_eq_mul_right
    (show 0 < k.factorial * (t - k).factorial * (b - t).factorial by positivity)
  have hL : t.choose k * b.choose t * (k.factorial * (t - k).factorial * (b - t).factorial)
      = (t.choose k * k.factorial * (t - k).factorial) * (b.choose t * (b - t).factorial) := by ring
  have hR : b.choose k * (b - k).choose (t - k) * (k.factorial * (t - k).factorial * (b - t).factorial)
      = (b.choose k * k.factorial) * ((b - k).choose (t - k) * (t - k).factorial * (b - t).factorial) := by ring
  rw [hL, hR, Nat.choose_mul_factorial_mul_factorial hk]
  rw [show (b - k).choose (t - k) * (t - k).factorial * (b - t).factorial
        = (b - k).choose (t - k) * (t - k).factorial * ((b - k) - (t - k)).factorial by rw [hbkt]]
  rw [Nat.choose_mul_factorial_mul_factorial htk]
  have h1 : b.choose t * t.factorial * (b - t).factorial = b.factorial :=
    Nat.choose_mul_factorial_mul_factorial ht
  have h2 : b.choose k * k.factorial * (b - k).factorial = b.factorial :=
    Nat.choose_mul_factorial_mul_factorial hkb
  calc t.factorial * (b.choose t * (b - t).factorial)
      = b.choose t * t.factorial * (b - t).factorial := by ring
    _ = b.factorial := h1
    _ = b.choose k * k.factorial * (b - k).factorial := h2.symm

/-! ### Counting -/

lemma count_weight_supset {b : ℕ} (S : Finset (Fin b)) {t : ℕ} (hSt : S.card ≤ t) :
    ((univ : Finset (Fin b → Bool)).filter
      (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t ∧
        ∀ i ∈ S, y i = true)).card =
    (b - S.card).choose (t - S.card) := by
  have hbij :
      ((univ : Finset (Fin b → Bool)).filter
        (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t ∧
          ∀ i ∈ S, y i = true)).card
      = ((univ \ S).powersetCard (t - S.card)).card := by
    refine Finset.card_bij'
      (fun y _ => (univ.filter (fun i => y i = true)) \ S)
      (fun T _ => (fun i => decide (i ∈ T ∨ i ∈ S)))
      ?_ ?_ ?_ ?_
    · rintro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      obtain ⟨hwt, hall⟩ := hy
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [mem_sdiff, mem_filter, mem_univ, true_and] at hi ⊢
        exact hi.2
      · have hSsub : S ⊆ univ.filter (fun i => y i = true) := by
          intro i hi
          simp only [mem_filter, mem_univ, true_and]
          exact hall i hi
        rw [Finset.card_sdiff, hwt, Finset.inter_eq_left.mpr hSsub]
    · rintro T hT
      rw [Finset.mem_powersetCard] at hT
      obtain ⟨hTsub, hTcard⟩ := hT
      simp only [mem_filter, mem_univ, true_and]
      have hdisj : Disjoint T S := by
        rw [Finset.disjoint_left]
        intro i hiT hiS
        have := hTsub hiT
        simp only [mem_sdiff] at this
        exact this.2 hiS
      refine ⟨?_, ?_⟩
      · have hfeq : (univ.filter (fun i => decide (i ∈ T ∨ i ∈ S) = true)) = T ∪ S := by
          ext i
          simp [Finset.mem_union]
        rw [hfeq, Finset.card_union_of_disjoint hdisj, hTcard]
        omega
      · intro i hi
        simp [hi]
    · rintro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      funext i
      by_cases hiS : i ∈ S
      · rw [hy.2 i hiS]
        simp [hiS]
      · simp only [decide_eq_true_eq, mem_sdiff, mem_filter, mem_univ, true_and, hiS,
          or_false, and_true]
        cases h : y i <;> simp [h]
    · rintro T hT
      rw [Finset.mem_powersetCard] at hT
      ext i
      simp only [mem_sdiff, mem_filter, mem_univ, true_and, decide_eq_true_eq]
      constructor
      · rintro ⟨hor, hiS⟩
        rcases hor with h | h
        · exact h
        · exact absurd h hiS
      · intro hiT
        have := hT.1 hiT
        simp only [mem_sdiff] at this
        exact ⟨Or.inl hiT, this.2⟩
  rw [hbij, Finset.card_powersetCard, Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]

lemma count_weight_supset_zero {b : ℕ} (S : Finset (Fin b)) {t : ℕ} (hSt : t < S.card) :
    ((univ : Finset (Fin b → Bool)).filter
      (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t ∧
        ∀ i ∈ S, y i = true)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y _
  intro hyp
  obtain ⟨hwt, hall⟩ := hyp
  have hSsub : S ⊆ univ.filter (fun i => y i = true) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and]
    exact hall i hi
  have := Finset.card_le_card hSsub
  omega

/-! ### The monomial piece -/

noncomputable def Qmono {b : ℕ} (α : Fin b →₀ ℕ) : Polynomial ℝ :=
  Polynomial.C ((b.choose α.support.card : ℝ)⁻¹) * cpoly α.support.card

lemma Qmono_natDegree_le {b : ℕ} (α : Fin b →₀ ℕ) : (Qmono α).natDegree ≤ α.support.card := by
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C, zero_add]
  exact cpoly_natDegree_le _

lemma eval_monomial_at_bool {b : ℕ} (α : Fin b →₀ ℕ) (y : Fin b → Bool) :
    MvPolynomial.eval (fun i => if y i = true then (1 : ℝ) else 0) (MvPolynomial.monomial α (1 : ℝ))
      = if ∀ i ∈ α.support, y i = true then (1 : ℝ) else 0 := by
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod]
  calc ∏ i ∈ α.support, (if y i = true then (1:ℝ) else 0) ^ α i
      = ∏ i ∈ α.support, (if y i = true then (1:ℝ) else 0) := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        have hαi : α i ≠ 0 := Finsupp.mem_support_iff.mp hi
        cases h : y i
        · simp [h, zero_pow hαi]
        · simp [h]
    _ = if ∀ i ∈ α.support, y i = true then (1:ℝ) else 0 := by
        split_ifs with hall
        · exact Finset.prod_eq_one (fun i hi => by simp [hall i hi])
        · push_neg at hall
          obtain ⟨i, hiS, hyi⟩ := hall
          exact Finset.prod_eq_zero hiS (if_neg hyi)

lemma Qmono_eval_eq {b : ℕ} (α : Fin b →₀ ℕ) {t : ℕ} (ht : t ≤ b) :
    (Qmono α).eval (t : ℝ) * (b.choose t : ℝ)
      = ∑ y ∈ (univ : Finset (Fin b → Bool)).filter
            (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t),
          MvPolynomial.eval (fun i => if y i = true then (1 : ℝ) else 0) (MvPolynomial.monomial α (1 : ℝ)) := by
  set k := α.support.card with hkdef
  have hkb : k ≤ b := by
    calc k ≤ (univ : Finset (Fin b)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = b := by rw [Finset.card_univ, Fintype.card_fin]
  have hRHS : (∑ y ∈ (univ : Finset (Fin b → Bool)).filter
        (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t),
      MvPolynomial.eval (fun i => if y i = true then (1 : ℝ) else 0) (MvPolynomial.monomial α (1 : ℝ)))
      = (((univ : Finset (Fin b → Bool)).filter
          (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t ∧
            ∀ i ∈ α.support, y i = true)).card : ℝ) := by
    simp only [eval_monomial_at_bool]
    rw [Finset.sum_boole, Finset.filter_filter]
  rw [hRHS, Qmono, Polynomial.eval_mul, Polynomial.eval_C, cpoly_eval]
  by_cases hkt : k ≤ t
  · rw [count_weight_supset α.support hkt]
    have hbcn : (b.choose k : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos hkb).ne'
    rw [show (↑(b.choose k) : ℝ)⁻¹ * (↑(t.choose k)) * (↑(b.choose t))
          = (↑(t.choose k) * ↑(b.choose t)) / (↑(b.choose k)) from by ring]
    rw [div_eq_iff hbcn]
    exact_mod_cast (choose_mul_eq hkt ht).trans (Nat.mul_comm _ _)
  · push_neg at hkt
    rw [count_weight_supset_zero α.support hkt]
    rw [Nat.choose_eq_zero_of_lt hkt]
    simp

lemma card_support_le_sum {b : ℕ} (α : Fin b →₀ ℕ) :
    α.support.card ≤ α.sum (fun _ e => e) := by
  rw [Finsupp.sum]
  calc α.support.card = ∑ _i ∈ α.support, 1 := Finset.card_eq_sum_ones _
    _ ≤ ∑ i ∈ α.support, α i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)

end MPsym

open MPsym

theorem solution
    {b : ℕ} (p : MvPolynomial (Fin b) ℝ) :
    ∃ Q : Polynomial ℝ,
      Q.natDegree ≤ p.totalDegree ∧
      ∀ t : ℕ, t ≤ b →
        Q.eval (t : ℝ) * ((b.choose t : ℕ) : ℝ) =
          ∑ y ∈ (Finset.univ : Finset (Fin b → Bool)).filter
                  (fun y => ((Finset.univ : Finset (Fin b)).filter
                                (fun i => y i = true)).card = t),
            MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) p := by
  refine ⟨∑ α ∈ p.support, Polynomial.C (MvPolynomial.coeff α p) * Qmono α, ?_, ?_⟩
  · -- degree bound
    refine Polynomial.natDegree_le_iff_degree_le.mpr ?_
    refine (Polynomial.degree_sum_le _ _).trans ?_
    refine Finset.sup_le ?_
    intro α hα
    refine Polynomial.degree_le_natDegree.trans ?_
    refine Nat.cast_le.mpr ?_
    calc (Polynomial.C (MvPolynomial.coeff α p) * Qmono α).natDegree
        ≤ 0 + (Qmono α).natDegree := by
          refine Polynomial.natDegree_mul_le.trans ?_
          rw [Polynomial.natDegree_C]
      _ ≤ α.support.card := by rw [zero_add]; exact Qmono_natDegree_le α
      _ ≤ α.sum (fun _ e => e) := card_support_le_sum α
      _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hα
  · intro t ht
    rw [Polynomial.eval_finset_sum]
    simp_rw [Polynomial.eval_mul, Polynomial.eval_C]
    rw [Finset.sum_mul]
    simp_rw [mul_assoc, Qmono_eval_eq _ ht, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro y _
    conv_rhs => rw [MvPolynomial.as_sum p]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro α _
    rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
    ring

end SymmetrizationReplay
noncomputable def minsky_papert_symmetrization := @SymmetrizationReplay.solution
namespace BooleanSymmetry
open Finset

namespace PDUBSketch

variable {b : ℕ}

/-- The weight-0 slice is the singleton `{fun _ => false}`. -/
lemma slice_zero :
    ((univ : Finset (Fin b → Bool)).filter
      (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = 0))
      = {fun _ => false} := by
  ext y
  simp only [mem_filter, mem_univ, true_and, mem_singleton, Finset.card_eq_zero]
  constructor
  · intro h
    funext i
    cases hy : y i
    · rfl
    · exfalso
      have hi : i ∈ (univ : Finset (Fin b)).filter (fun j => y j = true) := by simp [hy]
      rw [h] at hi
      exact Finset.notMem_empty i hi
  · rintro rfl
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    simp

/-- Every `y` in the weight-1 slice equals some `eᵢ`. -/
lemma slice_one_val (g : BoolFunc b)
    (h_units : ∀ i : Fin b, g (Function.update (fun _ => false) i true) = true)
    (y : Fin b → Bool)
    (hy : y ∈ (univ : Finset (Fin b → Bool)).filter
      (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = 1)) :
    g y = true := by
  simp only [mem_filter, mem_univ, true_and] at hy
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hy
  have hyi : y i = true := by
    have : i ∈ univ.filter (fun j => y j = true) := by rw [hi]; exact mem_singleton_self i
    exact (mem_filter.mp this).2
  have hynot : ∀ j, j ≠ i → y j = false := by
    intro j hj
    cases h : y j
    · rfl
    · exfalso
      have : j ∈ univ.filter (fun k => y k = true) := by simp [h]
      rw [hi] at this
      exact hj (mem_singleton.mp this)
  have hy_eq : y = Function.update (fun _ => false) i true := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [hyi]
    · simp only [Function.update, hj, dif_neg hj]
      exact hynot j hj
  rw [hy_eq]
  exact h_units i

/-- `#(slice t) = b.choose t`. -/
lemma card_slice {t : ℕ} (ht : t ≤ b) :
    ((univ : Finset (Fin b → Bool)).filter
      (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t)).card
    = b.choose t := by
  have hbij : ((univ : Finset (Fin b → Bool)).filter
      (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t)).card
      = ((univ : Finset (Fin b)).powersetCard t).card := by
    refine Finset.card_bij'
      (fun y _ => (univ : Finset (Fin b)).filter (fun i => y i = true))
      (fun T _ => (fun i => decide (i ∈ T)))
      ?_ ?_ ?_ ?_
    · intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.filter_subset _ _, hy⟩
    · intro T hT
      rw [Finset.mem_powersetCard] at hT
      simp only [mem_filter, mem_univ, true_and]
      have hTeq : (univ : Finset (Fin b)).filter (fun i => decide (i ∈ T) = true) = T := by
        ext i; simp
      rw [hTeq]; exact hT.2
    · intro y hy
      funext i
      simp only [decide_eq_true_eq, mem_filter, mem_univ, true_and]
      cases h : y i <;> simp [h]
    · intro T hT
      ext i; simp
  rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

end PDUBSketch

open PDUBSketch Classical

theorem solution
    {b : ℕ} (hb : 1 ≤ b) (g : BoolFunc b)
    (h_zero : g (fun _ => false) = false)
    (h_units : ∀ i : Fin b, g (Function.update (fun _ => false) i true) = true) :
    ∃ Q : Polynomial ℝ, Q.natDegree ≤ polyDegree g ∧ Q.eval 0 = 0 ∧ Q.eval 1 = 1 ∧ (∀ t : ℕ, t ≤ b → 0 ≤ Q.eval (t : ℝ)) ∧ (∀ t : ℕ, t ≤ b → Q.eval (t : ℝ) ≤ 1) := by
  -- Step 1: extract multilinear rep `p`.
  have hrep : HasPolyRep g (polyDegree g) := by
    unfold polyDegree
    exact Nat.find_spec _
  obtain ⟨p, hp_deg, hp_eval⟩ := hrep
  -- Step 2: Minsky–Papert symmetrization.
  obtain ⟨Q, hQ_deg, hQ_eval⟩ := minsky_papert_symmetrization p
  have hQd : Q.natDegree ≤ polyDegree g := hQ_deg.trans hp_deg
  have hQ_eval' : ∀ t : ℕ, t ≤ b →
      Q.eval (t : ℝ) * ((b.choose t : ℕ) : ℝ) =
        ∑ y ∈ (univ : Finset (Fin b → Bool)).filter
          (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t),
          (if g y = true then (1 : ℝ) else 0) := by
    intro t ht
    rw [hQ_eval t ht]
    refine Finset.sum_congr rfl ?_
    intro y _
    exact hp_eval y
  -- Step 3a: `Q(0) = 0`.
  have hQ0 : Q.eval 0 = 0 := by
    have h0 := hQ_eval' 0 (Nat.zero_le _)
    rw [slice_zero, Finset.sum_singleton, h_zero, if_neg (by decide), Nat.choose_zero_right,
      Nat.cast_one, mul_one, Nat.cast_zero] at h0
    exact h0
  -- Step 3b: `Q(1) = 1`.
  have hQ1 : Q.eval 1 = 1 := by
    have h1 := hQ_eval' 1 hb
    have hall : ∀ y ∈ (univ : Finset (Fin b → Bool)).filter
        (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = 1),
        (if g y = true then (1 : ℝ) else 0) = 1 := by
      intro y hy
      rw [slice_one_val g h_units y hy]
      simp
    rw [Finset.sum_congr rfl hall, Finset.sum_const, card_slice hb, nsmul_eq_mul, mul_one,
      Nat.choose_one_right, Nat.cast_one] at h1
    have hbne : ((b : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have : Q.eval 1 * (b : ℝ) = (b : ℝ) := h1
    field_simp at this
    tauto
  -- Step 3c: `0 ≤ Q(t) ≤ 1` on the grid.
  have hcbt_pos : ∀ t : ℕ, t ≤ b → (0 : ℝ) < ((b.choose t : ℕ) : ℝ) := by
    intro t ht
    exact_mod_cast Nat.choose_pos ht
  have hQ_lo : ∀ t : ℕ, t ≤ b → 0 ≤ Q.eval (t : ℝ) := by
    intro t ht
    have heq := hQ_eval' t ht
    have hsum_nonneg : (0 : ℝ) ≤ ∑ y ∈ (univ : Finset (Fin b → Bool)).filter
        (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t),
        (if g y = true then (1 : ℝ) else 0) := by
      refine Finset.sum_nonneg ?_
      intro y _; split_ifs <;> norm_num
    rw [← heq] at hsum_nonneg
    nlinarith [hsum_nonneg, hcbt_pos t ht]
  have hQ_hi : ∀ t : ℕ, t ≤ b → Q.eval (t : ℝ) ≤ 1 := by
    intro t ht
    have heq := hQ_eval' t ht
    have hsum_le : (∑ y ∈ (univ : Finset (Fin b → Bool)).filter
        (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t),
        (if g y = true then (1 : ℝ) else 0))
        ≤ ((b.choose t : ℕ) : ℝ) := by
      calc (∑ y ∈ (univ : Finset (Fin b → Bool)).filter
          (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t),
          (if g y = true then (1 : ℝ) else 0))
          ≤ ∑ _y ∈ (univ : Finset (Fin b → Bool)).filter
            (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t),
            (1 : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro y _; split_ifs <;> norm_num
        _ = ((b.choose t : ℕ) : ℝ) := by
            rw [Finset.sum_const, card_slice ht, nsmul_eq_mul, mul_one]
    rw [← heq] at hsum_le
    have hle : Q.eval (t : ℝ) * ((b.choose t : ℕ) : ℝ) ≤ 1 * ((b.choose t : ℕ) : ℝ) := by
      linarith
    exact le_of_mul_le_mul_right hle (hcbt_pos t ht)
  -- Adaptation: return the checked symmetrization and grid bounds for the curvature lemmas.
  exact ⟨Q, hQd, hQ0, hQ1, hQ_lo, hQ_hi⟩

end BooleanSymmetry

open Polynomial Set
namespace ProskurinDerivative

theorem rolle (p : Polynomial ℝ) (a b : ℝ) (hab : a < b)
    (h : p.eval a = p.eval b) :
    ∃ x ∈ Ioo a b, p.derivative.eval x = 0 := by
  exact exists_hasDerivAt_eq_zero hab p.continuous.continuousOn h
    (fun x _ => p.hasDerivAt x)

theorem rolle_three (p : Polynomial ℝ) (a b c : ℝ)
    (hab : a < b) (hbc : b < c)
    (ha : p.eval a = 0) (hb : p.eval b = 0) (hc : p.eval c = 0) :
    ∃ x ∈ Ioo a c, p.derivative.derivative.eval x = 0 := by
  obtain ⟨u, hu, hpu⟩ := rolle p a b hab (ha.trans hb.symm)
  obtain ⟨v, hv, hpv⟩ := rolle p b c hbc (hb.trans hc.symm)
  obtain ⟨x, hx, hpx⟩ := rolle p.derivative u v (hu.2.trans hv.1) (hpu.trans hpv.symm)
  exact ⟨x, ⟨hu.1.trans hx.1, hx.2.trans hv.2⟩, hpx⟩

theorem rolle_four (p : Polynomial ℝ) (a b c d : ℝ)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : p.eval a = 0) (hb : p.eval b = 0)
    (hc : p.eval c = 0) (hd : p.eval d = 0) :
    ∃ x ∈ Ioo a d, p.derivative.derivative.derivative.eval x = 0 := by
  obtain ⟨u, hu, hpu⟩ := rolle p a b hab (ha.trans hb.symm)
  obtain ⟨v, hv, hpv⟩ := rolle p b c hbc (hb.trans hc.symm)
  obtain ⟨z, hz, hpz⟩ := rolle p c d hcd (hc.trans hd.symm)
  obtain ⟨x, hx, hpx⟩ := rolle_three p.derivative u v z
    (hu.2.trans hv.1) (hv.2.trans hz.1) hpu hpv hpz
  exact ⟨x, ⟨hu.1.trans hx.1, hx.2.trans hz.2⟩, hpx⟩

noncomputable def cubic (u v : ℝ) : Polynomial ℝ :=
  C (1/6 : ℝ) * X * (X - C 3) * (X - C 4) -
    C (u/6) * X * (X - C 1) * (X - C 4) +
    C (v/12) * X * (X - C 1) * (X - C 3)

theorem cubic_values (u v : ℝ) :
    (cubic u v).eval 0 = 0 ∧ (cubic u v).eval 1 = 1 ∧
      (cubic u v).eval 3 = u ∧ (cubic u v).eval 4 = v := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [cubic] <;> ring

theorem cubic_third (u v x : ℝ) :
    (cubic u v).derivative.derivative.derivative.eval x = 1 - u + v/2 := by
  simp [cubic, derivative_mul, derivative_sub, derivative_add]
  <;> ring

theorem third_witness (p : Polynomial ℝ) (h0 : p.eval 0 = 0) (h1 : p.eval 1 = 1) :
    ∃ x ∈ Ioo (0 : ℝ) 4,
      p.derivative.derivative.derivative.eval x = 1 - p.eval 3 + p.eval 4 / 2 := by
  let q := cubic (p.eval 3) (p.eval 4)
  have hq := cubic_values (p.eval 3) (p.eval 4)
  obtain ⟨x, hx, hp⟩ := rolle_four (p-q) 0 1 3 4 (by norm_num) (by norm_num)
    (by norm_num) (by simp [q, h0, hq.1]) (by simp [q, h1, hq.2.1])
    (by simp [q, hq.2.2.1]) (by simp [q, hq.2.2.2])
  refine ⟨x, hx, ?_⟩
  simp only [derivative_sub, eval_sub] at hp
  have hq3 := cubic_third (p.eval 3) (p.eval 4) x
  change p.derivative.derivative.derivative.eval x -
    (cubic (p.eval 3) (p.eval 4)).derivative.derivative.derivative.eval x = 0 at hp
  linarith

theorem lemma_two (p : Polynomial ℝ) (h0 : p.eval 0 = 0) (h1 : p.eval 1 = 1)
    (h4 : 0 ≤ p.eval 4) :
    ∃ x ∈ Ioo (0 : ℝ) 4, 1 - p.eval 3 ≤ |p.derivative.derivative.derivative.eval x| := by
  obtain ⟨x, hx, hp⟩ := third_witness p h0 h1
  exact ⟨x, hx, le_trans (by linarith) (le_abs_self _)⟩

noncomputable def quadratic (u : ℝ) : Polynomial ℝ :=
  C (u / 2 - 1) * X^2 + C (2 - u / 2) * X

theorem quadratic_values (u : ℝ) :
    (quadratic u).eval 0 = 0 ∧ (quadratic u).eval 1 = 1 ∧
      (quadratic u).eval 2 = u := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [quadratic] <;> ring

theorem quadratic_second (u x : ℝ) :
    (quadratic u).derivative.derivative.eval x = u - 2 := by
  simp [quadratic, derivative_mul, derivative_add, derivative_pow]
  <;> ring

theorem second_witness (p : Polynomial ℝ) (h0 : p.eval 0 = 0) (h1 : p.eval 1 = 1) :
    ∃ x ∈ Ioo (0 : ℝ) 2, p.derivative.derivative.eval x = p.eval 2 - 2 := by
  let q := quadratic (p.eval 2)
  have hq := quadratic_values (p.eval 2)
  obtain ⟨x, hx, hp⟩ := rolle_three (p-q) 0 1 2 (by norm_num) (by norm_num)
    (by simp [q, h0, hq.1]) (by simp [q, h1, hq.2.1]) (by simp [q, hq.2.2])
  refine ⟨x, hx, ?_⟩
  simp only [derivative_sub, eval_sub] at hp
  have hq2 := quadratic_second (p.eval 2) x
  change p.derivative.derivative.eval x -
    (quadratic (p.eval 2)).derivative.derivative.eval x = 0 at hp
  linarith

theorem warmup_curvature (p : Polynomial ℝ) (h0 : p.eval 0 = 0)
    (h1 : p.eval 1 = 1) (h2 : p.eval 2 ≤ 1) :
    ∃ x ∈ Ioo (0 : ℝ) 2, 1 ≤ |p.derivative.derivative.eval x| := by
  obtain ⟨x, hx, hp⟩ := second_witness p h0 h1
  exact ⟨x, hx, le_trans (by linarith) (neg_le_abs _)⟩

theorem third_grid (p : Polynomial ℝ) (n : ℕ) (hn : 4 ≤ n)
    (h0 : p.eval 0 = 0) (h1 : p.eval 1 = 1)
    (hlo : ∀ k : ℕ, k ≤ n → 0 ≤ p.eval (k : ℝ)) :
    ∃ x ∈ Icc (0 : ℝ) n, 1 - p.eval 3 ≤ |p.derivative.derivative.derivative.eval x| := by
  obtain ⟨x, hx, hp⟩ := lemma_two p h0 h1 (by simpa using hlo 4 hn)
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨x, ⟨le_of_lt hx.1, le_trans (le_of_lt hx.2) hn'⟩, hp⟩

theorem low_third_value (p : Polynomial ℝ) (h0 : p.eval 0 = 0)
    (h1 : p.eval 1 = 1) (h4 : 0 ≤ p.eval 4) (h3 : p.eval 3 < 3/8) :
    ∃ x ∈ Ioo (0 : ℝ) 4, (5/8 : ℝ) < |p.derivative.derivative.derivative.eval x| := by
  obtain ⟨x, hx, hp⟩ := lemma_two p h0 h1 h4
  exact ⟨x, hx, by linarith⟩

theorem first_derivative_ratio (x : ℝ) (hx : 0 ≤ x)
    (h : (1 - x^2/6) * (3/2) ≤ x) : Real.sqrt 10 - 2 ≤ x := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
  have hp := Real.sqrt_nonneg (10 : ℝ)
  nlinarith [sq_nonneg (x + 2 - Real.sqrt 10)]

theorem third_derivative_ratio (x : ℝ) (hx : 0 ≤ x)
    (h : (1 - x^2/6) * (75/32) < x^3) : (6/5 : ℝ) < x := by
  by_contra hn
  have hle : x ≤ 6/5 := le_of_not_gt hn
  have hs : x^2 ≤ (6/5 : ℝ)^2 := sq_le_sq₀ hx (by norm_num) |>.mpr hle
  have hc : x^3 ≤ (6/5 : ℝ)^3 := pow_le_pow_left₀ hx hle 3
  nlinarith

theorem fourth_value_hypothesis_needed :
    (quadratic 1).eval 0 = 0 ∧ (quadratic 1).eval 1 = 1 ∧
    (quadratic 1).eval 3 = 0 ∧ (quadratic 1).eval 4 = -2 ∧
    ∀ x : ℝ, (quadratic 1).derivative.derivative.derivative.eval x = 0 := by
  norm_num [quadratic, derivative_mul, derivative_add, derivative_pow]

theorem cubic_sharp_control (x : ℝ) :
    (cubic (3/8) 0).derivative.derivative.derivative.eval x = (5/8 : ℝ) := by
  rw [cubic_third]
  norm_num

end ProskurinDerivative

namespace ProskurinDerivative

theorem normalized_curvature {n : ℕ} (hn : 4 ≤ n) (g : BoolFunc n)
    (h0 : g (fun _ => false) = false)
    (hunit : ∀ i : Fin n, g (Function.update (fun _ => false) i true) = true) :
    ∃ Q : Polynomial ℝ, Q.natDegree ≤ polyDegree g ∧ Q.eval 0 = 0 ∧ Q.eval 1 = 1 ∧
      (∀ k : ℕ, k ≤ n → 0 ≤ Q.eval (k : ℝ) ∧ Q.eval (k : ℝ) ≤ 1) ∧
      (∃ x ∈ Set.Icc (0 : ℝ) n, 1 ≤ |Q.derivative.derivative.eval x|) ∧
      (∃ x ∈ Set.Icc (0 : ℝ) n,
        1 - Q.eval 3 ≤ |Q.derivative.derivative.derivative.eval x|) := by
  obtain ⟨Q, hd, hz, ho, hlo, hhi⟩ := BooleanSymmetry.solution (by omega) g h0 hunit
  refine ⟨Q, hd, hz, ho, fun k hk => ⟨hlo k hk, hhi k hk⟩, ?_, third_grid Q n hn hz ho hlo⟩
  obtain ⟨x, hx, hp⟩ := warmup_curvature Q hz ho (by simpa using hhi 2 (by omega))
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  exact ⟨x, ⟨le_of_lt hx.1, (le_of_lt hx.2).trans hn'⟩, hp⟩

end ProskurinDerivative

namespace ProskurinDerivative

theorem iterated_rolle (k : ℕ) (p : Polynomial ℝ) (a b : ℝ)
    (z : Fin (k+1) → ℝ) (hz : StrictMono z)
    (hm : ∀ i, z i ∈ Set.Icc a b) (hr : ∀ i, p.eval (z i) = 0) :
    ∃ x ∈ Set.Icc a b, ((Polynomial.derivative^[k]) p).eval x = 0 := by
  induction k generalizing p with
  | zero => exact ⟨z 0, hm 0, hr 0⟩
  | succ k ih =>
    have hstep : ∀ i : Fin (k+1), ∃ y ∈ Set.Ioo (z i.castSucc) (z i.succ),
        p.derivative.eval y = 0 := by
      intro i
      exact rolle p _ _ (hz (by simp)) ((hr _).trans (hr _).symm)
    choose y hy hyr using hstep
    have hys : StrictMono y := by
      intro i j hij
      have hmid : z i.succ ≤ z j.castSucc := hz.monotone (by
        change i.val + 1 ≤ j.val
        exact hij)
      exact (hy i).2.trans_le (hmid.trans (le_of_lt (hy j).1))
    have hym : ∀ i, y i ∈ Set.Icc a b := by
      intro i
      exact ⟨(hm i.castSucc).1.trans (le_of_lt (hy i).1),
        (le_of_lt (hy i).2).trans (hm i.succ).2⟩
    obtain ⟨x, hx, hp⟩ := ih p.derivative y hys hym hyr
    exact ⟨x, hx, by simpa only [Function.iterate_succ_apply] using hp⟩

theorem matching_grid_derivative (k : ℕ) (p q : Polynomial ℝ)
    (h : ∀ j : ℕ, j ≤ k → p.eval (j : ℝ) = q.eval (j : ℝ)) :
    ∃ x ∈ Set.Icc (0 : ℝ) k,
      ((Polynomial.derivative^[k]) p).eval x = ((Polynomial.derivative^[k]) q).eval x := by
  obtain ⟨x, hx, hp⟩ := iterated_rolle k (p-q) 0 k (fun i => (i.val : ℝ))
    (by intro i j hij; change (i.val : ℝ) < (j.val : ℝ); exact_mod_cast hij)
    (by intro i; exact ⟨Nat.cast_nonneg _, by exact_mod_cast (show i.val ≤ k by omega)⟩)
    (by intro i; simp only [eval_sub]; exact sub_eq_zero.mpr (h i.val (by omega)))
  exact ⟨x, hx, by simpa only [Polynomial.iterate_derivative_sub, eval_sub, sub_eq_zero] using hp⟩

end ProskurinDerivative

namespace ProskurinDerivative

theorem derivative_of_degree_le (k : ℕ) (q : Polynomial ℝ) (hq : q.natDegree ≤ k) :
    (Polynomial.derivative^[k]) q = Polynomial.C ((k.factorial : ℝ) * q.coeff k) := by
  ext m
  by_cases hm : m = 0
  · subst m
    simp [Polynomial.coeff_iterate_derivative, Nat.descFactorial_self, nsmul_eq_mul]
  · have hmk : q.natDegree < m + k := by omega
    rw [Polynomial.coeff_iterate_derivative, Polynomial.coeff_eq_zero_of_natDegree_lt hmk]
    simp [hm]

theorem interpolation_coefficient_witness (k : ℕ) (p q : Polynomial ℝ)
    (hq : q.natDegree ≤ k)
    (h : ∀ j : ℕ, j ≤ k → p.eval (j : ℝ) = q.eval (j : ℝ)) :
    ∃ x ∈ Set.Icc (0 : ℝ) k,
      ((Polynomial.derivative^[k]) p).eval x = (k.factorial : ℝ) * q.coeff k := by
  obtain ⟨x, hx, he⟩ := matching_grid_derivative k p q h
  rw [derivative_of_degree_le k q hq, Polynomial.eval_C] at he
  exact ⟨x, hx, he⟩

end ProskurinDerivative

end
end CarriedDerivative

namespace CarriedNormal
section
open MvPolynomial
namespace DegreeNormal
noncomputable section
open Classical

lemma degree_substitute {n m : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (q : Fin n → MvPolynomial (Fin m) ℝ) (hq : ∀ i, (q i).totalDegree ≤ 1) :
    (eval₂ C q p).totalDegree ≤ p.totalDegree := by
  rw [eval₂_eq]
  apply totalDegree_finsetSum_le
  intro d hd
  calc
    (C (p.coeff d) * ∏ i ∈ d.support, q i ^ d i).totalDegree
        ≤ (C (p.coeff d)).totalDegree + (∏ i ∈ d.support, q i ^ d i).totalDegree :=
      totalDegree_mul _ _
    _ = (∏ i ∈ d.support, q i ^ d i).totalDegree := by simp
    _ ≤ ∑ i ∈ d.support, (q i ^ d i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hq i))
    _ ≤ p.totalDegree := le_totalDegree hd

def lift {n m : ℕ} (t : Finset (Fin n)) (E : t ≃ Fin m)
    (x : Fin n → Bool) (y : Fin m → Bool) : Fin n → Bool :=
  fun i => if h : i ∈ t then if y (E ⟨i,h⟩) then !x i else x i else x i

lemma lift_zero {n m : ℕ} (t : Finset (Fin n)) (E : t ≃ Fin m) (x : Fin n → Bool) :
    lift t E x (fun _ => false) = x := by
  funext i
  simp [lift]

lemma lift_unit {n m : ℕ} (t : Finset (Fin n)) (E : t ≃ Fin m)
    (x : Fin n → Bool) (j : Fin m) :
    lift t E x (Function.update (fun _ => false) j true) =
      flipBit x (E.symm j).val := by
  funext i
  by_cases hi : i ∈ t
  · have he : E ⟨i,hi⟩ = j ↔ i = (E.symm j).val := by
      constructor
      · intro h
        have := congrArg E.symm h
        simpa using congrArg Subtype.val this
      · intro h
        have h' : (⟨i,hi⟩ : t) = E.symm j := Subtype.ext h
        simpa [h']
    by_cases hij : i = (E.symm j).val
    · have hj : E ⟨i,hi⟩ = j := he.mpr hij
      simp [lift, hi, hj, flipBit, hij]
    · have hj : E ⟨i,hi⟩ ≠ j := fun h => hij (he.mp h)
      simp [lift, hi, Function.update_of_ne hj, flipBit, Function.update_of_ne hij]
  · have hij : i ≠ (E.symm j).val := by
      intro h
      exact hi (h ▸ (E.symm j).property)
    simp [lift, hi, flipBit, Function.update_of_ne hij]

def substitution {n m : ℕ} (t : Finset (Fin n)) (E : t ≃ Fin m)
    (x : Fin n → Bool) : Fin n → MvPolynomial (Fin m) ℝ :=
  fun i => if h : i ∈ t then if x i then 1 - X (E ⟨i,h⟩) else X (E ⟨i,h⟩)
    else C (if x i then 1 else 0)

lemma substitution_degree {n m : ℕ} (t : Finset (Fin n)) (E : t ≃ Fin m)
    (x : Fin n → Bool) (i : Fin n) : (substitution t E x i).totalDegree ≤ 1 := by
  unfold substitution
  split_ifs
  · exact (totalDegree_sub _ _).trans (by simp)
  · simp
  · simp
  · simp

lemma substitution_eval {n m : ℕ} (t : Finset (Fin n)) (E : t ≃ Fin m)
    (x : Fin n → Bool) (y : Fin m → Bool) (i : Fin n) :
    eval (fun j => if y j then (1:ℝ) else 0) (substitution t E x i) =
      if lift t E x y i then 1 else 0 := by
  by_cases hi : i ∈ t
  · cases hx : x i <;> cases hy : y (E ⟨i,hi⟩) <;> simp [substitution, lift, hi, hx, hy]
  · simp [substitution, lift, hi]

lemma normalized_degree {n m d : ℕ} (f : BoolFunc n) (hf : polyDegree f ≤ d)
    (t : Finset (Fin n)) (E : t ≃ Fin m) (x : Fin n → Bool) :
    polyDegree (fun y => if f x then !(f (lift t E x y)) else f (lift t E x y)) ≤ d := by
  obtain ⟨p,hp,hval⟩ := (show HasPolyRep f (polyDegree f) from Nat.find_spec _)
  let P := eval₂ C (substitution t E x) p
  have hP : P.totalDegree ≤ d :=
    (degree_substitute p _ (substitution_degree t E x)).trans (hp.trans hf)
  have hEval (y : Fin m → Bool) :
      eval (fun j => if y j then (1:ℝ) else 0) P = if f (lift t E x y) then 1 else 0 := by
    dsimp [P]
    rw [← eval_assoc]
    have he : (eval (fun j => if y j then (1:ℝ) else 0) ∘ substitution t E x) =
        (fun i => if lift t E x y i then (1:ℝ) else 0) := by
      funext i
      exact substitution_eval t E x y i
    rw [he]
    exact hval _
  apply Nat.find_min'
  refine ⟨if f x then 1-P else P, ?_, ?_⟩
  · split_ifs
    · exact (totalDegree_sub _ _).trans (by simpa using hP)
    · exact hP
  · intro y
    cases hx : f x <;> cases hy : f (lift t E x y) <;> simp [hx, hy, hEval y]

theorem normal_form :
    (∃ (n : ℕ) (f : BoolFunc n), polyDegree f ≤ 5 ∧ 14 ≤ sensitivity f) ↔
      ∃ g : BoolFunc 14, polyDegree g ≤ 5 ∧ g (fun _ => false) = false ∧
        ∀ i : Fin 14, g (Function.update (fun _ => false) i true) = true := by
  constructor
  · rintro ⟨n,f,hdeg,hs⟩
    obtain ⟨x,hx,hmax⟩ := Finset.exists_mem_eq_sup
      (Finset.univ : Finset (Fin n → Bool)) (by simp) (sensitivityAt f)
    have hcard : 14 ≤ (Finset.univ.filter (fun i => f (flipBit x i) ≠ f x)).card := by
      simpa [sensitivity, hmax, sensitivityAt] using hs
    obtain ⟨t,ht,hsize⟩ := Finset.exists_subset_card_eq hcard
    let E : t ≃ Fin 14 := t.equivFinOfCardEq hsize
    let g : BoolFunc 14 := fun y => if f x then !(f (lift t E x y)) else f (lift t E x y)
    refine ⟨g, normalized_degree f hdeg t E x, ?_, ?_⟩
    · simp [g, lift_zero]
    · intro j
      have hne : f (flipBit x (E.symm j).val) ≠ f x :=
        (Finset.mem_filter.mp (ht (E.symm j).property)).2
      dsimp [g]
      rw [lift_unit]
      cases hx : f x <;> cases hy : f (flipBit x (E.symm j).val) <;> simp_all
  · rintro ⟨g,hdeg,hzero,hunits⟩
    refine ⟨14,g,hdeg,?_⟩
    have hpoint : sensitivityAt g (fun _ => false) = 14 := by
      unfold sensitivityAt
      have hfilter : (Finset.univ.filter (fun i : Fin 14 =>
          g (flipBit (fun _ => false) i) ≠ g (fun _ => false))) = Finset.univ := by
        ext i
        simp [flipBit, hzero, hunits]
      rw [hfilter]
      simp
    calc
      14 = sensitivityAt g (fun _ => false) := hpoint.symm
      _ ≤ sensitivity g := Finset.le_sup (Finset.mem_univ _)

end
end DegreeNormal
theorem solution :
    (∃ (n : ℕ) (f : BoolFunc n), polyDegree f ≤ 5 ∧ 14 ≤ sensitivity f) ↔
      ∃ g : BoolFunc 14, polyDegree g ≤ 5 ∧ g (fun _ => false) = false ∧
        ∀ i : Fin 14, g (Function.update (fun _ => false) i true) = true :=
  DegreeNormal.normal_form

end
end CarriedNormal

open MeasureTheory Polynomial Finset
namespace AmanoTen
noncomputable section
open Classical

def weight {n : ℕ} (x : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i => x i = true)).card
def slice (n k : ℕ) : Finset (Fin n → Bool) := Finset.univ.filter (fun x => weight x = k)
def count {n : ℕ} (f : BoolFunc n) (k : ℕ) : ℕ := ((slice n k).filter (fun x => f x = true)).card

lemma slice_card {n k : ℕ} (hk : k ≤ n) : (slice n k).card = n.choose k :=
  CarriedDerivative.BooleanSymmetry.PDUBSketch.card_slice hk

lemma average {n : ℕ} (f : BoolFunc n) : ∃ Q : Polynomial ℝ,
    Q.natDegree ≤ polyDegree f ∧
    (∀ k : ℕ, k ≤ n → Q.eval (k:ℝ)*(n.choose k:ℝ) = (count f k:ℝ)) ∧
    (∀ k : ℕ, k ≤ n → 0 ≤ Q.eval (k:ℝ) ∧ Q.eval (k:ℝ) ≤ 1) := by
  obtain ⟨p,hp,hval⟩ := (show HasPolyRep f (polyDegree f) from Nat.find_spec _)
  obtain ⟨Q,hQ,hvalQ⟩ := CarriedDerivative.SymmetrizationReplay.solution p
  have he : ∀ k : ℕ, k ≤ n → Q.eval (k:ℝ)*(n.choose k:ℝ) = (count f k:ℝ) := by
    intro k hk
    rw [hvalQ k hk]
    simp_rw [hval]
    simp only [count,slice,weight,Finset.sum_boole, Nat.cast_inj]
    congr 1
  refine ⟨Q,hQ.trans hp,he,?_⟩
  intro k hk
  have hpos : (0:ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  have hle : count f k ≤ n.choose k := by
    rw [← slice_card hk]
    exact Finset.card_filter_le _ _
  have hz : (0:ℝ) ≤ count f k := by positivity
  have hc : (count f k:ℝ) ≤ n.choose k := by exact_mod_cast hle
  have hh := he k hk
  constructor <;> nlinarith

lemma count_zero {n : ℕ} (f : BoolFunc n) (k : ℕ) (h : count f k = 0)
    (x : Fin n → Bool) (hx : weight x = k) : f x = false := by
  have he : (slice n k).filter (fun y => f y = true) = ∅ := Finset.card_eq_zero.mp h
  have hmem : x ∈ slice n k := by simp [slice,hx]
  cases hf : f x
  · rfl
  · have : x ∈ (slice n k).filter (fun y => f y = true) := Finset.mem_filter.mpr ⟨hmem,hf⟩
    rw [he] at this
    exact (Finset.notMem_empty x this).elim
lemma count_full {n : ℕ} (f : BoolFunc n) (k : ℕ) (hk : k ≤ n)
    (h : count f k = n.choose k) (x : Fin n → Bool) (hx : weight x = k) : f x = true := by
  have he : (slice n k).filter (fun y => f y = true) = slice n k := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    rw [slice_card hk]
    exact h.ge
  have hm : x ∈ (slice n k).filter (fun y => f y = true) := by rw [he]; simp [slice,hx]
  exact (Finset.mem_filter.mp hm).2

lemma count_of_constant {n : ℕ} (f : BoolFunc n) (k : ℕ) (hk : k ≤ n) (v : Bool)
    (h : ∀ x, weight x = k → f x = v) : count f k = if v then n.choose k else 0 := by
  unfold count
  cases v
  · have he : (slice n k).filter (fun x => f x = true) = ∅ := by
      ext x
      simp only [Finset.mem_filter,Finset.notMem_empty,iff_false,not_and]
      intro hx
      have hw : weight x = k := (Finset.mem_filter.mp hx).2
      simp [h x hw]
    simp [he]
  · have he : (slice n k).filter (fun x => f x = true) = slice n k := by
      ext x
      simp only [Finset.mem_filter,and_iff_left_iff_imp]
      intro hx
      exact h x (Finset.mem_filter.mp hx).2
    simp [he,slice_card hk]

lemma quartic_eval (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ 4) (x : ℝ) :
    Q.eval x = Q.coeff 0 + Q.coeff 1*x + Q.coeff 2*x^2 + Q.coeff 3*x^3 + Q.coeff 4*x^4 := by
  rw [Polynomial.eval_eq_sum_range' (show Q.natDegree < 5 by omega)]
  norm_num [Finset.sum_range_succ]

lemma forced_quartic (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ 4)
    (h0 : Q.eval 0 = 0) (h1 : Q.eval 1 = 1)
    (hb : ∀ k : ℕ, k ≤ 10 → 0 ≤ Q.eval (k:ℝ) ∧ Q.eval (k:ℝ) ≤ 1) :
    Q.eval 2 = 1 ∧ Q.eval 5 = 0 ∧ Q.eval 8 = 1 := by
  have h2 := hb 2 (by norm_num)
  have h5 := hb 5 (by norm_num)
  have h8 := hb 8 (by norm_num)
  have h9 := hb 9 (by norm_num)
  have h10 := hb 10 (by norm_num)
  simp only [quartic_eval Q hQ] at h0 h1 h2 h5 h8 h9 h10 ⊢
  norm_num at h0 h1 h2 h5 h8 h9 h10 ⊢
  constructor
  · linarith
  constructor <;> linarith

lemma restricted_value (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ 4)
    (h0 : Q.eval 0 = 0) (h1 : Q.eval 1 = 1) (h2 : Q.eval 2 = 1)
    (h5 : Q.eval 5 = 0) (h8 : Q.eval 8 = 1) : Q.eval 3 = 7/12 := by
  simp only [quartic_eval Q hQ] at h0 h1 h2 h5 h8 ⊢
  norm_num at h0 h1 h2 h5 h8 ⊢
  linarith

end
end AmanoTen

namespace AmanoTen
noncomputable section
open Classical
lemma on_zero {n : ℕ} (g : BoolFunc n) (h0 : g (fun _ => false) = false)
    (x : Fin n → Bool) (hx : weight x = 0) : g x = false := by
  have he : x = fun _ => false := by
    have hem : Finset.univ.filter (fun i => x i = true) = ∅ := Finset.card_eq_zero.mp hx
    funext i
    cases hxi : x i
    · rfl
    · have hh : i ∈ Finset.univ.filter (fun i => x i = true) := by simp [hxi]
      rw [hem] at hh
      exact (Finset.notMem_empty i hh).elim
  simpa [he] using h0
lemma on_one {n : ℕ} (g : BoolFunc n)
    (h1 : ∀ i, g (Function.update (fun _ => false) i true) = true)
    (x : Fin n → Bool) (hx : weight x = 1) : g x = true := by
  apply CarriedDerivative.BooleanSymmetry.PDUBSketch.slice_one_val g h1 x
  simp [weight] at hx
  simpa using hx
lemma average_constant {n : ℕ} (f : BoolFunc n) (Q : Polynomial ℝ)
    (he : ∀ k : ℕ, k ≤ n → Q.eval (k:ℝ)*(n.choose k:ℝ) = (count f k:ℝ))
    (k : ℕ) (hk : k ≤ n) (v : Bool) (h : ∀ x, weight x = k → f x = v) :
    Q.eval (k:ℝ) = if v then 1 else 0 := by
  have hc := count_of_constant f k hk v h
  have hh := he k hk
  have hp : (0:ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  cases v <;> simp at hc ⊢ <;> rw [hc] at hh <;> (try simp only [Nat.cast_zero] at hh) <;> nlinarith only [hh,hp]

lemma normalize (f : BoolFunc 10) (hd : polyDegree f ≤ 4) (hs : sensitivity f = 10) :
    ∃ g : BoolFunc 10, polyDegree g ≤ 4 ∧ g (fun _ => false) = false ∧
      ∀ i, g (Function.update (fun _ => false) i true) = true := by
  obtain ⟨x,hx,hmax⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Fin 10 → Bool)) (by simp) (sensitivityAt f)
  have hcard : 10 ≤ (Finset.univ.filter (fun i => f (flipBit x i) ≠ f x)).card := by
    simpa [sensitivity,hmax,sensitivityAt] using hs.ge
  obtain ⟨t,ht,hsize⟩ := Finset.exists_subset_card_eq hcard
  let E : t ≃ Fin 10 := t.equivFinOfCardEq hsize
  let g : BoolFunc 10 := fun y => if f x then !(f (CarriedNormal.DegreeNormal.lift t E x y))
    else f (CarriedNormal.DegreeNormal.lift t E x y)
  refine ⟨g,CarriedNormal.DegreeNormal.normalized_degree f hd t E x,?_,?_⟩
  · simp [g,CarriedNormal.DegreeNormal.lift_zero]
  · intro j
    have hne : f (flipBit x (E.symm j).val) ≠ f x :=
      (Finset.mem_filter.mp (ht (E.symm j).property)).2
    dsimp [g]
    rw [CarriedNormal.DegreeNormal.lift_unit]
    cases hx : f x <;> cases hy : f (flipBit x (E.symm j).val) <;> simp_all

def extend (y : Fin 8 → Bool) : Fin 10 → Bool := fun i => Fin.addCases y (fun _ : Fin 2 => false) i
lemma weight_extend (y : Fin 8 → Bool) : weight (extend y) = weight y := by
  unfold weight
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Fin.sum_univ_add (a := 8) (b := 2)]
  simp [extend]
lemma restrict_degree (f : BoolFunc 10) : polyDegree (fun y => f (extend y)) ≤ polyDegree f := by
  obtain ⟨p,hp,hval⟩ := (show HasPolyRep f (polyDegree f) from Nat.find_spec _)
  let q : Fin 10 → MvPolynomial (Fin 8) ℝ := fun i => Fin.addCases (fun j : Fin 8 => MvPolynomial.X j) (fun _ : Fin 2 => 0) i
  have hq : ∀ i, (q i).totalDegree ≤ 1 := by
    intro i
    refine Fin.addCases (m := 8) (n := 2) (fun j => ?_) (fun j => ?_) i <;> simp [q]
  apply Nat.find_min'
  refine ⟨MvPolynomial.eval₂ MvPolynomial.C q p,
    (CarriedNormal.DegreeNormal.degree_substitute p q hq).trans hp,?_⟩
  intro y
  rw [← MvPolynomial.eval_assoc]
  have he : (MvPolynomial.eval (fun j => if y j then (1:ℝ) else 0) ∘ q) =
      (fun i => if extend y i then (1:ℝ) else 0) := by
    funext i
    refine Fin.addCases (m := 8) (n := 2) (fun j => ?_) (fun j => ?_) i <;> simp [q,extend]
  rw [he]
  exact hval _

lemma no_normalized (g : BoolFunc 10) (hd : polyDegree g ≤ 4)
    (h0 : g (fun _ => false) = false)
    (h1 : ∀ i, g (Function.update (fun _ => false) i true) = true) : False := by
  obtain ⟨Q,hQ,he,hb⟩ := average g
  have hQ0 : Q.eval 0 = 0 := by simpa using average_constant g Q he 0 (by omega) false (on_zero g h0)
  have hQ1 : Q.eval 1 = 1 := by simpa using average_constant g Q he 1 (by omega) true (on_one g h1)
  obtain ⟨hQ2,hQ5,hQ8⟩ := forced_quartic Q (hQ.trans hd) hQ0 hQ1 hb
  have hc2 : count g 2 = (10:ℕ).choose 2 := by
    have hh := he 2 (by omega)
    norm_num [hQ2] at hh ⊢
    exact_mod_cast hh.symm
  have hc5 : count g 5 = 0 := by
    have hh := he 5 (by omega)
    norm_num [hQ5] at hh
    exact_mod_cast hh.symm
  have hc8 : count g 8 = (10:ℕ).choose 8 := by
    have hh := he 8 (by omega)
    norm_num [hQ8] at hh ⊢
    exact_mod_cast hh.symm
  let f : BoolFunc 8 := fun y => g (extend y)
  obtain ⟨R,hR,her,hbr⟩ := average f
  have hR0 : R.eval 0 = 0 := by
    simpa using average_constant f R her 0 (by omega) false
      (fun x hx => on_zero g h0 _ ((weight_extend x).trans hx))
  have hR1 : R.eval 1 = 1 := by
    simpa using average_constant f R her 1 (by omega) true
      (fun x hx => on_one g h1 _ ((weight_extend x).trans hx))
  have hR2 : R.eval 2 = 1 := by
    apply average_constant f R her 2 (by omega) true
    intro x hx
    exact count_full g 2 (by omega) hc2 _ ((weight_extend x).trans hx)
  have hR5 : R.eval 5 = 0 := by
    apply average_constant f R her 5 (by omega) false
    intro x hx
    exact count_zero g 5 hc5 _ ((weight_extend x).trans hx)
  have hR8 : R.eval 8 = 1 := by
    apply average_constant f R her 8 (by omega) true
    intro x hx
    exact count_full g 8 (by omega) hc8 _ ((weight_extend x).trans hx)
  have hR3 := restricted_value R (hR.trans ((restrict_degree g).trans hd)) hR0 hR1 hR2 hR5 hR8
  have hc := her 3 (by omega)
  norm_num [hR3,Nat.choose] at hc
  have hz : (3:ℝ)*(count f 3:ℝ) = 98 := by linarith
  have hn : 3*count f 3 = 98 := by exact_mod_cast hz
  omega
end
end AmanoTen

theorem solution : ¬ ∃ f : BoolFunc 10, polyDegree f ≤ 4 ∧ sensitivity f = 10 := by
  rintro ⟨f,hd,hs⟩
  obtain ⟨g,hg,h0,h1⟩ := AmanoTen.normalize f hd hs
  exact AmanoTen.no_normalized g hg h0 h1

namespace AmanoTen
noncomputable def relaxedQuartic : Polynomial ℝ :=
  X - C (1/2)*X*(X-1) + C (7/72)*X*(X-1)*(X-2) - C (1/144)*X*(X-1)*(X-2)*(X-3)
/-- A feasible real polynomial exists: the Boolean slice integrality is essential. -/
theorem relaxation_control : relaxedQuartic.natDegree ≤ 4 ∧
    relaxedQuartic.eval 0 = 0 ∧ relaxedQuartic.eval 1 = 1 ∧
    (∀ k : Fin 11, 0 ≤ relaxedQuartic.eval (k:ℝ) ∧ relaxedQuartic.eval (k:ℝ) ≤ 1) ∧
    relaxedQuartic.eval 3 = 7/12 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · unfold relaxedQuartic
    compute_degree
  · norm_num [relaxedQuartic]
  · norm_num [relaxedQuartic]
  · intro k
    fin_cases k <;> norm_num [relaxedQuartic]
  · norm_num [relaxedQuartic]
end AmanoTen
