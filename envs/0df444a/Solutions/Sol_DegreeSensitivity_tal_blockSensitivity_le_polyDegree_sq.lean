-- Prove2me | solution 1 for DegreeSensitivity.tal_blockSensitivity_le_polyDegree_sq
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-15T20:06:59.058646+00:00
-- url     : https://prove2.me/submissions/6f2ee94d-3d7c-4736-9bd6-09e06b904bf6

import Mathlib
import Definitions.Def_BoolFunc
import Definitions.Def_polyDegree
import Definitions.Def_blockSensitivity


namespace CommunityReplay_64b5f1b7_2bc9_48de_8b63_4b6907f9addf
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

end CommunityReplay_64b5f1b7_2bc9_48de_8b63_4b6907f9addf

noncomputable def minsky_papert_symmetrization := @CommunityReplay_64b5f1b7_2bc9_48de_8b63_4b6907f9addf.solution

namespace CommunityReplay_36b703fc_a778_4020_b894_e46646ac2827
open Polynomial Polynomial.Chebyshev

namespace ChebPythag

/-- The evaluation of the Pythagorean polynomial at `cos θ` for `θ ∈ (0,π)` is zero. -/
lemma eval_cos_eq_zero (d : ℕ) (θ : ℝ) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi) :
    (1 - (Real.cos θ)^2) * ((derivative (T ℝ (d : ℤ))).eval (Real.cos θ))^2
      + (d : ℝ)^2 * ((T ℝ (d : ℤ)).eval (Real.cos θ))^2 = (d : ℝ)^2 := by
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ1 hθ2
  have hsin_ne : Real.sin θ ≠ 0 := ne_of_gt hsin_pos
  -- T_d(cos θ) = cos(d θ)
  have hT : (T ℝ (d : ℤ)).eval (Real.cos θ) = Real.cos ((d : ℤ) * θ) := T_real_cos θ d
  -- T'_d(cos θ) = d * U_{d-1}(cos θ), and U_{d-1}(cos θ) sin θ = sin(d θ).
  have hU := U_real_cos θ ((d : ℤ) - 1)
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, sub_add_cancel] at hU
  -- hU : (U ℝ (d-1)).eval (cos θ) * sin θ = sin (↑d * θ)
  have hderiv : derivative (T ℝ (d : ℤ)) = ((d : ℤ) : ℝ[X]) * U ℝ ((d : ℤ) - 1) :=
    T_derivative_eq_U (d : ℤ)
  -- Evaluate the derivative.
  have hderiv_eval : (derivative (T ℝ (d : ℤ))).eval (Real.cos θ)
      = (d : ℝ) * (U ℝ ((d : ℤ) - 1)).eval (Real.cos θ) := by
    rw [hderiv, Polynomial.eval_mul]
    congr 1
    simp
  -- U eval: (U ℝ (d-1)).eval (cos θ) = sin(d θ) / sin θ
  have hUeval : (U ℝ ((d : ℤ) - 1)).eval (Real.cos θ) = Real.sin ((d : ℤ) * θ) / Real.sin θ := by
    rw [eq_div_iff hsin_ne]
    push_cast at hU ⊢
    linarith [hU]
  -- 1 - cos²θ = sin²θ
  have h1c : 1 - (Real.cos θ)^2 = (Real.sin θ)^2 := by
    have := Real.sin_sq_add_cos_sq θ
    linarith
  -- Cast ((d : ℤ) : ℝ) = (d : ℝ)
  have hdc : (((d : ℤ) : ℝ)) = (d : ℝ) := by simp
  rw [h1c, hderiv_eval, hUeval, hT]
  -- Compute: sin²θ · (d · sin(dθ)/sinθ)² + d² cos²(dθ) = d² sin²(dθ) + d² cos²(dθ) = d²
  have hsq := Real.sin_sq_add_cos_sq ((d : ℤ) * θ)
  field_simp
  nlinarith [hsq, sq_nonneg (Real.sin θ), sq_nonneg (Real.sin ((d:ℤ)*θ)), sq_nonneg (Real.cos ((d:ℤ)*θ))]

end ChebPythag

open ChebPythag

theorem solution (d : ℕ) :
    ∀ c : ℝ, (1 - c^2) * ((Polynomial.derivative (Polynomial.Chebyshev.T ℝ (d : ℤ))).eval c)^2 + (d : ℝ)^2 * ((Polynomial.Chebyshev.T ℝ (d : ℤ)).eval c)^2 = (d : ℝ)^2 := by
  intro c
  -- The Pythagorean polynomial vanishes identically.
  set P : Polynomial ℝ := (1 - X^2) * (derivative (T ℝ (d : ℤ)))^2
    + C ((d : ℝ)^2) * (T ℝ (d : ℤ))^2 - C ((d : ℝ)^2) with hP_def
  -- P.eval x = 0 for all x, because P has infinitely many roots.
  have hP0 : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hIcc_inf : (Set.Ioo (-1 : ℝ) 1).Infinite := Set.infinite_coe_iff.mp (Set.Ioo.infinite (by norm_num))
    apply hIcc_inf.mono
    intro x hx
    -- x ∈ (-1, 1). Set θ := arccos x.
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot]
    have hx1 : -1 < x := hx.1
    have hx2 : x < 1 := hx.2
    have hx1' : -1 ≤ x := le_of_lt hx1
    have hx2' : x ≤ 1 := le_of_lt hx2
    set θ := Real.arccos x with hθ_def
    have hθpos : 0 < θ := Real.arccos_pos.mpr hx2
    have hθlt : θ < Real.pi := Real.arccos_lt_pi.mpr hx1
    have hcos : Real.cos θ = x := Real.cos_arccos hx1' hx2'
    have := eval_cos_eq_zero d θ hθpos hθlt
    rw [hcos] at this
    rw [hP_def]
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C]
    linarith
  -- Now use P = 0 to get the identity at c.
  have := congrArg (Polynomial.eval c) hP0
  rw [hP_def] at this
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_zero] at this
  linarith

end CommunityReplay_36b703fc_a778_4020_b894_e46646ac2827

noncomputable def cheb_pythag := @CommunityReplay_36b703fc_a778_4020_b894_e46646ac2827.solution

namespace CommunityReplay_c4a8e483_d818_4e7b_8a11_bc4a1c1dcf05
open Polynomial Polynomial.Chebyshev Real

namespace ChebZerosProps

/-- `cos((2j+1)π/2) = 0` : argument is an odd multiple of `π/2`. -/
lemma cos_odd_pi_div_two (j : ℕ) : Real.cos ((2 * (j : ℝ) + 1) * Real.pi / 2) = 0 := by
  have h : (2 * (j : ℝ) + 1) * Real.pi / 2 = (j : ℝ) * Real.pi + Real.pi / 2 := by ring
  have hsin : Real.sin ((j : ℝ) * Real.pi) = 0 := by
    rw [show ((j : ℝ) * Real.pi) = (j : ℤ) * Real.pi by push_cast; ring]
    exact Real.sin_int_mul_pi j
  rw [h, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, hsin]
  ring

/-- `sin((2j+1)π/2) = (-1)^j`. -/
lemma sin_odd_pi_div_two (j : ℕ) : Real.sin ((2 * (j : ℝ) + 1) * Real.pi / 2) = (-1 : ℝ)^j := by
  have h : (2 * (j : ℝ) + 1) * Real.pi / 2 = (j : ℝ) * Real.pi + Real.pi / 2 := by ring
  have hcos : Real.cos ((j : ℝ) * Real.pi) = (-1 : ℝ)^j := by
    rw [show ((j : ℝ) * Real.pi) = (j : ℤ) * Real.pi by push_cast; ring]
    rw [Real.cos_int_mul_pi j]
    norm_cast
  rw [h, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two, hcos]
  ring

end ChebZerosProps

open ChebZerosProps

theorem solution (d : ℕ) (hd : 1 ≤ d) (j : ℕ) (hj : j < d) :
    let θj := (2 * (j : ℝ) + 1) * Real.pi / (2 * d);
    (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (Real.cos θj) = 0 ∧
    0 < (-1:ℝ)^j * (Polynomial.derivative (Polynomial.Chebyshev.T ℝ (d : ℤ))).eval (Real.cos θj) ∧
    -1 < Real.cos θj ∧ Real.cos θj < 1 := by
  have hdr : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdr_pos : (0 : ℝ) < (d : ℝ) := by linarith
  have hjr : (j : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hj
  have hpi := Real.pi_pos
  set θj : ℝ := (2 * (j : ℝ) + 1) * Real.pi / (2 * d) with hθ_def
  -- θj ∈ (0, π).
  have hθj_pos : (0 : ℝ) < θj := by rw [hθ_def]; positivity
  have hθj_lt_pi : θj < Real.pi := by
    rw [hθ_def, div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hsinθ_pos : (0 : ℝ) < Real.sin θj := Real.sin_pos_of_pos_of_lt_pi hθj_pos hθj_lt_pi
  -- d · θj = (2j+1)π/2.
  have hdθ : (d : ℝ) * θj = (2 * (j : ℝ) + 1) * Real.pi / 2 := by
    rw [hθ_def]; field_simp
  -- Part 1: T_d(cos θj) = cos(d θj) = 0.
  have hT0 : (T ℝ (d : ℤ)).eval (Real.cos θj) = 0 := by
    rw [T_real_cos θj (d : ℤ)]
    have : ((d : ℤ) : ℝ) * θj = (2 * (j : ℝ) + 1) * Real.pi / 2 := by push_cast; linarith [hdθ]
    rw [this, cos_odd_pi_div_two]
  -- Part 2: U_{d-1}(cos θj) sin θj = sin(d θj) = (-1)^j.
  have hUsin := U_real_cos θj ((d : ℤ) - 1)
  have hsub : (((d : ℤ) - 1 : ℤ) : ℝ) + 1 = ((d : ℤ) : ℝ) := by push_cast; ring
  rw [hsub] at hUsin
  have hUsin' : (U ℝ ((d : ℤ) - 1)).eval (Real.cos θj) * Real.sin θj = (-1 : ℝ)^j := by
    rw [hUsin]
    have : ((d : ℤ) : ℝ) * θj = (2 * (j : ℝ) + 1) * Real.pi / 2 := by push_cast; linarith [hdθ]
    rw [this, sin_odd_pi_div_two]
  -- T'_d = d U_{d-1}, so T'_d(cos θj) = d U_{d-1}(cos θj) = d(-1)^j / sin θj.
  have hderiv : derivative (T ℝ (d : ℤ)) = ((d : ℤ) : ℝ[X]) * U ℝ ((d : ℤ) - 1) :=
    T_derivative_eq_U (d : ℤ)
  have hT'eval : (derivative (T ℝ (d : ℤ))).eval (Real.cos θj)
      = (d : ℝ) * ((U ℝ ((d : ℤ) - 1)).eval (Real.cos θj)) := by
    rw [hderiv]; simp [Polynomial.eval_mul]
  have halt : (0 : ℝ) < (-1:ℝ)^j * (derivative (T ℝ (d : ℤ))).eval (Real.cos θj) := by
    rw [hT'eval]
    have hU_val : (U ℝ ((d : ℤ) - 1)).eval (Real.cos θj) = (-1:ℝ)^j / Real.sin θj := by
      rw [eq_div_iff (ne_of_gt hsinθ_pos)]; exact hUsin'
    rw [hU_val]
    have hj2 : ((-1:ℝ)^j)^2 = 1 := by
      rw [← pow_mul, pow_mul']
      simp
    have : (-1:ℝ)^j * ((d : ℝ) * ((-1:ℝ)^j / Real.sin θj)) = (d : ℝ) / Real.sin θj := by
      field_simp
      nlinarith [hj2]
    rw [this]
    positivity
  -- Part 3: cos θj ∈ (-1, 1).
  have hcos_lt : Real.cos θj < 1 := by
    calc Real.cos θj < Real.cos 0 := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθj_lt_pi.le hθj_pos
      _ = 1 := Real.cos_zero
  have hcos_gt : -1 < Real.cos θj := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi hθj_pos.le le_rfl hθj_lt_pi
    rw [Real.cos_pi] at this
    linarith
  exact ⟨hT0, halt, hcos_gt, hcos_lt⟩

end CommunityReplay_c4a8e483_d818_4e7b_8a11_bc4a1c1dcf05

noncomputable def cheb_zeros_props := @CommunityReplay_c4a8e483_d818_4e7b_8a11_bc4a1c1dcf05.solution

namespace CommunityReplay_110621c0_b7a8_42b6_a5ca_25e2dd91bb0d
open Polynomial Set

namespace PolyAltSign

/-- IVT: if a polynomial changes sign on `[a,b]`, it has a root in `(a,b)`. -/
lemma exists_root_of_sign_change (R : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (h : R.eval a * R.eval b < 0) : ∃ r ∈ Set.Ioo a b, R.IsRoot r := by
  have hcont : ContinuousOn (fun x => R.eval x) (Set.Icc a b) := (Polynomial.continuous R).continuousOn
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · -- R(a) > 0 > R(b): use intermediate_value_Ioo'.
    have h0 : (0 : ℝ) ∈ Set.Ioo (R.eval b) (R.eval a) := ⟨hb, ha⟩
    have := intermediate_value_Ioo' hab.le hcont h0
    obtain ⟨r, hr1, hr2⟩ := this
    exact ⟨r, hr1, hr2⟩
  · -- R(a) < 0 < R(b): use intermediate_value_Ioo.
    have h0 : (0 : ℝ) ∈ Set.Ioo (R.eval a) (R.eval b) := ⟨ha, hb⟩
    have := intermediate_value_Ioo hab.le hcont h0
    obtain ⟨r, hr1, hr2⟩ := this
    exact ⟨r, hr1, hr2⟩

/-- The core root-counting: an alternating polynomial with extra outer root. -/
lemma no_outer_root (R : Polynomial ℝ) (n : ℕ) (t : ℕ → ℝ)
    (ht : ∀ i j : ℕ, i < j → j ≤ n → t j < t i)
    (hdeg : R.natDegree ≤ n)
    (halt : ∀ i : ℕ, i ≤ n → 0 < (-1:ℝ)^i * R.eval (t i))
    (c : ℝ) (hc : t 0 ≤ c ∨ c ≤ t n) (hroot : R.IsRoot c) : False := by
  -- R ≠ 0 since R(t 0) > 0.
  have hR0 : R ≠ 0 := by
    intro hR
    have := halt 0 (Nat.zero_le n)
    simp [hR] at this
  -- For each i < n, R changes sign on (t(i+1), t i), giving a root r_i.
  have hroots : ∀ i : ℕ, i < n → ∃ r ∈ Set.Ioo (t (i + 1)) (t i), R.IsRoot r := by
    intro i hi
    apply exists_root_of_sign_change R (ht i (i+1) (Nat.lt_succ_self i) hi)
    -- R(t(i+1)) · R(t i) < 0.
    have h1 := halt (i + 1) hi
    have h2 := halt i (Nat.le_of_lt hi)
    have heq : (-1:ℝ)^(i+1) = -(-1:ℝ)^i := by rw [pow_succ]; ring
    rw [heq] at h1
    nlinarith [sq_nonneg ((-1:ℝ)^i)]
  -- Choice function for the roots.
  classical
  let r : ℕ → ℝ := fun i => if hi : i < n then (hroots i hi).choose else c
  have hr_mem : ∀ i, i < n → r i ∈ Set.Ioo (t (i + 1)) (t i) := by
    intro i hi
    simp only [r, dif_pos hi]
    exact (hroots i hi).choose_spec.1
  have hr_root : ∀ i, i < n → R.IsRoot (r i) := by
    intro i hi
    simp only [r, dif_pos hi]
    exact (hroots i hi).choose_spec.2
  -- r i ∈ (t n, t 0) for all i < n.
  have hr_inner : ∀ i, i < n → t n < r i ∧ r i < t 0 := by
    intro i hi
    obtain ⟨h1, h2⟩ := hr_mem i hi
    constructor
    · rcases Nat.lt_or_ge (i + 1) n with h | h
      · exact lt_trans (ht (i+1) n h le_rfl) h1
      · have : i + 1 = n := le_antisymm hi h
        rw [this] at h1; exact h1
    · rcases Nat.eq_zero_or_pos i with h | h
      · subst h; exact h2
      · exact lt_trans h2 (ht 0 i h (Nat.le_of_lt hi))
  -- The r i are pairwise distinct.
  have hr_inj : ∀ i j, i < n → j < n → i < j → r i ≠ r j := by
    intro i j hi hj hij
    obtain ⟨hi1, hi2⟩ := hr_mem i hi
    obtain ⟨hj1, hj2⟩ := hr_mem j hj
    have htij : t j ≤ t (i + 1) := by
      rcases Nat.lt_or_ge (i + 1) j with h | h
      · exact (ht (i+1) j h (Nat.le_of_lt hj)).le
      · have : i + 1 = j := le_antisymm hij h
        rw [this]
    intro heq
    linarith [heq ▸ hi1]
  -- c ≠ r i for all i < n (c is outside (t n, t 0)).
  have hc_ne : ∀ i, i < n → c ≠ r i := by
    intro i hi heq
    obtain ⟨hri1, hri2⟩ := hr_inner i hi
    rcases hc with hc1 | hc2
    · linarith [heq ▸ hc1]
    · linarith [heq ▸ hc2]
  -- Build the finset S.
  let S : Finset ℝ := (Finset.range n).image r ∪ {c}
  have hS_sub : S ⊆ R.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hR0]
    simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_singleton] at hx
    rcases hx with ⟨i, hi, heq⟩ | heq
    · rw [← heq]; exact hr_root i hi
    · rw [heq]; exact hroot
  have hr_injOn : Set.InjOn r ↑(Finset.range n) := by
    intro i hi j hj heq
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_ge i j with h | h
    · exact hr_inj i j hi hj h heq
    · exact hr_inj j i hj hi (lt_of_le_of_ne h (Ne.symm hne)) heq.symm
  have hdisj : Disjoint ((Finset.range n).image r) {c} := by
    rw [Finset.disjoint_singleton_right, Finset.mem_image]
    rintro ⟨i, hi, heq⟩
    exact hc_ne i (Finset.mem_range.mp hi) heq.symm
  have hS_card : S.card = n + 1 := by
    show ((Finset.range n).image r ∪ {c}).card = n + 1
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton,
        Finset.card_image_of_injOn hr_injOn, Finset.card_range]
  have := calc n + 1 = S.card := hS_card.symm
    _ ≤ R.roots.toFinset.card := Finset.card_le_card hS_sub
    _ ≤ Multiset.card R.roots := Multiset.toFinset_card_le _
    _ ≤ R.natDegree := Polynomial.card_roots' R
    _ ≤ n := hdeg
  omega

end PolyAltSign

open PolyAltSign

theorem solution : ∀ (Tp p : Polynomial ℝ) (n : ℕ) (t : ℕ → ℝ) (ht : ∀ i j : ℕ, i < j → j ≤ n → t j < t i) (hTdeg : Tp.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (halt : ∀ i : ℕ, i ≤ n → 0 < (-1:ℝ)^i * Tp.eval (t i)) (hcmp : ∀ i : ℕ, i ≤ n → |p.eval (t i)| ≤ |Tp.eval (t i)|), ∀ c : ℝ, (t 0 ≤ c ∨ c ≤ t n) → |p.eval c| ≤ |Tp.eval c| := by
  intro Tp p n t ht hTdeg hpdeg halt hcmp c hc
  by_contra hcontra
  push_neg at hcontra
  -- Case 1: Tp(c) = 0. Then Tp has an outer root, contradiction.
  rcases eq_or_ne (Tp.eval c) 0 with hTc | hTc
  · exact no_outer_root Tp n t ht hTdeg halt c hc hTc
  -- Case 2: Tp(c) ≠ 0. Let μ := Tp(c)/p(c).
  have hpc : p.eval c ≠ 0 := by
    intro hpc
    rw [hpc, abs_zero] at hcontra
    exact absurd hcontra (not_lt.mpr (abs_nonneg _))
  have hmu : |Tp.eval c / p.eval c| < 1 := by
    rw [abs_div, div_lt_one (abs_pos.mpr hpc)]
    exact hcontra
  set μ := Tp.eval c / p.eval c with hμ_def
  set R := Tp - C μ * p with hR_def
  have hR_eval : ∀ x : ℝ, R.eval x = Tp.eval x - μ * p.eval x := by
    intro x; rw [hR_def]; simp [Polynomial.eval_sub, Polynomial.eval_mul]
  -- R(c) = 0.
  have hRc : R.IsRoot c := by
    rw [Polynomial.IsRoot, hR_eval, hμ_def]
    field_simp
    ring
  -- deg R ≤ n.
  have hRdeg : R.natDegree ≤ n := by
    rw [hR_def]
    calc (Tp - C μ * p).natDegree ≤ max Tp.natDegree (C μ * p).natDegree := Polynomial.natDegree_sub_le _ _
      _ ≤ max Tp.natDegree p.natDegree := by
          apply max_le_max le_rfl
          exact Polynomial.natDegree_C_mul_le _ _
      _ ≤ n := max_le hTdeg hpdeg
  -- R alternates at t i.
  have hRalt : ∀ i : ℕ, i ≤ n → 0 < (-1:ℝ)^i * R.eval (t i) := by
    intro i hi
    rw [hR_eval]
    have h1 := halt i hi
    have h2 := hcmp i hi
    have h3 : |μ * p.eval (t i)| ≤ |μ| * |Tp.eval (t i)| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg μ)
    have hTi_ne : Tp.eval (t i) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1
      exact absurd h1 (lt_irrefl 0)
    have hTi_pos : 0 < |Tp.eval (t i)| := abs_pos.mpr hTi_ne
    -- (-1)^i Tp(t i) = |Tp(t i)|
    have hsign : (-1:ℝ)^i * Tp.eval (t i) = |Tp.eval (t i)| := by
      have hab : |(-1:ℝ)^i * Tp.eval (t i)| = |Tp.eval (t i)| := by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      rw [← hab, abs_of_pos h1]
    calc (0:ℝ) < (1 - |μ|) * |Tp.eval (t i)| := by
          apply mul_pos _ hTi_pos; linarith [hmu]
      _ = |Tp.eval (t i)| - |μ| * |Tp.eval (t i)| := by ring
      _ ≤ (-1:ℝ)^i * Tp.eval (t i) - |μ * p.eval (t i)| := by
          rw [hsign]; linarith [h3]
      _ ≤ (-1:ℝ)^i * Tp.eval (t i) - (-1:ℝ)^i * (μ * p.eval (t i)) := by
          have := neg_abs_le ((-1:ℝ)^i * (μ * p.eval (t i)))
          have habs : |(-1:ℝ)^i * (μ * p.eval (t i))| = |μ * p.eval (t i)| := by
            rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
          linarith [le_abs_self ((-1:ℝ)^i * (μ * p.eval (t i))), habs]
      _ = (-1:ℝ)^i * (Tp.eval (t i) - μ * p.eval (t i)) := by ring
  -- Apply no_outer_root.
  exact no_outer_root R n t ht hRdeg hRalt c hc hRc

end CommunityReplay_110621c0_b7a8_42b6_a5ca_25e2dd91bb0d

noncomputable def poly_alt_sign_compare := @CommunityReplay_110621c0_b7a8_42b6_a5ca_25e2dd91bb0d.solution

namespace CommunityReplay_5c483b4b_6789_4c19_b8d1_b21257138b3c
open Polynomial Polynomial.Chebyshev Real

theorem solution (p : Polynomial ℝ) {d : ℕ} (hd1 : 1 ≤ d) (hd : p.natDegree < d)
    (h : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (1 - x^2) * (p.eval x)^2 ≤ (d : ℝ)^2) :
    ∀ c : ℝ, -1 ≤ c → c ≤ 1 → Real.cos (Real.pi / (2 * (d : ℝ))) ≤ |c| →
      |p.eval c| ≤ |(Polynomial.derivative (Polynomial.Chebyshev.T ℝ (d : ℤ))).eval c| := by
  intro c hc1 hc2 hcos
  have hdr : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hdr_pos : (0 : ℝ) < (d : ℝ) := by linarith
  have hpi := Real.pi_pos
  -- Chebyshev zeros: t j := cos((2j+1)π/(2d)) for j = 0..d-1.
  set t : ℕ → ℝ := fun j => Real.cos ((2 * (j : ℝ) + 1) * Real.pi / (2 * d)) with ht_def
  set Td' : Polynomial ℝ := derivative (T ℝ (d : ℤ)) with hTd'_def
  -- Step 0: argument range.
  have harg_bounds : ∀ j : ℕ, j ≤ d - 1 → (0 : ℝ) < (2 * (j : ℝ) + 1) * Real.pi / (2 * d)
      ∧ (2 * (j : ℝ) + 1) * Real.pi / (2 * d) < Real.pi := by
    intro j hj
    have hjd : j < d := by omega
    have hjr : (j : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hjd
    refine ⟨by positivity, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  -- Step 1: strict antimonotonicity of t on {0,...,d-1}.
  have ht_anti : ∀ i j : ℕ, i < j → j ≤ d - 1 → t j < t i := by
    intro i j hij hj
    have hi : i ≤ d - 1 := by omega
    have ⟨hib1, hib2⟩ := harg_bounds i hi
    have ⟨hjb1, hjb2⟩ := harg_bounds j hj
    apply Real.cos_lt_cos_of_nonneg_of_le_pi hib1.le hjb2.le
    have hir : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    rw [div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < 2 * (d : ℝ))]
    nlinarith [Real.pi_pos]
  -- Step 2: zeros and alternation properties.
  have hzeros : ∀ j : ℕ, j ≤ d - 1 →
      (T ℝ (d : ℤ)).eval (t j) = 0 ∧ 0 < (-1:ℝ)^j * Td'.eval (t j) ∧ -1 < t j ∧ t j < 1 := by
    intro j hj
    have hjd : j < d := by omega
    exact cheb_zeros_props d hd1 j hjd
  -- Step 3: natDegree bounds.
  have hTd'deg : Td'.natDegree ≤ d - 1 := by
    rw [hTd'_def]
    calc (derivative (T ℝ (d:ℤ))).natDegree ≤ (T ℝ (d:ℤ)).natDegree - 1 :=
          Polynomial.natDegree_derivative_le _
      _ = (d : ℤ).natAbs - 1 := by rw [natDegree_T]
      _ = d - 1 := by rw [Int.natAbs_natCast]
  have hpdeg : p.natDegree ≤ d - 1 := by omega
  -- Step 4: |p(t j)| ≤ |T'_d(t j)| from Bernstein hyp + Pythagoras.
  have hcmp : ∀ j : ℕ, j ≤ d - 1 → |p.eval (t j)| ≤ |Td'.eval (t j)| := by
    intro j hj
    obtain ⟨hTj0, hTd'j, htj1, htj2⟩ := hzeros j hj
    have h1tj : (0 : ℝ) < 1 - (t j)^2 := by nlinarith
    -- cheb_pythag at t j: (1-(t j)²)T'_d(t j)² + d²·T_d(t j)² = d², and T_d(t j)=0.
    have hpythag := cheb_pythag d (t j)
    rw [hTj0] at hpythag
    -- Bernstein hyp at t j: (1-(t j)²)p(t j)² ≤ d².
    have hbern := h (t j) htj1.le htj2.le
    -- So (p.eval (t j))² ≤ (T'_d.eval (t j))².
    have hsq : (p.eval (t j))^2 ≤ (Td'.eval (t j))^2 := by nlinarith
    have h1 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at h1
  -- Step 5: apply poly_alt_sign_compare.
  have hcmp_result := poly_alt_sign_compare Td' p (d - 1) t ht_anti hTd'deg hpdeg
    (fun j hj => (hzeros j hj).2.1) hcmp c
  -- Step 6: translate `cos(π/(2d)) ≤ |c|` into `t 0 ≤ c ∨ c ≤ t (d-1)`.
  have ht0 : t 0 = Real.cos (Real.pi / (2 * (d : ℝ))) := by
    rw [ht_def]
    simp only [Nat.cast_zero, mul_zero, zero_add, one_mul]
  have htd1 : t (d - 1) = -Real.cos (Real.pi / (2 * (d : ℝ))) := by
    rw [ht_def]
    have hd1r : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      have := Nat.cast_sub hd1 (R := ℝ)
      push_cast at this ⊢
      linarith
    simp only
    rw [hd1r]
    have harg : (2 * ((d : ℝ) - 1) + 1) * Real.pi / (2 * d) = Real.pi - Real.pi / (2 * d) := by
      field_simp
      ring
    rw [harg, Real.cos_pi_sub]
  have hdisj : t 0 ≤ c ∨ c ≤ t (d - 1) := by
    rw [ht0, htd1]
    rcases le_abs.mp hcos with hle | hle
    · left; exact hle
    · right; linarith
  exact hcmp_result hdisj

end CommunityReplay_5c483b4b_6789_4c19_b8d1_b21257138b3c

noncomputable def cheb_alt_compare := @CommunityReplay_5c483b4b_6789_4c19_b8d1_b21257138b3c.solution

namespace CommunityReplay_1faabb49_2fe5_4b64_b1b2_ce97eaaa30bb
open Real

theorem solution (d : ℕ) (hd : 1 ≤ d) :
    Real.cos (Real.pi / (2 * (d : ℝ)))^2 ≤ 1 - 1/(d : ℝ)^2 := by
  have hdr : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdr_pos : (0 : ℝ) < (d : ℝ) := by linarith
  have hpi := Real.pi_pos
  -- π/(2d) ∈ [0, π/2]
  have h0 : (0 : ℝ) ≤ Real.pi / (2 * d) := by positivity
  have h2 : Real.pi / (2 * (d : ℝ)) ≤ Real.pi / 2 := by
    apply div_le_div_of_nonneg_left (le_of_lt hpi) (by norm_num) ?_
    linarith
  -- Jordan: 2/π · π/(2d) ≤ sin(π/(2d)).
  have hjordan := Real.mul_le_sin h0 h2
  -- Simplify LHS: 2/π · π/(2d) = 1/d.
  have hlhs : 2 / Real.pi * (Real.pi / (2 * (d : ℝ))) = 1 / (d : ℝ) := by
    field_simp
  rw [hlhs] at hjordan
  -- sin(π/(2d)) ≥ 1/d ≥ 0, so sin² ≥ 1/d².
  have hsin_sq : (1 / (d : ℝ))^2 ≤ (Real.sin (Real.pi / (2 * d)))^2 := by
    apply sq_le_sq'
    · linarith [hjordan, (by positivity : (0:ℝ) ≤ 1/(d:ℝ))]
    · exact hjordan
  -- cos² = 1 - sin² ≤ 1 - 1/d².
  have hpythag := Real.sin_sq_add_cos_sq (Real.pi / (2 * (d : ℝ)))
  have h1d : (1 / (d : ℝ))^2 = 1 / (d : ℝ)^2 := by field_simp
  linarith [hsin_sq, hpythag, h1d]

end CommunityReplay_1faabb49_2fe5_4b64_b1b2_ce97eaaa30bb

noncomputable def jordan_cos_sq_le := @CommunityReplay_1faabb49_2fe5_4b64_b1b2_ce97eaaa30bb.solution

namespace CommunityReplay_f06fdc22_68d3_4d1a_a8fb_8cbb7681a2a3
open Polynomial Polynomial.Chebyshev Real

theorem solution (p : Polynomial ℝ) {d : ℕ} (hd1 : 1 ≤ d) (hd : p.natDegree < d)
    (h : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (1 - x^2) * (p.eval x)^2 ≤ (d : ℝ)^2) :
    ∀ c : ℝ, -1 ≤ c → c ≤ 1 → (d : ℝ)^2 * (1 - c^2) ≤ 1 →
      |p.eval c| ≤ |(Polynomial.derivative (Polynomial.Chebyshev.T ℝ (d : ℤ))).eval c| := by
  intro c hc1 hc2 hcase
  have hdr_pos : (0 : ℝ) < (d : ℝ) := by
    have : (1 : ℕ) ≤ d := hd1
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  -- d² > 0, so from d²(1-c²) ≤ 1, get 1-c² ≤ 1/d², i.e., c² ≥ 1-1/d².
  have hd2_pos : (0 : ℝ) < (d : ℝ)^2 := by positivity
  have hc2ge : (1 : ℝ) - 1/(d : ℝ)^2 ≤ c^2 := by
    have h1 : 1 - c^2 ≤ 1/(d:ℝ)^2 := by
      rw [le_div_iff₀ hd2_pos]
      nlinarith [hcase]
    linarith
  -- Jordan: cos(π/(2d))² ≤ 1 - 1/d² ≤ c².
  have hjordan := jordan_cos_sq_le d hd1
  have hcsq : Real.cos (Real.pi / (2 * d))^2 ≤ c^2 := le_trans hjordan hc2ge
  -- So cos(π/(2d)) ≤ |cos(π/(2d))| ≤ |c|.
  have hcabs : Real.cos (Real.pi / (2 * d)) ≤ |c| := by
    calc Real.cos (Real.pi / (2 * d)) ≤ |Real.cos (Real.pi / (2 * d))| := le_abs_self _
      _ ≤ |c| := by
          have h1 := Real.sqrt_le_sqrt hcsq
          rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at h1
  exact cheb_alt_compare p hd1 hd h c hc1 hc2 hcabs

end CommunityReplay_f06fdc22_68d3_4d1a_a8fb_8cbb7681a2a3

noncomputable def cheb_compare_outer := @CommunityReplay_f06fdc22_68d3_4d1a_a8fb_8cbb7681a2a3.solution

namespace CommunityReplay_08059237_c837_48c7_9d87_27e2348ee8bc
open Polynomial Polynomial.Chebyshev

namespace ChebDeriv

/-- `|T_n(c)| ≤ 1` for `c ∈ [-1,1]`. -/
lemma T_abs_le_one (n : ℤ) (c : ℝ) (hc1 : -1 ≤ c) (hc2 : c ≤ 1) :
    |(T ℝ n).eval c| ≤ 1 := by
  have hcos : Real.cos (Real.arccos c) = c := Real.cos_arccos hc1 hc2
  have := T_real_cos (Real.arccos c) n
  rw [hcos] at this
  rw [this]
  exact Real.abs_cos_le_one _

/-- `|U_n(c)| ≤ n + 1` for `c ∈ [-1,1]`, `n : ℕ`. -/
lemma U_abs_le (n : ℕ) (c : ℝ) (hc1 : -1 ≤ c) (hc2 : c ≤ 1) :
    |(U ℝ (n : ℤ)).eval c| ≤ (n : ℝ) + 1 := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, Int.cast_zero, U_zero, Polynomial.eval_one, abs_one, zero_add, le_refl]
  | succ m ih =>
    -- U_eq_X_mul_U_add_T R m : U R (m+1) = X * U R m + T R (m+1)
    have hrec := U_eq_X_mul_U_add_T ℝ (m : ℤ)
    have hcabs : |c| ≤ 1 := abs_le.mpr ⟨hc1, hc2⟩
    have hcastm1 : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    rw [hcastm1]
    calc |(U ℝ ((m : ℤ) + 1)).eval c|
        = |c * (U ℝ (m : ℤ)).eval c + (T ℝ ((m : ℤ) + 1)).eval c| := by
          rw [hrec]; simp [Polynomial.eval_add, Polynomial.eval_mul]
      _ ≤ |c * (U ℝ (m : ℤ)).eval c| + |(T ℝ ((m : ℤ) + 1)).eval c| := abs_add_le _ _
      _ = |c| * |(U ℝ (m : ℤ)).eval c| + |(T ℝ ((m : ℤ) + 1)).eval c| := by rw [abs_mul]
      _ ≤ 1 * ((m : ℝ) + 1) + 1 := by
          apply add_le_add
          · apply mul_le_mul hcabs ih (abs_nonneg _) (by norm_num)
          · exact T_abs_le_one _ c hc1 hc2
      _ = (m : ℝ) + 1 + 1 := by ring
      _ = ((m + 1 : ℕ) : ℝ) + 1 := by push_cast; ring

end ChebDeriv

open ChebDeriv

theorem solution (d : ℕ) :
    ∀ c : ℝ, -1 ≤ c → c ≤ 1 → |(Polynomial.derivative (Polynomial.Chebyshev.T ℝ (d : ℤ))).eval c| ≤ (d : ℝ)^2 := by
  intro c hc1 hc2
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- d = 0: T_0 = 1, derivative = 0.
    subst hd0
    simp only [Nat.cast_zero, Int.cast_zero, T_zero, Polynomial.derivative_one,
      Polynomial.eval_zero, abs_zero]
    norm_num
  · -- d ≥ 1: T'_d = d * U_{d-1}, |U_{d-1}| ≤ d.
    have hderiv := T_derivative_eq_U (R := ℝ) (d : ℤ)
    have hd1 : (d : ℤ) - 1 = ((d - 1 : ℕ) : ℤ) := by omega
    rw [hd1] at hderiv
    have hUbd := U_abs_le (d - 1) c hc1 hc2
    have hd1r : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
      have : (1 : ℕ) ≤ d := hdpos
      push_cast [Nat.cast_sub this]
      ring
    rw [hd1r] at hUbd
    calc |(derivative (T ℝ (d : ℤ))).eval c|
        = |(d : ℝ) * (U ℝ ((d - 1 : ℕ) : ℤ)).eval c| := by
          rw [hderiv]
          simp [Polynomial.eval_mul]
      _ = (d : ℝ) * |(U ℝ ((d - 1 : ℕ) : ℤ)).eval c| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (d:ℝ))]
      _ ≤ (d : ℝ) * (d : ℝ) := by
          apply mul_le_mul_of_nonneg_left hUbd (by positivity)
      _ = (d : ℝ)^2 := by ring

end CommunityReplay_08059237_c837_48c7_9d87_27e2348ee8bc

noncomputable def cheb_deriv_abs_le := @CommunityReplay_08059237_c837_48c7_9d87_27e2348ee8bc.solution

namespace CommunityReplay_843c9344_d8e3_4942_b43f_89bfe0ccefc9
open Polynomial

namespace CosShiftDecompose

/-- Auxiliary: `cos_shift_decompose` with the degree bound `≤ n` in the hypothesis,
so we can do induction on `n`. Also tracks `E(1) = Q(cos φ)`. -/
theorem aux (n : ℕ) : ∀ (Q : Polynomial ℝ) (φ : ℝ), Q.natDegree ≤ n →
    ∃ E P : Polynomial ℝ, E.natDegree ≤ Q.natDegree ∧
      (P.natDegree + 1 ≤ Q.natDegree ∨ P = 0) ∧
      (∀ θ : ℝ, Q.eval (Real.cos (φ + θ)) = E.eval (Real.cos θ) + P.eval (Real.cos θ) * Real.sin θ) ∧
      E.eval 1 = Q.eval (Real.cos φ) ∧
      P.eval 1 = -Real.sin φ * Q.derivative.eval (Real.cos φ) := by
  induction n with
  | zero =>
    -- Q is constant.
    intro Q φ hQdeg
    have hQ0 : Q.natDegree = 0 := Nat.le_zero.mp hQdeg
    obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hQ0
    refine ⟨C a, 0, ?_, Or.inr rfl, ?_, ?_, ?_⟩
    · rw [Polynomial.natDegree_C]; omega
    · intro θ; rw [← ha]; simp
    · rw [← ha]; simp
    · rw [← ha]; simp
  | succ m ih =>
    intro Q φ hQdeg
    rcases Nat.lt_or_ge m Q.natDegree with hgt | hle
    swap
    · exact ih Q φ hle
    -- Q.natDegree = m + 1.
    have hQeq : Q.natDegree = m + 1 := le_antisymm hQdeg hgt
    have hQ1pos : 1 ≤ Q.natDegree := by omega
    -- Decompose Q = X * Q.divX + C (Q.coeff 0).
    set a := Q.coeff 0 with ha_def
    set Q₁ := Q.divX with hQ1_def
    have hXmul : X * Q₁ + C a = Q := Polynomial.X_mul_divX_add Q
    -- Q₁ ≠ 0 and natDegree Q₁ = m.
    have hQ1ne : Q₁ ≠ 0 := by
      intro hQ10
      rw [hQ10, mul_zero, zero_add] at hXmul
      rw [← hXmul, Polynomial.natDegree_C] at hQeq
      omega
    have hQ1deg : Q₁.natDegree ≤ m := by
      have hX : (X * Q₁).natDegree = 1 + Q₁.natDegree := by
        rw [Polynomial.natDegree_mul (Polynomial.X_ne_zero) hQ1ne, Polynomial.natDegree_X]
      have hlt : (C a : ℝ[X]).natDegree < (X * Q₁).natDegree := by
        rw [Polynomial.natDegree_C, hX]; omega
      have heq : Q.natDegree = (X * Q₁).natDegree := by
        rw [← hXmul]
        exact Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt
      rw [heq, hX] at hQeq
      omega
    -- IH applied to Q₁.
    obtain ⟨E₁, P₁, hE₁deg, hP₁deg, hident₁, hE₁1, hP₁1⟩ := ih Q₁ φ hQ1deg
    -- Define E, P.
    set E : Polynomial ℝ := C a + C (Real.cos φ) * X * E₁ - C (Real.sin φ) * (1 - X^2) * P₁ with hE_def
    set P : Polynomial ℝ := C (Real.cos φ) * X * P₁ - C (Real.sin φ) * E₁ with hP_def
    refine ⟨E, P, ?_, ?_, ?_, ?_, ?_⟩
    · -- deg E ≤ deg Q.
      rw [hE_def]
      have h1 : (C a : Polynomial ℝ).natDegree ≤ Q.natDegree := by
        rw [Polynomial.natDegree_C]; omega
      have h2 : (C (Real.cos φ) * X * E₁).natDegree ≤ Q.natDegree := by
        calc (C (Real.cos φ) * X * E₁).natDegree ≤ (C (Real.cos φ) * X).natDegree + E₁.natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ 1 + E₁.natDegree := by
              apply Nat.add_le_add_right
              calc (C (Real.cos φ) * X).natDegree ≤ (C (Real.cos φ)).natDegree + (X : ℝ[X]).natDegree :=
                    Polynomial.natDegree_mul_le
                _ ≤ 0 + 1 := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
                _ = 1 := by ring
          _ ≤ 1 + Q₁.natDegree := by omega
          _ ≤ Q.natDegree := by omega
      have h3 : (C (Real.sin φ) * (1 - X^2) * P₁).natDegree ≤ Q.natDegree := by
        rcases hP₁deg with hP₁ | hP₁
        · calc (C (Real.sin φ) * (1 - X^2) * P₁).natDegree ≤ (C (Real.sin φ) * (1 - X^2)).natDegree + P₁.natDegree :=
                Polynomial.natDegree_mul_le
            _ ≤ 2 + P₁.natDegree := by
                apply Nat.add_le_add_right
                calc (C (Real.sin φ) * (1 - X^2)).natDegree ≤ (C (Real.sin φ)).natDegree + ((1:ℝ[X]) - X^2).natDegree :=
                      Polynomial.natDegree_mul_le
                  _ ≤ 0 + 2 := by
                      apply add_le_add
                      · rw [Polynomial.natDegree_C]
                      · calc ((1:ℝ[X]) - X^2).natDegree ≤ max (1:ℝ[X]).natDegree ((X:ℝ[X])^2).natDegree :=
                              Polynomial.natDegree_sub_le _ _
                          _ ≤ 2 := by rw [Polynomial.natDegree_one, Polynomial.natDegree_X_pow]; omega
                  _ = 2 := by ring
            _ ≤ 2 + (Q₁.natDegree - 1) := by omega
            _ ≤ Q.natDegree := by omega
        · rw [hP₁, mul_zero, Polynomial.natDegree_zero]; omega
      calc (C a + C (Real.cos φ) * X * E₁ - C (Real.sin φ) * (1 - X^2) * P₁).natDegree
          ≤ max (C a + C (Real.cos φ) * X * E₁).natDegree (C (Real.sin φ) * (1 - X^2) * P₁).natDegree :=
            Polynomial.natDegree_sub_le _ _
        _ ≤ max (max (C a : Polynomial ℝ).natDegree (C (Real.cos φ) * X * E₁).natDegree)
              (C (Real.sin φ) * (1 - X^2) * P₁).natDegree := by
            apply max_le_max _ le_rfl
            exact Polynomial.natDegree_add_le _ _
        _ ≤ Q.natDegree := by
            apply max_le (max_le h1 h2) h3
    · -- deg P + 1 ≤ deg Q or P = 0.
      by_cases hP0 : P = 0
      · right; exact hP0
      left
      rw [hP_def]
      have h1 : (C (Real.cos φ) * X * P₁).natDegree ≤ Q.natDegree - 1 := by
        rcases hP₁deg with hP₁ | hP₁
        · calc (C (Real.cos φ) * X * P₁).natDegree ≤ (C (Real.cos φ) * X).natDegree + P₁.natDegree :=
                Polynomial.natDegree_mul_le
            _ ≤ 1 + P₁.natDegree := by
                apply Nat.add_le_add_right
                calc (C (Real.cos φ) * X).natDegree ≤ (C (Real.cos φ)).natDegree + (X : ℝ[X]).natDegree :=
                      Polynomial.natDegree_mul_le
                  _ ≤ 1 := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
            _ ≤ 1 + (Q₁.natDegree - 1) := by omega
            _ ≤ Q.natDegree - 1 := by omega
        · rw [hP₁, mul_zero, Polynomial.natDegree_zero]; omega
      have h2 : (C (Real.sin φ) * E₁).natDegree ≤ Q.natDegree - 1 := by
        calc (C (Real.sin φ) * E₁).natDegree ≤ E₁.natDegree := Polynomial.natDegree_C_mul_le _ _
          _ ≤ Q₁.natDegree := hE₁deg
          _ ≤ Q.natDegree - 1 := by omega
      calc (C (Real.cos φ) * X * P₁ - C (Real.sin φ) * E₁).natDegree + 1
          ≤ max (C (Real.cos φ) * X * P₁).natDegree (C (Real.sin φ) * E₁).natDegree + 1 := by
            exact Nat.add_le_add_right (Polynomial.natDegree_sub_le _ _) 1
        _ ≤ (Q.natDegree - 1) + 1 := by
            exact Nat.add_le_add_right (max_le h1 h2) 1
        _ ≤ Q.natDegree := by omega
    · -- The identity.
      intro θ
      have hc := Real.cos_add φ θ
      have hident := hident₁ θ
      have hsc := Real.sin_sq_add_cos_sq θ
      rw [← hXmul]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        hE_def, hP_def, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow]
      rw [hident, hc]
      have hsub : (1 : ℝ) - (Real.cos θ)^2 = (Real.sin θ)^2 := by nlinarith [hsc]
      rw [hsub]
      ring
    · -- E(1) = Q(cos φ).
      rw [hE_def, ← hXmul]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, one_pow]
      rw [hE₁1]
      ring
    · -- P(1) = -sin φ Q'(cos φ).
      rw [hP_def, ← hXmul]
      have hQderiv : (X * Q₁ + C a).derivative = Q₁ + X * Q₁.derivative := by
        rw [Polynomial.derivative_add, Polynomial.derivative_C, add_zero, Polynomial.derivative_mul,
          Polynomial.derivative_X, one_mul]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        hQderiv, Polynomial.eval_add, one_mul]
      rw [hP₁1, hE₁1]
      ring

end CosShiftDecompose

open CosShiftDecompose

theorem solution (Q : Polynomial ℝ) (φ : ℝ) :
    ∃ E P : Polynomial ℝ, E.natDegree ≤ Q.natDegree ∧ (P.natDegree + 1 ≤ Q.natDegree ∨ P = 0) ∧
      (∀ θ : ℝ, Q.eval (Real.cos (φ + θ)) = E.eval (Real.cos θ) + P.eval (Real.cos θ) * Real.sin θ) ∧
      P.eval 1 = -Real.sin φ * Q.derivative.eval (Real.cos φ) := by
  obtain ⟨E, P, h1, h2, h3, _, h5⟩ := aux Q.natDegree Q φ le_rfl
  exact ⟨E, P, h1, h2, h3, h5⟩

end CommunityReplay_843c9344_d8e3_4942_b43f_89bfe0ccefc9

noncomputable def cos_shift_decompose := @CommunityReplay_843c9344_d8e3_4942_b43f_89bfe0ccefc9.solution

namespace CommunityReplay_253170f5_9d88_4177_a7b7_8c64c41b5b20
open Polynomial Polynomial.Chebyshev Real

theorem solution (Q : Polynomial ℝ) {d : ℕ} (hd : Q.natDegree ≤ d)
    (h : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → |Q.eval x| ≤ 1) :
    ∀ c : ℝ, -1 ≤ c → c ≤ 1 → (1 - c^2) * (Q.derivative.eval c)^2 ≤ (d : ℝ)^2 := by
  intro c hc1 hc2
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- d = 0: Q constant, Q' = 0.
    subst hd0
    have hQ0 : Q.natDegree = 0 := Nat.le_zero.mp hd
    obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hQ0
    rw [← ha, Polynomial.derivative_C, Polynomial.eval_zero]
    norm_num
  · -- d ≥ 1.
    have hdr : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
    have hdr_pos : (0 : ℝ) < (d : ℝ) := by linarith
    -- c = ±1: trivial.
    rcases eq_or_lt_of_le hc1 with hc1eq | hc1lt
    · have : (1 : ℝ) - c^2 = 0 := by rw [← hc1eq]; ring
      rw [this, zero_mul]; positivity
    rcases eq_or_lt_of_le hc2 with hc2eq | hc2lt
    · have : (1 : ℝ) - c^2 = 0 := by rw [hc2eq]; ring
      rw [this, zero_mul]; positivity
    -- c ∈ (-1, 1).
    set φ := Real.arccos c with hφ_def
    have hcos : Real.cos φ = c := Real.cos_arccos hc1 hc2
    have hsin : Real.sin φ = Real.sqrt (1 - c^2) := by
      rw [hφ_def]; exact Real.sin_arccos c
    have hsin_pos : (0 : ℝ) < Real.sin φ := by
      rw [hsin]; apply Real.sqrt_pos.mpr; nlinarith
    -- Obtain the odd-part polynomial P.
    obtain ⟨E, P, hEdeg, hPdeg, hident, hP1⟩ := cos_shift_decompose Q φ
    -- (1-x²) P(x)² ≤ 1 on [-1,1].
    have hPbound : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (1 - x^2) * (P.eval x)^2 ≤ 1 := by
      intro x hx1 hx2
      set θ := Real.arccos x with hθ_def
      have hcosθ : Real.cos θ = x := Real.cos_arccos hx1 hx2
      have hsinθ : Real.sin θ = Real.sqrt (1 - x^2) := by
        rw [hθ_def]; exact Real.sin_arccos x
      have hsinθ_sq : (Real.sin θ)^2 = 1 - x^2 := by
        rw [hsinθ, Real.sq_sqrt (by nlinarith : (0:ℝ) ≤ 1 - x^2)]
      -- Q(cos(φ + θ)) = E(x) + P(x) sin θ and Q(cos(φ - θ)) = E(x) - P(x) sin θ.
      have h1 := hident θ
      have h2 := hident (-θ)
      rw [hcosθ] at h1
      rw [Real.cos_neg, Real.sin_neg, hcosθ, mul_neg] at h2
      -- Subtract: Q(cos(φ+θ)) - Q(cos(φ-θ)) = 2 P(x) sin θ.
      have hdiff : Q.eval (Real.cos (φ + θ)) - Q.eval (Real.cos (φ + -θ)) = 2 * P.eval x * Real.sin θ := by
        rw [h1, h2]; ring
      -- |Q(cos ·)| ≤ 1.
      have hQ1 : |Q.eval (Real.cos (φ + θ))| ≤ 1 := h _ (Real.neg_one_le_cos _) (Real.cos_le_one _)
      have hQ2 : |Q.eval (Real.cos (φ + -θ))| ≤ 1 := h _ (Real.neg_one_le_cos _) (Real.cos_le_one _)
      -- So |2 P(x) sin θ| ≤ 2.
      have : |2 * P.eval x * Real.sin θ| ≤ 2 := by
        rw [← hdiff]
        calc |Q.eval (Real.cos (φ + θ)) - Q.eval (Real.cos (φ + -θ))|
            ≤ |Q.eval (Real.cos (φ + θ))| + |Q.eval (Real.cos (φ + -θ))| := abs_sub _ _
          _ ≤ 1 + 1 := add_le_add hQ1 hQ2
          _ = 2 := by ring
      -- So (P(x) sin θ)² ≤ 1, i.e., (1-x²) P(x)² ≤ 1.
      have hsq : (P.eval x * Real.sin θ)^2 ≤ 1 := by nlinarith [this, abs_nonneg (2 * P.eval x * Real.sin θ), sq_abs (2 * P.eval x * Real.sin θ)]
      calc (1 - x^2) * (P.eval x)^2 = (P.eval x)^2 * (Real.sin θ)^2 := by rw [hsinθ_sq]; ring
        _ = (P.eval x * Real.sin θ)^2 := by ring
        _ ≤ 1 := hsq
    -- Set p := (C d) * P.
    set p : Polynomial ℝ := C (d : ℝ) * P with hp_def
    have hpdeg : p.natDegree < d := by
      rw [hp_def]
      have hPP : P.natDegree < d := by
        rcases hPdeg with h1 | h2
        · omega
        · rw [h2, Polynomial.natDegree_zero]; exact hdpos
      calc (C (d : ℝ) * P).natDegree ≤ P.natDegree := Polynomial.natDegree_C_mul_le _ _
        _ < d := hPP
    have hpbound : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (1 - x^2) * (p.eval x)^2 ≤ (d : ℝ)^2 := by
      intro x hx1 hx2
      rw [hp_def]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      have := hPbound x hx1 hx2
      nlinarith [this, sq_nonneg (P.eval x)]
    -- Apply cheb_compare_outer at c = 1.
    have hcmp := cheb_compare_outer p hdpos hpdeg hpbound 1 (by norm_num) (by norm_num) (by simp)
    have hT'1 := cheb_deriv_abs_le d 1 (by norm_num) (by norm_num)
    have hp1 : |p.eval 1| ≤ (d : ℝ)^2 := le_trans hcmp hT'1
    -- p(1) = d P(1) = d (-sin φ Q'(c)).
    have hp1val : p.eval 1 = (d : ℝ) * (-Real.sin φ * Q.derivative.eval c) := by
      rw [hp_def]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      rw [hP1, hcos]
    rw [hp1val] at hp1
    -- |d sin φ Q'(c)| ≤ d², so sin φ |Q'(c)| ≤ d.
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hsin_pos.le, abs_of_nonneg hdr_pos.le] at hp1
    have hsin2 : (Real.sin φ)^2 = 1 - c^2 := by
      rw [hsin, Real.sq_sqrt (by nlinarith : (0:ℝ) ≤ 1 - c^2)]
    -- (1-c²) Q'(c)² = sin²φ Q'(c)².
    have heq1 : (1 - c^2) * (Q.derivative.eval c)^2 = (Real.sin φ * |Q.derivative.eval c|)^2 := by
      rw [← hsin2, mul_pow, sq_abs]
    rw [heq1]
    have h1 : Real.sin φ * |Q.derivative.eval c| ≤ (d : ℝ) := by
      nlinarith [hp1, abs_nonneg (Q.derivative.eval c), hsin_pos, hdr_pos]
    nlinarith [h1, mul_nonneg hsin_pos.le (abs_nonneg (Q.derivative.eval c))]

end CommunityReplay_253170f5_9d88_4177_a7b7_8c64c41b5b20

noncomputable def bernstein_unit := @CommunityReplay_253170f5_9d88_4177_a7b7_8c64c41b5b20.solution

namespace CommunityReplay_613a8ef2_e928_4d79_97fb_7c8e2e4165ef
open Polynomial Polynomial.Chebyshev

theorem solution (p : Polynomial ℝ) {d : ℕ} (hd : p.natDegree < d)
    (h : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (1 - x^2) * (p.eval x)^2 ≤ (d : ℝ)^2) :
    ∀ c : ℝ, -1 ≤ c → c ≤ 1 → |p.eval c| ≤ (d : ℝ)^2 := by
  intro c hc1 hc2
  have hd_pos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (fun hd0 => by omega)
  have hdr_pos : (0 : ℝ) < (d : ℝ) := by positivity
  have hc2_nonneg : (0 : ℝ) ≤ 1 - c^2 := by nlinarith
  by_cases hcase : (d : ℝ)^2 * (1 - c^2) ≤ 1
  · -- Comparison case: |c| near ±1.
    have hcmp := cheb_compare_outer p hd_pos hd h c hc1 hc2 hcase
    calc |p.eval c| ≤ |(derivative (T ℝ (d : ℤ))).eval c| := hcmp
      _ ≤ (d : ℝ)^2 := cheb_deriv_abs_le d c hc1 hc2
  · -- Direct Bernstein case: |c| in the middle.
    push Not at hcase
    have hbern := h c hc1 hc2
    -- (1 - c²) p(c)² ≤ d², and d²(1-c²) > 1, so p(c)² ≤ d²/(1-c²) < d⁴.
    have h1c_pos : (0 : ℝ) < 1 - c^2 := by
      by_contra hle
      push Not at hle
      have : (1 - c^2 : ℝ) = 0 := le_antisymm hle hc2_nonneg
      rw [this, mul_zero] at hcase
      linarith
    have hpc : (p.eval c)^2 ≤ (d : ℝ)^2 / (1 - c^2) := by
      rw [le_div_iff₀ h1c_pos]
      nlinarith [hbern]
    have hdiv : (d : ℝ)^2 / (1 - c^2) < (d : ℝ)^2 * (d : ℝ)^2 := by
      rw [div_lt_iff₀ h1c_pos]
      calc (d : ℝ)^2 = (d : ℝ)^2 * 1 := (mul_one _).symm
        _ < (d : ℝ)^2 * ((d : ℝ)^2 * (1 - c^2)) := by
            apply mul_lt_mul_of_pos_left hcase
            positivity
        _ = (d : ℝ)^2 * (d : ℝ)^2 * (1 - c^2) := by ring
    have hpc2 : (p.eval c)^2 ≤ ((d : ℝ)^2)^2 := by nlinarith [hpc, hdiv]
    have hd2_nonneg : (0 : ℝ) ≤ (d : ℝ)^2 := by positivity
    exact abs_le.mpr (abs_le_of_sq_le_sq' hpc2 hd2_nonneg)

end CommunityReplay_613a8ef2_e928_4d79_97fb_7c8e2e4165ef

noncomputable def markov_from_bernstein := @CommunityReplay_613a8ef2_e928_4d79_97fb_7c8e2e4165ef.solution

namespace CommunityReplay_2f155b73_36df_493a_aa64_b05e2c3ae72a
open Polynomial

/-- Sketch: reduce `markov_unit` to `bernstein_unit` + `markov_from_bernstein`.
Route: A. Markov 1889. Step 1 (Bernstein): `(1-c²) Q'(c)² ≤ d²` on `[-1,1]`.
Step 2 (comparison to T'_d): any `p` of degree `< d` satisfying the Bernstein
bound satisfies `|p| ≤ d²` on `[-1,1]`. Apply Step 2 to `p := Q'`.
Degenerate case `d = 0`: `Q` is constant, `Q' = 0`. -/
theorem solution (Q : Polynomial ℝ) {d : ℕ} (hd : Q.natDegree ≤ d)
    (h : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → |Q.eval x| ≤ 1) :
    ∀ c : ℝ, -1 ≤ c → c ≤ 1 → |Q.derivative.eval c| ≤ (d : ℝ)^2 := by
  intro c hc1 hc2
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- d = 0: Q is constant, Q' = 0.
    subst hd0
    have hQ0 : Q.natDegree = 0 := Nat.le_zero.mp hd
    have : Q.derivative = 0 := by
      have := Polynomial.natDegree_eq_zero.mp hQ0
      obtain ⟨a, ha⟩ := this
      rw [← ha, Polynomial.derivative_C]
    rw [this, Polynomial.eval_zero, abs_zero]
    norm_num
  · -- d ≥ 1: apply Bernstein + markov_from_bernstein.
    have hbern := bernstein_unit Q hd h
    have hdeg : Q.derivative.natDegree < d := by
      rcases Nat.eq_zero_or_pos Q.natDegree with hQ0 | hQpos
      · -- Q is constant, Q' = 0.
        have : Q.derivative = 0 := by
          have := Polynomial.natDegree_eq_zero.mp hQ0
          obtain ⟨a, ha⟩ := this
          rw [← ha, Polynomial.derivative_C]
        rw [this, Polynomial.natDegree_zero]
        exact hdpos
      · exact (Polynomial.natDegree_derivative_lt (Nat.pos_iff_ne_zero.mp hQpos)).trans_le hd
    exact markov_from_bernstein Q.derivative hdeg hbern c hc1 hc2

end CommunityReplay_2f155b73_36df_493a_aa64_b05e2c3ae72a

noncomputable def markov_unit := @CommunityReplay_2f155b73_36df_493a_aa64_b05e2c3ae72a.solution

namespace CommunityReplay_b0875906_c30b_44d6_9d22_a6db13c06b58
open Polynomial Set

namespace CMRSketch

/-- A polynomial equal to the constant `m` on an infinite interval is `C m`. -/
lemma eq_C_of_const_on_Icc {Q : Polynomial ℝ} {a b m : ℝ} (hab : a < b)
    (h : ∀ x : ℝ, a ≤ x → x ≤ b → Q.eval x = m) : Q = C m := by
  have hsub : ∀ x ∈ Set.Icc a b, (Q - C m).IsRoot x := by
    intro x hx
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C, h x hx.1 hx.2, sub_self]
  have hIcc_inf : (Set.Icc a b).Infinite := Set.infinite_coe_iff.mp (Set.Icc.infinite hab)
  have hinf : Set.Infinite {x | (Q - C m).IsRoot x} := hIcc_inf.mono hsub
  have h0 := Polynomial.eq_zero_of_infinite_isRoot (Q - C m) hinf
  exact sub_eq_zero.mp h0

end CMRSketch

open CMRSketch

/-- Sketch: reduce `classical_markov_range` on `[a,b]` with bounds `m ≤ Q ≤ M`
to `markov_unit` (the `[-1,1]`, `|Q| ≤ 1` form). If `m = M`, `Q` is constant so `Q' = 0`.
Otherwise affine-rescale `P(u) := (2 Q((b-a)(u+1)/2 + a) - M - m)/(M - m)` and apply
`markov_unit` to `P`. -/
theorem solution
    (a b : ℝ) (hab : a < b) (Q : Polynomial ℝ) {d : ℕ} (hd : Q.natDegree ≤ d)
    (m M : ℝ)
    (hm : ∀ x : ℝ, a ≤ x → x ≤ b → m ≤ Q.eval x)
    (hM : ∀ x : ℝ, a ≤ x → x ≤ b → Q.eval x ≤ M) :
    ∀ c : ℝ, a ≤ c → c ≤ b → |Q.derivative.eval c| ≤ (d : ℝ)^2 * (M - m) / (b - a) := by
  intro c hca hcb
  have hba : (0 : ℝ) < b - a := by linarith
  have hmM : m ≤ M := (hm a le_rfl hab.le).trans (hM a le_rfl hab.le)
  rcases eq_or_lt_of_le hmM with hmM_eq | hmM_lt
  · -- Degenerate: m = M, Q is constant on [a,b].
    subst hmM_eq
    have hQc : Q = C m := eq_C_of_const_on_Icc hab (fun x hx1 hx2 => le_antisymm (hM x hx1 hx2) (hm x hx1 hx2))
    rw [hQc, Polynomial.derivative_C, Polynomial.eval_zero, abs_zero, sub_self, mul_zero, zero_div]
  · -- Nondegenerate: m < M.
    set α := (b - a) / 2 with hα_def
    set β := (a + b) / 2 with hβ_def
    have hα_pos : (0 : ℝ) < α := by rw [hα_def]; linarith
    have hMm : (0 : ℝ) < M - m := by linarith
    -- The affine polynomial L(u) = α u + β.
    set L : Polynomial ℝ := C α * X + C β with hL_def
    -- The rescaled polynomial P := (2/(M-m)) * Q.comp L - (M+m)/(M-m).
    set P : Polynomial ℝ := C (2 / (M - m)) * Q.comp L - C ((M + m) / (M - m)) with hP_def
    -- 1. L evaluates as an affine map.
    have hL_eval : ∀ u : ℝ, L.eval u = α * u + β := by
      intro u; rw [hL_def]; simp
    -- 2. For u ∈ [-1,1], L(u) ∈ [a,b].
    have hL_mem : ∀ u : ℝ, -1 ≤ u → u ≤ 1 → a ≤ L.eval u ∧ L.eval u ≤ b := by
      intro u hu1 hu2
      rw [hL_eval]
      constructor
      · rw [hα_def, hβ_def]; nlinarith
      · rw [hα_def, hβ_def]; nlinarith
    -- 3. P evaluates as the affine rescale of Q.
    have hP_eval : ∀ u : ℝ, P.eval u = (2 * Q.eval (α * u + β) - M - m) / (M - m) := by
      intro u
      rw [hP_def]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
        hL_eval u]
      ring
    -- 4. |P| ≤ 1 on [-1,1].
    have hP_bound : ∀ u : ℝ, -1 ≤ u → u ≤ 1 → |P.eval u| ≤ 1 := by
      intro u hu1 hu2
      obtain ⟨hmem1, hmem2⟩ := hL_mem u hu1 hu2
      rw [hL_eval] at hmem1 hmem2
      have h_lo := hm (α * u + β) hmem1 hmem2
      have h_hi := hM (α * u + β) hmem1 hmem2
      rw [hP_eval, abs_le]
      constructor
      · rw [le_div_iff₀ hMm]; nlinarith
      · rw [div_le_iff₀ hMm]; nlinarith
    -- 5. deg P ≤ d.
    have hL_deg : L.natDegree = 1 := by
      rw [hL_def]
      compute_degree!
      exact ne_of_gt hα_pos
    have hP_deg : P.natDegree ≤ d := by
      have h1 : (Q.comp L).natDegree = Q.natDegree * L.natDegree := Polynomial.natDegree_comp
      rw [hL_deg, mul_one] at h1
      calc P.natDegree = (C (2 / (M - m)) * Q.comp L - C ((M + m) / (M - m))).natDegree := by rw [hP_def]
        _ ≤ max (C (2 / (M - m)) * Q.comp L).natDegree (C ((M + m) / (M - m))).natDegree :=
            Polynomial.natDegree_sub_le _ _
        _ = (C (2 / (M - m)) * Q.comp L).natDegree := by rw [Polynomial.natDegree_C]; exact Nat.max_eq_left (Nat.zero_le _)
        _ ≤ (Q.comp L).natDegree := Polynomial.natDegree_C_mul_le _ _
        _ = Q.natDegree := h1
        _ ≤ d := hd
    -- 6. Derivative of P.
    have hL_deriv : derivative L = C α := by rw [hL_def]; simp
    have hP_deriv : ∀ u : ℝ, P.derivative.eval u = (b - a) / (M - m) * Q.derivative.eval (α * u + β) := by
      intro u
      rw [hP_def]
      simp only [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero,
        Polynomial.derivative_C_mul, Polynomial.derivative_comp, hL_deriv,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, hL_eval u]
      rw [hα_def]; ring
    -- 7. Apply markov_unit to P.
    have hmarkov := markov_unit P hP_deg hP_bound
    -- 8. Instantiate at u := (2c - a - b)/(b - a).
    set u := (2 * c - a - b) / (b - a) with hu_def
    have hu1 : -1 ≤ u := by rw [hu_def]; rw [le_div_iff₀ hba]; linarith
    have hu2 : u ≤ 1 := by rw [hu_def]; rw [div_le_iff₀ hba]; linarith
    have hcu : α * u + β = c := by rw [hα_def, hβ_def, hu_def]; field_simp; ring
    have := hmarkov u hu1 hu2
    rw [hP_deriv u, hcu, abs_mul, abs_div] at this
    have hba_abs : |b - a| = b - a := abs_of_pos hba
    have hMm_abs : |M - m| = M - m := abs_of_pos hMm
    rw [hba_abs, hMm_abs] at this
    -- this : (b-a)/(M-m) * |Q'(c)| ≤ d²
    -- want : |Q'(c)| ≤ d²(M-m)/(b-a)
    rw [le_div_iff₀ hba]
    have key : |Q.derivative.eval c| * (b - a) = (M - m) * ((b - a) / (M - m) * |Q.derivative.eval c|) := by
      field_simp
    rw [key]
    calc (M - m) * ((b - a) / (M - m) * |Q.derivative.eval c|)
        ≤ (M - m) * (↑d ^ 2) := mul_le_mul_of_nonneg_left this (le_of_lt hMm)
      _ = ↑d ^ 2 * (M - m) := by ring

end CommunityReplay_b0875906_c30b_44d6_9d22_a6db13c06b58

noncomputable def classical_markov_range := @CommunityReplay_b0875906_c30b_44d6_9d22_a6db13c06b58.solution

namespace CommunityReplay_eb8e04fd_9e23_456a_a835_d4d941d07c76
open Polynomial Set

namespace NSMarkovSketch

/-- Mean-value inequality for a polynomial on an interval:
if `|Q'(z)| ≤ B` on `[a,b]` and `x, y ∈ [a,b]`, then `|Q(x) - Q(y)| ≤ B·|x - y|`. -/
lemma mvt_dist_bound (Q : Polynomial ℝ) {a b : ℝ}
    (B : ℝ) (hB : ∀ z : ℝ, a ≤ z → z ≤ b → |Q.derivative.eval z| ≤ B)
    (x y : ℝ) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |Q.eval x - Q.eval y| ≤ B * |x - y| := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · obtain ⟨ξ, hξmem, hξ⟩ := exists_hasDerivAt_eq_slope
      (fun z => Q.eval z) (fun z => Q.derivative.eval z) hxy
      ((Polynomial.continuous Q).continuousOn)
      (fun z _ => Polynomial.hasDerivAt Q z)
    have hξa : a ≤ ξ := hx.1.trans hξmem.1.le
    have hξb : ξ ≤ b := hξmem.2.le.trans hy.2
    have hξB : |Q.derivative.eval ξ| ≤ B := hB ξ hξa hξb
    have hyx : (0 : ℝ) < y - x := by linarith
    have hne : (y : ℝ) - x ≠ 0 := by linarith
    have heq : Q.eval y - Q.eval x = Q.derivative.eval ξ * (y - x) := by
      have := hξ
      field_simp [hne] at this
      linarith [this]
    calc |Q.eval x - Q.eval y| = |Q.eval y - Q.eval x| := abs_sub_comm _ _
      _ = |Q.derivative.eval ξ| * |y - x| := by rw [heq, abs_mul]
      _ ≤ B * |y - x| := mul_le_mul_of_nonneg_right hξB (abs_nonneg _)
      _ = B * |x - y| := by rw [abs_sub_comm]
  · subst hxy; simp
  · obtain ⟨ξ, hξmem, hξ⟩ := exists_hasDerivAt_eq_slope
      (fun z => Q.eval z) (fun z => Q.derivative.eval z) hxy
      ((Polynomial.continuous Q).continuousOn)
      (fun z _ => Polynomial.hasDerivAt Q z)
    have hξa : a ≤ ξ := hy.1.trans hξmem.1.le
    have hξb : ξ ≤ b := hξmem.2.le.trans hx.2
    have hξB : |Q.derivative.eval ξ| ≤ B := hB ξ hξa hξb
    have hxy' : (0 : ℝ) < x - y := by linarith
    have hne : (x : ℝ) - y ≠ 0 := by linarith
    have heq : Q.eval x - Q.eval y = Q.derivative.eval ξ * (x - y) := by
      have := hξ
      field_simp [hne] at this
      linarith [this]
    calc |Q.eval x - Q.eval y| = |Q.derivative.eval ξ| * |x - y| := by rw [heq, abs_mul]
      _ ≤ B * |x - y| := mul_le_mul_of_nonneg_right hξB (abs_nonneg _)

/-- `round` is monotone. -/
lemma round_mono' : Monotone (round : ℝ → ℤ) := by
  intro x y hxy
  rw [round_eq, round_eq]
  exact Int.floor_mono (by linarith)

/-- For `x ∈ [0, b]` (`b : ℕ`), there is an integer grid point `n ∈ {0, …, b}` within
distance `1/2` of `x`. -/
lemma exists_grid_near {b : ℕ} (x : ℝ) (hx0 : 0 ≤ x) (hxb : x ≤ (b : ℝ)) :
    ∃ n : ℕ, n ≤ b ∧ |x - (n : ℝ)| ≤ 1 / 2 := by
  have hr_nonneg : (0 : ℤ) ≤ round x := by
    have : round (0 : ℝ) ≤ round x := round_mono' hx0
    simpa using this
  have hr_le : round x ≤ (b : ℤ) := by
    have : round x ≤ round ((b : ℕ) : ℝ) := round_mono' hxb
    rw [round_natCast] at this
    exact this
  refine ⟨(round x).toNat, ?_, ?_⟩
  · exact Int.toNat_le.mpr hr_le
  · have hcast : (((round x).toNat : ℕ) : ℝ) = ((round x : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hr_nonneg
    rw [hcast]
    exact abs_sub_round x

end NSMarkovSketch

open NSMarkovSketch

theorem solution : ∀ {b : ℕ} (hb : 1 ≤ b) (Q : Polynomial ℝ) {d : ℕ} (h_deg : Q.natDegree ≤ d) (h_lo : ∀ t : ℕ, t ≤ b → 0 ≤ Q.eval (t : ℝ)) (h_hi : ∀ t : ℕ, t ≤ b → Q.eval (t : ℝ) ≤ 1) (h_d2b : (d : ℝ)^2 < (b : ℝ)), ∀ c : ℝ, 0 ≤ c → c ≤ (b : ℝ) → |Q.derivative.eval c| ≤ (d : ℝ)^2 / ((b : ℝ) - (d : ℝ)^2) := by
  intro b hb Q d h_deg h_lo h_hi h_d2b
  have hb_pos : (0 : ℝ) < (b : ℝ) := by
    have : (0 : ℕ) < b := by omega
    exact_mod_cast this
  have hbd2 : (0 : ℝ) < (b : ℝ) - (d : ℝ) ^ 2 := by linarith
  -- Extremum of Q on [0, b] via compactness.
  have hcompact : IsCompact (Set.Icc (0 : ℝ) (b : ℝ)) := isCompact_Icc
  have hnonempty : (Set.Icc (0 : ℝ) (b : ℝ)).Nonempty := ⟨0, ⟨le_refl 0, le_of_lt hb_pos⟩⟩
  have hcont : ContinuousOn (fun x => Q.eval x) (Set.Icc (0 : ℝ) (b : ℝ)) :=
    (Polynomial.continuous Q).continuousOn
  obtain ⟨xM, hxM_mem, hxM⟩ := hcompact.exists_isMaxOn hnonempty hcont
  obtain ⟨xm, hxm_mem, hxm⟩ := hcompact.exists_isMinOn hnonempty hcont
  set M := Q.eval xM with hMdef
  set m := Q.eval xm with hmdef
  have hmM : m ≤ M := by
    have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (b : ℝ) := ⟨le_refl 0, le_of_lt hb_pos⟩
    calc m ≤ Q.eval 0 := hxm hmem0
      _ ≤ M := hxM hmem0
  -- Apply the classical Markov child with the continuous range `[m, M]`.
  have hmarkov := classical_markov_range 0 (b : ℝ) hb_pos Q h_deg m M
    (fun x hx0 hxb => hxm ⟨hx0, hxb⟩) (fun x hx0 hxb => hxM ⟨hx0, hxb⟩)
  -- hmarkov : ∀ c, 0 ≤ c → c ≤ b → |Q'(c)| ≤ d²(M - m)/(b - 0) = d²(M - m)/b
  simp only [sub_zero] at hmarkov
  set B := (d : ℝ) ^ 2 * (M - m) / (b : ℝ) with hBdef
  have hBnonneg : (0 : ℝ) ≤ B := by
    rw [hBdef]
    have : (0 : ℝ) ≤ M - m := by linarith
    positivity
  -- Nearest-grid bound for `M`: `M ≤ 1 + B/2`.
  have hMbound : M ≤ 1 + B / 2 := by
    obtain ⟨n, hn_le, hn_dist⟩ := exists_grid_near xM hxM_mem.1 hxM_mem.2
    have hQn_hi : Q.eval (n : ℝ) ≤ 1 := h_hi n hn_le
    have hdist : |Q.eval xM - Q.eval (n : ℝ)| ≤ B * (1 / 2) := by
      refine (mvt_dist_bound Q B hmarkov xM (n : ℝ) hxM_mem ?_).trans ?_
      · refine ⟨Nat.cast_nonneg n, ?_⟩
        exact_mod_cast hn_le
      · exact mul_le_mul_of_nonneg_left hn_dist hBnonneg
    have : Q.eval xM - Q.eval (n : ℝ) ≤ B * (1 / 2) := (le_abs_self _).trans hdist
    linarith
  -- Nearest-grid bound for `m`: `m ≥ -B/2`.
  have hmbound : -(B / 2) ≤ m := by
    obtain ⟨n, hn_le, hn_dist⟩ := exists_grid_near xm hxm_mem.1 hxm_mem.2
    have hQn_lo : (0 : ℝ) ≤ Q.eval (n : ℝ) := h_lo n hn_le
    have hdist : |Q.eval (n : ℝ) - Q.eval xm| ≤ B * (1 / 2) := by
      refine (mvt_dist_bound Q B hmarkov (n : ℝ) xm ?_ hxm_mem).trans ?_
      · refine ⟨Nat.cast_nonneg n, ?_⟩
        exact_mod_cast hn_le
      · rw [abs_sub_comm]
        exact mul_le_mul_of_nonneg_left hn_dist hBnonneg
    have : Q.eval (n : ℝ) - Q.eval xm ≤ B * (1 / 2) := (le_abs_self _).trans hdist
    linarith
  -- Combine: `M - m ≤ 1 + B`.
  have hrange : M - m ≤ 1 + B := by linarith
  -- Algebra: `B = d²(M-m)/b ≤ d²(1+B)/b`, so `B ≤ d²/(b - d²)`.
  have hBle : B ≤ (d : ℝ) ^ 2 / ((b : ℝ) - (d : ℝ) ^ 2) := by
    have hBb : B * (b : ℝ) = (d : ℝ) ^ 2 * (M - m) := by
      rw [hBdef]; field_simp
    have h1 : B * (b : ℝ) ≤ (d : ℝ) ^ 2 * (1 + B) := by
      rw [hBb]
      have hdnonneg : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
      nlinarith [hrange, hdnonneg]
    have h2 : B * ((b : ℝ) - (d : ℝ) ^ 2) ≤ (d : ℝ) ^ 2 := by nlinarith [h1]
    have hinv : (0 : ℝ) < ((b : ℝ) - (d : ℝ) ^ 2)⁻¹ := by positivity
    have hm := mul_le_mul_of_nonneg_right h2 (le_of_lt hinv)
    rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hbd2), mul_one, ← div_eq_mul_inv] at hm
  -- Conclude.
  intro c hc0 hcb
  exact (hmarkov c hc0 hcb).trans hBle

end CommunityReplay_eb8e04fd_9e23_456a_a835_d4d941d07c76

noncomputable def ns_markov_grid_lemma := @CommunityReplay_eb8e04fd_9e23_456a_a835_d4d941d07c76.solution

namespace CommunityReplay_a74a903f_773e_41b5_9d17_83af91fb3d65
open Polynomial Set

/-- Sketch: reduce NS 1994 Lemma 2 (nonnegative form) to the Markov-on-the-grid
derivative bound `ns_markov_grid_lemma`.

Argument: if `b ≤ 2d²` we are done; otherwise `d² < b`. By MVT on `[0,1]`, using
`Q(0) = 0` and `Q(1) = 1`, there is `ξ ∈ (0,1)` with `Q'(ξ) = 1`. The child
lemma (a Markov / Coppersmith–Rivlin style bound) gives `|Q'(ξ)| ≤ d²/(b-d²)`.
Hence `1 ≤ d²/(b-d²)`, so `b - d² ≤ d²`, so `b ≤ 2d²` — contradiction. -/
theorem solution : ∀ {b : ℕ} (hb : 1 ≤ b) (Q : Polynomial ℝ) {d : ℕ} (h_deg : Q.natDegree ≤ d) (h_zero : Q.eval 0 = 0) (h_one : Q.eval 1 = 1) (h_lo : ∀ t : ℕ, t ≤ b → 0 ≤ Q.eval (t : ℝ)) (h_hi : ∀ t : ℕ, t ≤ b → Q.eval (t : ℝ) ≤ 1), b ≤ 2 * d^2 := by
  intro b hb Q d h_deg h_zero h_one h_lo h_hi
  by_cases hdb : b ≤ 2 * d ^ 2
  · exact hdb
  exfalso
  push_neg at hdb
  -- `hdb : 2 * d^2 < b`.
  have hd2b : (d : ℝ) ^ 2 < (b : ℝ) := by
    have : (2 : ℝ) * (d : ℝ) ^ 2 < (b : ℝ) := by exact_mod_cast hdb
    nlinarith [sq_nonneg (d : ℝ)]
  -- MVT on `[0,1]`: `∃ ξ ∈ (0,1), Q'(ξ) = 1`.
  obtain ⟨ξ, hξmem, hξ⟩ := exists_hasDerivAt_eq_slope
    (fun x => Q.eval x) (fun x => Q.derivative.eval x)
    (show (0 : ℝ) < 1 by norm_num)
    ((Polynomial.continuous Q).continuousOn)
    (fun x _ => Polynomial.hasDerivAt Q x)
  rw [h_zero, h_one] at hξ
  norm_num at hξ
  -- `hξ : Q.derivative.eval ξ = 1`; `hξmem : ξ ∈ Ioo 0 1`.
  have hξ0 : (0 : ℝ) ≤ ξ := le_of_lt hξmem.1
  have hξb : ξ ≤ (b : ℝ) := by
    have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith [hξmem.2]
  -- Apply the Markov child.
  have hmarkov := ns_markov_grid_lemma hb Q h_deg h_lo h_hi hd2b ξ hξ0 hξb
  rw [hξ] at hmarkov
  have h1 : (1 : ℝ) ≤ (d : ℝ) ^ 2 / ((b : ℝ) - (d : ℝ) ^ 2) := (le_abs_self 1).trans hmarkov
  have hbd2 : (0 : ℝ) < (b : ℝ) - (d : ℝ) ^ 2 := by linarith
  have h2 : (b : ℝ) - (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right h1 (le_of_lt hbd2)
    rw [one_mul, div_mul_cancel₀ _ (ne_of_gt hbd2)] at hm
    exact hm
  have hble : (b : ℝ) ≤ 2 * (d : ℝ) ^ 2 := by linarith
  have hnat : b ≤ 2 * d ^ 2 := by exact_mod_cast hble
  omega

end CommunityReplay_a74a903f_773e_41b5_9d17_83af91fb3d65

noncomputable def ns_lemma2_nonneg := @CommunityReplay_a74a903f_773e_41b5_9d17_83af91fb3d65.solution

namespace CommunityReplay_ac876a91_ecfb_4f48_9d6d_2e4e0cc78bf5
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
    b ≤ 2 * (polyDegree g)^2 := by
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
  -- Step 4: apply the Nisan–Szegedy Lemma 2 child.
  exact ns_lemma2_nonneg hb Q hQd hQ0 hQ1 hQ_lo hQ_hi

end CommunityReplay_ac876a91_ecfb_4f48_9d6d_2e4e0cc78bf5

noncomputable def polyDegree_distinguishing_units_bound := @CommunityReplay_ac876a91_ecfb_4f48_9d6d_2e4e0cc78bf5.solution

section
namespace BlockRestrictionReplay
/-!
# Polynomial degree under block-restriction

For a Boolean function `f : {0,1}ⁿ → {0,1}` of polynomial degree `d`,
restricting attention to a *block-substitution sub-cube* — fixing some
coordinates to `x`, and grouping the remaining coordinates into pairwise-
disjoint blocks each parameterised by a single bit — yields a Boolean
function on the smaller cube `{0,1}ᵇ` whose polynomial degree is also at
most `d`.

This is the missing block-substitution lemma in the Nisan-Szegedy
proof. Its proof requires:
1. A construction of the substituted multivariate polynomial via
   `MvPolynomial.bind₁` with linear or constant inputs at each variable.
2. A proof that `bind₁` of a polynomial of total degree `≤ d` into linear
   polynomials yields a polynomial of total degree `≤ d` (this is
   `bind₁_totalDegree_le` for the special case `k = 1`, missing from
   Mathlib at present).
3. A proof that the substituted polynomial agrees with the block-restricted
   function on the cube.

Left as a platform leaf — DEFERRED. Estimated 150-250 lines.
-/

/-- The "multi-flip" of `x` selected by `y` over an indexed family of
disjoint blocks: at coordinate `j`, flips `x j` iff some block `e i`
contains `j` and `y i = true`. With `Classical.dec`, this is
`noncomputable`. -/
noncomputable def blockFlipMulti_sol {n b : ℕ}
    (x : Fin n → Bool) (e : Fin b → Finset (Fin n))
    (y : Fin b → Bool) (j : Fin n) : Bool :=
  open Classical in
  if ∃ i, j ∈ e i ∧ y i = true then !x j else x j


/-!
# Proof — `block_restrict_polyDegree_le`

Construct the block-substitution polynomial `bind₁ s p` where `s` is linear
(or constant) at every variable, and show its `totalDegree` is bounded by
that of the original polynomial. This gives a polynomial witness for
the block-restricted Boolean function of degree `≤ polyDegree f`.
-/

open MvPolynomial

namespace BlockRestrict

variable {n b : ℕ}

/-! ### bind₁ degree-preservation for ≤ 1-degree substitutes -/

/-- Substituting linear-or-constant polynomials into `p` yields a polynomial
of total degree at most `p.totalDegree`. (The general case
`bind₁_totalDegree_le : (bind₁ s p).totalDegree ≤ k * p.totalDegree` for
`k = max (s i).totalDegree` specialises to this when `k = 1`.) -/
lemma bind₁_totalDegree_le_one
    {σ τ R : Type*} [CommSemiring R]
    (s : σ → MvPolynomial τ R)
    (h_each : ∀ i, (s i).totalDegree ≤ 1)
    (p : MvPolynomial σ R) :
    (bind₁ s p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intros m hm
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finset_prod _ _).trans ?_
  refine (Finset.sum_le_sum (fun i _ => totalDegree_pow _ _)).trans ?_
  refine (Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (h_each i))).trans ?_
  simp only [mul_one]
  exact le_totalDegree hm

/-! ### The substitution map for block-restriction -/

/-- The substitution polynomial for coordinate `j`. Linear in `Y_i` if `j`
lies in block `e i` (unique by disjointness), constant otherwise. -/
noncomputable def substMap (x : Fin n → Bool) (e : Fin b → Finset (Fin n))
    (j : Fin n) : MvPolynomial (Fin b) ℝ :=
  open Classical in
  if h : ∃ i, j ∈ e i then
    if x j then 1 - X h.choose else X h.choose
  else
    if x j then 1 else 0

lemma substMap_totalDegree_le_one (x : Fin n → Bool) (e : Fin b → Finset (Fin n))
    (j : Fin n) : (substMap x e j).totalDegree ≤ 1 := by
  classical
  unfold substMap
  by_cases h : ∃ i, j ∈ e i
  · rw [dif_pos h]
    by_cases hx : x j
    · rw [if_pos hx]
      refine (totalDegree_sub _ _).trans ?_
      rw [totalDegree_one, totalDegree_X]
      omega
    · rw [if_neg hx, totalDegree_X]
  · rw [dif_neg h]
    by_cases hx : x j
    · rw [if_pos hx, totalDegree_one]; omega
    · rw [if_neg hx]; simp

/-! ### Eval correspondence -/

/-- Disjointness: if `j ∈ e i` and `j ∈ e k`, then `i = k`. -/
lemma block_unique (e : Fin b → Finset (Fin n))
    (h_disj : ∀ i k : Fin b, i ≠ k → Disjoint (e i) (e k))
    {j : Fin n} {i k : Fin b} (hi : j ∈ e i) (hk : j ∈ e k) : i = k := by
  by_contra h_ne
  exact (Finset.disjoint_left.mp (h_disj i k h_ne)) hi hk

lemma blockFlipMulti_unique (x : Fin n → Bool) (e : Fin b → Finset (Fin n))
    (h_disj : ∀ i k : Fin b, i ≠ k → Disjoint (e i) (e k))
    (y : Fin b → Bool) (j : Fin n) {i : Fin b} (hi : j ∈ e i) :
    blockFlipMulti_sol x e y j = (if y i then !x j else x j) := by
  classical
  unfold blockFlipMulti_sol
  by_cases hy : y i = true
  · rw [if_pos ⟨i, hi, hy⟩, if_pos hy]
  · rw [if_neg hy]
    rw [if_neg]
    rintro ⟨k, hk, hyk⟩
    have heq : i = k := block_unique e h_disj hi hk
    rw [← heq] at hyk
    exact hy hyk

lemma blockFlipMulti_no_block (x : Fin n → Bool) (e : Fin b → Finset (Fin n))
    (y : Fin b → Bool) {j : Fin n} (h : ¬ ∃ i, j ∈ e i) :
    blockFlipMulti_sol x e y j = x j := by
  classical
  unfold blockFlipMulti_sol
  rw [if_neg]
  rintro ⟨i, hi, _⟩
  exact h ⟨i, hi⟩

/-- The evaluation of `substMap x e j` matches `boolToReal (blockFlipMulti_sol x e y j)`. -/
lemma eval_substMap (x : Fin n → Bool) (e : Fin b → Finset (Fin n))
    (h_disj : ∀ i k : Fin b, i ≠ k → Disjoint (e i) (e k))
    (y : Fin b → Bool) (j : Fin n) :
    MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) (substMap x e j)
      = (if blockFlipMulti_sol x e y j then (1 : ℝ) else 0) := by
  classical
  unfold substMap
  by_cases h : ∃ i, j ∈ e i
  · rw [dif_pos h]
    have h_chose : j ∈ e (Classical.choose h) := Classical.choose_spec h
    rw [blockFlipMulti_unique x e h_disj y j h_chose]
    by_cases hx : x j
    · rw [if_pos hx, hx]
      simp only [map_sub, map_one, eval_X]
      cases y (Classical.choose h) <;> simp
    · have hxf : x j = false := Bool.eq_false_of_not_eq_true hx
      rw [if_neg hx, hxf]
      simp only [eval_X]
      cases y (Classical.choose h) <;> simp
  · rw [dif_neg h, blockFlipMulti_no_block x e y h]
    by_cases hx : x j
    · rw [if_pos hx, hx]; simp
    · have hxf : x j = false := Bool.eq_false_of_not_eq_true hx
      rw [if_neg hx, hxf]; simp

end BlockRestrict

open BlockRestrict

/-! ### Main proof. -/

theorem solution
    {n b : ℕ} (f : BoolFunc n) (x : Fin n → Bool)
    (e : Fin b → Finset (Fin n))
    (h_disj : ∀ i j : Fin b, i ≠ j → Disjoint (e i) (e j)) :
    polyDegree (fun y : Fin b → Bool => f (blockFlipMulti_sol x e y))
      ≤ polyDegree f := by
  classical
  -- Get the polynomial witness for f at degree polyDegree f
  have hp : HasPolyRep f (polyDegree f) :=
    Nat.find_spec (⟨n, hasPolyRep_card f⟩ : ∃ d, HasPolyRep f d)
  obtain ⟨p, hp_deg, hp_eval⟩ := hp
  -- Build the substitution polynomial
  set q : MvPolynomial (Fin b) ℝ := bind₁ (substMap x e) p with hq_def
  -- Step 1: q.totalDegree ≤ p.totalDegree ≤ polyDegree f
  have hq_deg : q.totalDegree ≤ polyDegree f :=
    (bind₁_totalDegree_le_one (substMap x e) (substMap_totalDegree_le_one x e) p).trans hp_deg
  -- Step 2: q evaluates correctly: eval ∘ y on q matches g
  have hq_eval : ∀ y : Fin b → Bool,
      MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) q
        = if f (blockFlipMulti_sol x e y) then (1 : ℝ) else 0 := by
    intro y
    rw [hq_def]
    -- aeval_bind₁: aeval f (bind₁ g φ) = aeval (fun i => aeval f (g i)) φ
    -- For eval (a non-AlgHom version), we use the fact that eval = aeval applied to the right algebra map.
    -- More directly: use eval_bind₁-style by unfolding.
    have h_aeval :
        (MvPolynomial.aeval (fun i => if y i then (1 : ℝ) else 0)) (bind₁ (substMap x e) p)
        = (MvPolynomial.aeval
            (fun j => MvPolynomial.aeval (fun i => if y i then (1 : ℝ) else 0) (substMap x e j))) p :=
      MvPolynomial.aeval_bind₁ _ _ _
    -- aeval = eval (since the target algebra is the identity over ℝ).
    rw [MvPolynomial.aeval_eq_eval] at h_aeval
    rw [h_aeval]
    -- Goal: (aeval (fun j => eval ... (substMap x e j))) p = if f (...) then 1 else 0
    -- Rewrite the inner eval ... (substMap x e j) using eval_substMap.
    have h_eq_lambdas :
        (fun j : Fin n => MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0)
                            (substMap x e j))
          = (fun j : Fin n => if blockFlipMulti_sol x e y j then (1 : ℝ) else 0) := by
      funext j
      exact eval_substMap x e h_disj y j
    rw [h_eq_lambdas, MvPolynomial.aeval_eq_eval]
    exact hp_eval (blockFlipMulti_sol x e y)
  -- Step 3: assemble HasPolyRep witness for g at degree polyDegree f
  have h_witness : HasPolyRep (fun y : Fin b → Bool => f (blockFlipMulti_sol x e y))
                              (polyDegree f) := by
    refine ⟨q, hq_deg, ?_⟩
    intro y
    exact hq_eval y
  -- Step 4: apply Nat.find_le
  show Nat.find _ ≤ _
  exact Nat.find_le h_witness

end BlockRestrictionReplay
/-! Generic normalized Boolean composition, adapted from the independently checked
KushPower composition proof by Alexander Richard Towell with OpenAI Codex assistance.
The numeric amplification argument follows the composition method of Avishay Tal.
No platform dependency is assumed proved inside this packet. -/
namespace DegreeAmplification
noncomputable section
open Classical
open MvPolynomial

lemma degree_substitute_bound {n m : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (q : Fin n → MvPolynomial (Fin m) ℝ) (d : ℕ) (hq : ∀ i, (q i).totalDegree ≤ d) :
    (eval₂ C q p).totalDegree ≤ p.totalDegree * d := by
  rw [eval₂_eq]
  apply totalDegree_finsetSum_le
  intro u hu
  calc
    (C (p.coeff u) * ∏ i ∈ u.support, q i ^ u i).totalDegree
      ≤ (C (p.coeff u)).totalDegree + (∏ i ∈ u.support, q i ^ u i).totalDegree := totalDegree_mul _ _
    _ = (∏ i ∈ u.support, q i ^ u i).totalDegree := by simp
    _ ≤ ∑ i ∈ u.support, (q i ^ u i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ u.support, u i * d := by
      apply Finset.sum_le_sum
      intro i hi
      exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hq i))
    _ = (∑ i ∈ u.support, u i) * d := (Finset.sum_mul _ _ _).symm
    _ ≤ p.totalDegree * d := Nat.mul_le_mul_right d (le_totalDegree hu)

def compose {n m : ℕ} (f : BoolFunc n) (g : BoolFunc m) : BoolFunc (n*m) :=
  fun x => f fun i => g fun j => x (finProdFinEquiv (i,j))

lemma compose_degree {n m : ℕ} (f : BoolFunc n) (g : BoolFunc m) :
    polyDegree (compose f g) ≤ polyDegree f * polyDegree g := by
  obtain ⟨p,hp,he⟩ := Nat.find_spec (show ∃ d, HasPolyRep f d from ⟨n,hasPolyRep_card f⟩)
  obtain ⟨r,hr,hre⟩ := Nat.find_spec (show ∃ d, HasPolyRep g d from ⟨m,hasPolyRep_card g⟩)
  let q : Fin n → MvPolynomial (Fin (n*m)) ℝ := fun i => rename (fun j => finProdFinEquiv (i,j)) r
  apply Nat.find_min'
  refine ⟨eval₂ C q p, ?_, ?_⟩
  · exact (degree_substitute_bound _ q (polyDegree g) (fun i =>
      (totalDegree_rename_le _ _).trans hr)).trans (Nat.mul_le_mul_right _ hp)
  · intro x
    rw [eval_eval₂]
    have hq : (fun i => eval (fun j => if x j then (1:ℝ) else 0) (q i)) =
        (fun i => if g (fun j => x (finProdFinEquiv (i,j))) then (1:ℝ) else 0) := by
      funext i
      exact (eval_rename _ _ r).trans (hre _)
    have hc : (eval (fun j => if x j then (1:ℝ) else 0)).comp C = RingHom.id ℝ := by
      ext r
      simp
    rw [hq,hc,eval₂_id]
    exact he _

lemma compose_zero {n m : ℕ} (f : BoolFunc n) (g : BoolFunc m)
    (hf : f (fun _ => false) = false) (hg : g (fun _ => false) = false) :
    compose f g (fun _ => false) = false := by simp [compose,hg,hf]

lemma block_unit {n m : ℕ} (a : Fin (n*m)) (i : Fin n) :
    (fun j : Fin m => Function.update (fun _ => false) a true (finProdFinEquiv (i,j))) =
      if i = (finProdFinEquiv.symm a).1 then
        Function.update (fun _ => false) (finProdFinEquiv.symm a).2 true else fun _ => false := by
  funext j
  have hindex : finProdFinEquiv (i,j) = a ↔
      i = (finProdFinEquiv.symm a).1 ∧ j = (finProdFinEquiv.symm a).2 := by
    rw [Equiv.apply_eq_iff_eq_symm_apply]
    exact Prod.ext_iff
  by_cases hi : i = (finProdFinEquiv.symm a).1
  · rw [if_pos hi]
    simp only [Function.update_apply]
    congr 1
    apply propext
    exact ⟨fun h => (hindex.mp h).2, fun h => hindex.mpr ⟨hi,h⟩⟩
  · rw [if_neg hi]
    simp only [Function.update_apply]
    rw [if_neg (fun h => hi (hindex.mp h).1)]

lemma compose_unit {n m : ℕ} (f : BoolFunc n) (g : BoolFunc m)
    (hz : g (fun _ => false) = false)
    (hf : ∀ i, f (Function.update (fun _ => false) i true) = true)
    (hg : ∀ i, g (Function.update (fun _ => false) i true) = true) (a : Fin (n*m)) :
    compose f g (Function.update (fun _ => false) a true) = true := by
  unfold compose
  have hrows : (fun i : Fin n => g fun j => Function.update (fun _ => false) a true (finProdFinEquiv (i,j))) =
      Function.update (fun _ => false) (finProdFinEquiv.symm a).1 true := by
    funext i
    rw [block_unit]
    by_cases hi : i = (finProdFinEquiv.symm a).1
    · rw [if_pos hi, hg, hi]; simp
    · rw [if_neg hi, hz, Function.update_of_ne hi]
  rw [hrows]
  exact hf _

lemma exists_power {n : ℕ} (f : BoolFunc n)
    (hz : f (fun _ => false) = false)
    (hu : ∀ i, f (Function.update (fun _ => false) i true) = true) (k : ℕ) :
    ∃ g : BoolFunc (n^k), polyDegree g ≤ polyDegree f ^ k ∧
      g (fun _ => false) = false ∧ ∀ i, g (Function.update (fun _ => false) i true) = true := by
  induction k with
  | zero =>
    change ∃ g : BoolFunc 1, polyDegree g ≤ 1 ∧
      g (fun _ => false) = false ∧ ∀ i, g (Function.update (fun _ => false) i true) = true
    refine ⟨fun x => x 0, ?_, rfl, ?_⟩
    · apply Nat.find_min'
      refine ⟨X 0, ?_, ?_⟩
      · simp
      · intro x; simp
    · intro i
      have : i = 0 := Subsingleton.elim _ _
      subst i
      simp
  | succ k ih =>
    obtain ⟨g,hd,hz',hu'⟩ := ih
    exact ⟨compose g f, (compose_degree g f).trans (Nat.mul_le_mul_right _ hd),
      compose_zero g f hz' hz, compose_unit g f hz hu' hu⟩

lemma linear_lower (d k : ℕ) :
    d^(k+1)+(k+1)*d^k ≤ (d+1)^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := Nat.mul_le_mul_right (d+1) ih
    simp only [pow_succ] at h ⊢
    nlinarith only [h, Nat.zero_le ((k+1)*d^k)]

lemma remove_two (n d : ℕ) (h : ∀ k : ℕ, n^k ≤ 2*d^k) : n ≤ d := by
  by_contra hn
  have hnd : d+1 ≤ n := by omega
  by_cases hd : d = 0
  · have h1 := h 1
    simp [hd] at h1
    omega
  · have hpos : 0 < d^d := pow_pos (Nat.pos_of_ne_zero hd) _
    have hlow := linear_lower d d
    have hpow := Nat.pow_le_pow_left hnd (d+1)
    have hupper := h (d+1)
    simp only [pow_succ] at hlow hupper hpow
    nlinarith

/-- The normalized degree-squared bound follows from the uniform factor-two bound.
The latter remains an explicit hypothesis until its complete proof is replayed. -/
theorem normalized_sharpening
    (weak : ∀ {b : ℕ}, 1 ≤ b → ∀ g : BoolFunc b,
      g (fun _ => false) = false →
      (∀ i, g (Function.update (fun _ => false) i true) = true) →
      b ≤ 2 * polyDegree g ^ 2)
    {n : ℕ} (f : BoolFunc n) (hz : f (fun _ => false) = false)
    (hu : ∀ i, f (Function.update (fun _ => false) i true) = true) :
    n ≤ polyDegree f ^ 2 := by
  apply remove_two
  intro k
  obtain ⟨g,hd,hz',hu'⟩ := exists_power f hz hu k
  by_cases hn : n^k = 0
  · simp [hn]
  · have h := weak (Nat.one_le_iff_ne_zero.mpr hn) g hz' hu'
    calc n^k ≤ 2 * polyDegree g ^ 2 := h
      _ ≤ 2 * (polyDegree f ^ k)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd 2)
      _ = 2 * (polyDegree f ^ 2)^k := by rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
end
end DegreeAmplification

namespace DegreeAmplification
open MvPolynomial
lemma degree_compl {b : ℕ} (g : BoolFunc b) :
    polyDegree (fun y => !g y) ≤ polyDegree g := by
  classical
  obtain ⟨p,hp,he⟩ := Nat.find_spec (show ∃ d, HasPolyRep g d from ⟨b,hasPolyRep_card g⟩)
  apply Nat.find_min'
  refine ⟨1-p, ?_, ?_⟩
  · exact (totalDegree_sub _ _).trans (max_le (by simp) hp)
  · intro y
    rw [map_sub,map_one,he]
    cases h : g y <;> simp [h]

lemma block_zero {n b : ℕ} (x : Fin n → Bool) (e : Fin b → Finset (Fin n)) :
    BlockRestrictionReplay.blockFlipMulti_sol x e (fun _ => false) = x := by
  classical
  funext j
  simp [BlockRestrictionReplay.blockFlipMulti_sol]

lemma block_basis {n b : ℕ} (x : Fin n → Bool) (e : Fin b → Finset (Fin n)) (i : Fin b) :
    BlockRestrictionReplay.blockFlipMulti_sol x e (Function.update (fun _ => false) i true) = flipBlock x (e i) := by
  classical
  funext j
  have h : (∃ k, j ∈ e k ∧ Function.update (fun _ => false) i true k = true) ↔ j ∈ e i := by
    simp only [Function.update_apply]
    constructor
    · rintro ⟨k,hk,hv⟩
      by_cases hki : k=i
      · simpa [hki] using hk
      · simp [hki] at hv
    · intro hj; exact ⟨i,hj,by simp⟩
  simp only [BlockRestrictionReplay.blockFlipMulti_sol,flipBlock,h]

/-- Full exact platform conclusion, conditional only on the unreplayed normalized
factor-two bound. Block restriction is proved by the retained community source. -/
theorem bs_bound_of_weak
    (weak : ∀ {b : ℕ}, 1 ≤ b → ∀ g : BoolFunc b,
      g (fun _ => false) = false →
      (∀ i, g (Function.update (fun _ => false) i true) = true) →
      b ≤ 2 * polyDegree g ^ 2)
    {n : ℕ} (f : BoolFunc n) : blockSensitivity f ≤ polyDegree f ^ 2 := by
  classical
  unfold blockSensitivity
  rw [Finset.sup_le_iff]
  intro x hx
  unfold blockSensitivityAt
  rw [Finset.sup_le_iff]
  intro B hB
  have hh := (Finset.mem_filter.mp hB).2
  let e : Fin B.card → Finset (Fin n) := fun i => (B.equivFin.symm i).val
  have hem : ∀ i, e i ∈ B := fun i => (B.equivFin.symm i).property
  have hei : Function.Injective e := by
    intro i j hij
    apply B.equivFin.symm.injective
    exact Subtype.ext hij
  have hdis : ∀ i j, i ≠ j → Disjoint (e i) (e j) := by
    intro i j hij
    exact hh.2 (hem i) (hem j) (fun h => hij (hei h))
  let g : BoolFunc B.card := fun y => f (BlockRestrictionReplay.blockFlipMulti_sol x e y)
  have hg : polyDegree g ≤ polyDegree f := BlockRestrictionReplay.solution f x e hdis
  have hz : g (fun _ => false) = f x := by simp only [g,block_zero]
  have hu : ∀ i, g (Function.update (fun _ => false) i true) ≠ f x := by
    intro i
    simpa only [g,block_basis] using (hh.1 (e i) (hem i)).2
  cases hfx : f x
  · have hzero : g (fun _ => false) = false := hz.trans hfx
    have hunit : ∀ i, g (Function.update (fun _ => false) i true) = true := by
      intro i
      have h := hu i
      rw [hfx] at h
      cases hv : g (Function.update (fun _ => false) i true) <;> simp_all
    exact (normalized_sharpening weak g hzero hunit).trans (Nat.pow_le_pow_left hg 2)
  · have hzero : (fun y => !g y) (fun _ => false) = false := by simp [hz,hfx]
    have hunit : ∀ i, (fun y => !g y) (Function.update (fun _ => false) i true) = true := by
      intro i
      have h := hu i
      rw [hfx] at h
      cases hv : g (Function.update (fun _ => false) i true) <;> simp_all
    exact (normalized_sharpening weak (fun y => !g y) hzero hunit).trans
      (Nat.pow_le_pow_left ((degree_compl g).trans hg) 2)
end DegreeAmplification

end

theorem solution {n : Nat} (f : BoolFunc n) : blockSensitivity f <= polyDegree f ^ 2 := by
  exact DegreeAmplification.bs_bound_of_weak (fun hb g hz hu => polyDegree_distinguishing_units_bound hb g hz hu) f
