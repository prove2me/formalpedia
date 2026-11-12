-- Prove2me | solution 1 for DerivationHitting.Commutative.logarithm_order_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:36:17.740215+00:00
-- url     : https://prove2.me/submissions/b73566fe-59a0-4dab-a441-cd25a4a8bbf8

import Mathlib
import Definitions.Def_DerivationHitting_Commutative_DifferentialData
import Theorems.Thm_DerivationHitting_Commutative_evaluation_injective
import Theorems.Thm_DerivationHitting_Commutative_trivial_constants
import Theorems.Thm_DerivationHitting_Commutative_wronskian_degree_bound
import Theorems.Thm_DerivationHitting_Commutative_partial_space_finite_dimensional
import Theorems.Thm_OAI_NCHitting_hasOrderBasis_of_finrank_le
import Theorems.Thm_OAI_NCHitting_wronskian_order_sum
import Theorems.Thm_OAI_NCHitting_order_le_wronskian_add

section
open scoped RatFunc LaurentSeries
open DerivationHitting.Commutative

namespace DerivationHitting.Dev.Common
noncomputable section

variable {F : Type*} [Field F]

lemma bdd_dL (z : LaurentSeries F) :
    BddBelow (Function.support (fun n : ℤ => ((n + 1 : ℤ) : F) * z.coeff (n + 1))) := by
  by_cases hz : z = 0
  · subst hz; simp
  refine ⟨z.order - 1, fun n hn => ?_⟩
  have h1 : z.coeff (n + 1) ≠ 0 := fun h0 => hn (by simp [h0])
  have := HahnSeries.order_le_of_coeff_ne_zero h1
  omega

/-- Formal derivative on Laurent series. -/
def dL (z : LaurentSeries F) : LaurentSeries F :=
  HahnSeries.ofSuppBddBelow (fun n : ℤ => ((n + 1 : ℤ) : F) * z.coeff (n + 1)) (bdd_dL z)

theorem coeff_dL (z : LaurentSeries F) (n : ℤ) :
    (dL z).coeff n = ((n + 1 : ℤ) : F) * z.coeff (n + 1) := rfl

theorem dL_add (z w : LaurentSeries F) : dL (z + w) = dL z + dL w := by
  ext n; simp [coeff_dL, mul_add]

theorem dL_zero : dL (0 : LaurentSeries F) = 0 := by
  ext n; simp [coeff_dL]

lemma coeff_ofPS (p : PowerSeries F) (k : ℤ) :
    ((p : PowerSeries F) : LaurentSeries F).coeff k = if k < 0 then 0 else PowerSeries.coeff k.natAbs p :=
  PowerSeries.coeff_coe p k

theorem dL_single_mul (m : ℤ) (p : PowerSeries F) :
    dL (HahnSeries.single m (1 : F) * (p : LaurentSeries F)) =
      HahnSeries.C (m : F) * HahnSeries.single (m - 1) (1 : F) * (p : LaurentSeries F)
        + HahnSeries.single m (1 : F) * ((PowerSeries.derivative F p : PowerSeries F) : LaurentSeries F) := by
  ext n
  rw [coeff_dL, HahnSeries.coeff_add, mul_assoc, HahnSeries.C_mul_eq_smul,
    HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul,
    HahnSeries.coeff_smul, HahnSeries.coeff_single_mul]
  have e : n - (m - 1) = n + 1 - m := by ring
  rw [e]
  simp only [one_mul, smul_eq_mul]
  by_cases h : n + 1 - m < 0
  · have h' : n - m < 0 := by omega
    simp [coeff_ofPS, h, h']
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ n + 1 - m by omega)
    rcases k with _ | k
    · have h1 : n + 1 - m = ((0 : ℕ) : ℤ) := hk
      have h2 : n - m < 0 := by omega
      have h3 : (n : ℤ) + 1 = m := by omega
      rw [h1, coeff_ofPS, coeff_ofPS _ (n - m), if_pos h2, if_neg (by omega)]
      simp [← h3]
    · have h1 : n + 1 - m = ((k + 1 : ℕ) : ℤ) := hk
      have h2 : n - m = (k : ℤ) := by omega
      have h3 : (n : ℤ) = m + k := by omega
      rw [h1, h2, coeff_ofPS, coeff_ofPS, if_neg (by omega), if_neg (by omega), h3]
      simp only [Int.natAbs_natCast, PowerSeries.coeff_derivative]
      push_cast
      ring

lemma single_add_one (a b : ℤ) :
    HahnSeries.single (a + b - 1) (1 : F) =
      HahnSeries.single (a - 1) (1 : F) * HahnSeries.single b (1 : F) := by
  rw [HahnSeries.single_mul_single, one_mul, show a - 1 + b = a + b - 1 by ring]

lemma dL_mul_aux (a b : ℤ) (P Q : PowerSeries F) :
    dL ((HahnSeries.single a (1 : F) * (P : LaurentSeries F)) *
        (HahnSeries.single b (1 : F) * (Q : LaurentSeries F))) =
      dL (HahnSeries.single a (1 : F) * (P : LaurentSeries F)) *
          (HahnSeries.single b (1 : F) * (Q : LaurentSeries F)) +
        (HahnSeries.single a (1 : F) * (P : LaurentSeries F)) *
          dL (HahnSeries.single b (1 : F) * (Q : LaurentSeries F)) := by
  have hs : ∀ x y : ℤ, HahnSeries.single x (1 : F) * HahnSeries.single y (1 : F) =
      HahnSeries.single (x + y) (1 : F) := fun x y => by
    rw [HahnSeries.single_mul_single, one_mul]
  have e : (HahnSeries.single a (1 : F) * (P : LaurentSeries F)) *
        (HahnSeries.single b (1 : F) * (Q : LaurentSeries F)) =
      HahnSeries.single (a + b) (1 : F) * ((P * Q : PowerSeries F) : LaurentSeries F) := by
    rw [← hs, PowerSeries.coe_mul]; ring
  rw [e, dL_single_mul, dL_single_mul, dL_single_mul, Derivation.leibniz]
  have h1 := single_add_one (F := F) a b
  have h2 : HahnSeries.single (a + b - 1) (1 : F) =
      HahnSeries.single a (1 : F) * HahnSeries.single (b - 1) (1 : F) := by
    rw [hs, show a + (b - 1) = a + b - 1 by ring]
  have h3 : (HahnSeries.C ((a + b : ℤ) : F) : LaurentSeries F) = HahnSeries.C (a : F) + HahnSeries.C (b : F) := by
    rw [Int.cast_add, map_add]
  have h4 : ((P • (PowerSeries.derivative F) Q + Q • (PowerSeries.derivative F) P : PowerSeries F) :
      LaurentSeries F) = (P : LaurentSeries F) * ((PowerSeries.derivative F Q : PowerSeries F) : LaurentSeries F)
      + (Q : LaurentSeries F) * ((PowerSeries.derivative F P : PowerSeries F) : LaurentSeries F) := by
    simp [PowerSeries.coe_add, PowerSeries.coe_mul]
  rw [h4, h3]
  rw [← hs a b, PowerSeries.coe_mul]
  linear_combination ((HahnSeries.C (a : F) : LaurentSeries F) * (P : LaurentSeries F) * (Q : LaurentSeries F)) * h1
    + ((HahnSeries.C (b : F) : LaurentSeries F) * (P : LaurentSeries F) * (Q : LaurentSeries F)) * h2

theorem dL_mul (z w : LaurentSeries F) : dL (z * w) = dL z * w + z * dL w := by
  conv_lhs => rw [← z.single_order_mul_powerSeriesPart, ← w.single_order_mul_powerSeriesPart]
  rw [dL_mul_aux]
  rw [z.single_order_mul_powerSeriesPart, w.single_order_mul_powerSeriesPart]

theorem dL_algebraMap_powerSeries (p : PowerSeries F) :
    dL (algebraMap (PowerSeries F) (LaurentSeries F) p) =
      algebraMap (PowerSeries F) (LaurentSeries F) (PowerSeries.derivative F p) := by
  have h := dL_single_mul (0 : ℤ) p
  simp only [HahnSeries.single_zero_one, Int.cast_zero, map_zero, zero_mul, one_mul, zero_add] at h
  exact h

lemma algebraMap_poly (P : Polynomial F) :
    algebraMap (RatFunc F) (LaurentSeries F) (algebraMap (Polynomial F) (RatFunc F) P) =
      algebraMap (PowerSeries F) (LaurentSeries F) (P : PowerSeries F) := by
  have := RatFunc.coe_coe (F := F) P
  simpa using this.symm

lemma dL_poly (P : Polynomial F) :
    dL (algebraMap (RatFunc F) (LaurentSeries F) (algebraMap (Polynomial F) (RatFunc F) P)) =
      algebraMap (RatFunc F) (LaurentSeries F)
        (algebraMap (Polynomial F) (RatFunc F) (Polynomial.derivative P)) := by
  rw [algebraMap_poly, algebraMap_poly, dL_algebraMap_powerSeries, PowerSeries.derivative_coe]

theorem dL_algebraMap_ratFunc (a : RatFunc F) :
    dL (algebraMap (RatFunc F) (LaurentSeries F) a) =
      algebraMap (RatFunc F) (LaurentSeries F) (rationalDerivative a) := by
  set N := algebraMap (RatFunc F) (LaurentSeries F) (algebraMap (Polynomial F) (RatFunc F) a.num)
  set D := algebraMap (RatFunc F) (LaurentSeries F) (algebraMap (Polynomial F) (RatFunc F) a.denom)
  have hD : D ≠ 0 := by
    simp only [D]
    exact (map_ne_zero_iff _ (algebraMap (RatFunc F) (LaurentSeries F)).injective).2
      (by simpa using a.denom_ne_zero)
  have ha : algebraMap (RatFunc F) (LaurentSeries F) a = N / D := by
    simp only [N, D, ← map_div₀, RatFunc.num_div_denom]
  have hN := dL_poly a.num
  have hD' := dL_poly a.denom
  have key : dL (N / D) * D = dL N - N / D * dL D := by
    have := dL_mul (N / D) D
    rw [div_mul_cancel₀ _ hD] at this
    rw [this]; ring
  unfold rationalDerivative
  rw [ha]
  simp only [map_div₀, map_sub, map_mul, map_pow]
  rw [← hN, ← hD'] 
  change dL (N / D) = (dL N * D - N * dL D) / D ^ 2
  rw [eq_div_iff (pow_ne_zero 2 hD), show dL (N / D) * D ^ 2 = (dL (N / D) * D) * D by ring, key]
  field_simp

lemma rd_zero : rationalDerivative (0 : RatFunc F) = 0 := by
  have h := dL_algebraMap_ratFunc (0 : RatFunc F)
  rw [map_zero, dL_zero] at h
  exact (algebraMap (RatFunc F) (LaurentSeries F)).injective (by rw [← h, map_zero])

lemma rd_add (a b : RatFunc F) :
    rationalDerivative (a + b) = rationalDerivative a + rationalDerivative b := by
  apply (algebraMap (RatFunc F) (LaurentSeries F)).injective
  rw [← dL_algebraMap_ratFunc, map_add, dL_add, map_add, dL_algebraMap_ratFunc,
    dL_algebraMap_ratFunc]

variable {n : ℕ}

lemma coeff_timeDerivative (h : MvPolynomial (Fin n) (RatFunc F)) (m : Fin n →₀ ℕ) :
    MvPolynomial.coeff m (timeDerivative h) = rationalDerivative (MvPolynomial.coeff m h) := by
  classical
  unfold timeDerivative
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hm : m ∈ h.support
  · rw [Finset.sum_eq_single m]
    · simp
    · intro x _ hx; simp [hx]
    · intro hx; exact absurd hm hx
  · have : MvPolynomial.coeff m h = 0 := by simpa using hm
    rw [this, rd_zero]
    apply Finset.sum_eq_zero
    intro x hx
    have : x ≠ m := fun e => hm (e ▸ hx)
    simp [this]

lemma timeDerivative_add (p q : MvPolynomial (Fin n) (RatFunc F)) :
    timeDerivative (p + q) = timeDerivative p + timeDerivative q := by
  ext m; simp [coeff_timeDerivative, rd_add]

lemma timeDerivative_C (a : RatFunc F) :
    timeDerivative (MvPolynomial.C a : MvPolynomial (Fin n) (RatFunc F)) =
      MvPolynomial.C (rationalDerivative a) := by
  classical
  ext m
  rw [coeff_timeDerivative, MvPolynomial.coeff_C, MvPolynomial.coeff_C]
  split_ifs <;> simp [rd_zero]

lemma timeDerivative_mul_X (h : MvPolynomial (Fin n) (RatFunc F)) (j : Fin n) :
    timeDerivative (h * MvPolynomial.X j) = timeDerivative h * MvPolynomial.X j := by
  classical
  ext m
  rw [coeff_timeDerivative, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X',
    coeff_timeDerivative]
  split_ifs <;> simp [rd_zero]

lemma linearDerivation_add (b : Fin n → RatFunc F) (p q : MvPolynomial (Fin n) (RatFunc F)) :
    linearDerivation b (p + q) = linearDerivation b p + linearDerivation b q := by
  unfold linearDerivation
  simp only [timeDerivative_add, map_add, mul_add, Finset.sum_add_distrib]
  abel

lemma linearDerivation_C (b : Fin n → RatFunc F) (a : RatFunc F) :
    linearDerivation b (MvPolynomial.C a : MvPolynomial (Fin n) (RatFunc F)) =
      MvPolynomial.C (rationalDerivative a) := by
  simp [linearDerivation, timeDerivative_C]

lemma linearDerivation_mul_X (b : Fin n → RatFunc F) (h : MvPolynomial (Fin n) (RatFunc F))
    (j : Fin n) :
    linearDerivation b (h * MvPolynomial.X j) =
      linearDerivation b h * MvPolynomial.X j + h * MvPolynomial.C (b j) := by
  classical
  unfold linearDerivation
  simp only [timeDerivative_mul_X, Derivation.leibniz, smul_eq_mul,
    mul_add, Finset.sum_add_distrib, add_mul, Finset.sum_mul]
  have : ∀ i : Fin n, MvPolynomial.C (b i) * (h * MvPolynomial.pderiv i (MvPolynomial.X j))
      = if i = j then h * MvPolynomial.C (b j) else 0 := by
    intro i
    by_cases hij : i = j
    · subst hij; simp [MvPolynomial.pderiv_X_self]; ring
    · simp [hij, MvPolynomial.pderiv_X_of_ne (Ne.symm hij)]
  simp_rw [this]
  rw [Finset.sum_ite_eq' Finset.univ j, if_pos (Finset.mem_univ j)]
  have h2 : ∑ x : Fin n, MvPolynomial.C (b x) * (MvPolynomial.X j * (MvPolynomial.pderiv x) h) =
      ∑ i : Fin n, MvPolynomial.C (b i) * (MvPolynomial.pderiv i) h * MvPolynomial.X j :=
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [h2]; ring

theorem eval_linearDerivation {n : ℕ} (b : Fin n → RatFunc F) (P : Fin n → PowerSeries F)
    (hbP : arePrimitives b P) (h : MvPolynomial (Fin n) (RatFunc F)) :
    associatedEvaluation P (linearDerivation b h) = dL (associatedEvaluation P h) := by
  induction h using MvPolynomial.induction_on with
  | C a =>
    rw [linearDerivation_C]
    simp [associatedEvaluation, dL_algebraMap_ratFunc]
  | add p q hp hq =>
    rw [linearDerivation_add, map_add, map_add, hp, hq, dL_add]
  | mul_X p j hp =>
    rw [linearDerivation_mul_X, map_add, map_mul, map_mul, map_mul, hp, dL_mul]
    have e : associatedEvaluation P (MvPolynomial.X j) =
        algebraMap (PowerSeries F) (LaurentSeries F) (P j) := by simp [associatedEvaluation]
    have e2 : associatedEvaluation P (MvPolynomial.C (b j)) =
        algebraMap (RatFunc F) (LaurentSeries F) (b j) := by simp [associatedEvaluation]
    rw [e, e2, dL_algebraMap_powerSeries, hbP j]

theorem eval_linearDerivation_iterate {n : ℕ} (b : Fin n → RatFunc F) (P : Fin n → PowerSeries F)
    (hbP : arePrimitives b P) (m : ℕ) (h : MvPolynomial (Fin n) (RatFunc F)) :
    associatedEvaluation P ((linearDerivation b)^[m] h) = dL^[m] (associatedEvaluation P h) := by
  induction m generalizing h with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, eval_linearDerivation b P hbP]


end
end DerivationHitting.Dev.Common
end

section
open scoped RatFunc LaurentSeries
open DerivationHitting.Commutative DerivationHitting.Dev.Common

namespace DerivationHitting.Dev.Order
noncomputable section

variable {F : Type*} [Field F]

lemma coeff_deriv_log [CharZero F] {n : ℕ} (i : Fin n) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.derivative F (formalLogarithm i)) =
      (-1 : F) ^ k * ((i.val + 1 : ℕ) : F) ^ (k + 1) := by
  rw [PowerSeries.coeff_derivative]
  simp only [formalLogarithm, PowerSeries.coeff_mk, logarithmCoefficient]
  have h : ((k : F) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [if_neg (Nat.succ_ne_zero k)]
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp

lemma deriv_log_mul [CharZero F] {n : ℕ} (i : Fin n) :
    PowerSeries.derivative F (formalLogarithm i) *
      (1 + PowerSeries.C (((i.val + 1 : ℕ) : F)) * PowerSeries.X) =
      PowerSeries.C (((i.val + 1 : ℕ) : F)) := by
  ext k
  rw [mul_add, mul_one, map_add]
  rcases k with _ | k
  · simp [coeff_deriv_log]
  · rw [← mul_assoc, mul_comm _ (PowerSeries.C _), mul_assoc, mul_comm _ PowerSeries.X,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, coeff_deriv_log, coeff_deriv_log,
      PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero k)]
    simp [pow_succ]
    ring

lemma primitives [CharZero F] {n : ℕ} :
    arePrimitives (F := F) (n := n) logarithmKernel formalLogarithm := by
  intro i
  set c : F := ((i.val + 1 : ℕ) : F) with hc
  have hk : logarithmKernel i = algebraMap (Polynomial F) (RatFunc F) (Polynomial.C c) /
      algebraMap (Polynomial F) (RatFunc F) (1 + Polynomial.C c * Polynomial.X) := by
    simp [logarithmKernel, ← hc]
  have hne : ((1 + Polynomial.C c * Polynomial.X : Polynomial F) : PowerSeries F) ≠ 0 := by
    intro h
    have := congrArg (PowerSeries.coeff 0) h
    simp at this
  rw [hk, map_div₀, algebraMap_poly, algebraMap_poly]
  have hne' : algebraMap (PowerSeries F) (LaurentSeries F)
      ((1 + Polynomial.C c * Polynomial.X : Polynomial F) : PowerSeries F) ≠ 0 :=
    (map_ne_zero_iff _ (HahnSeries.ofPowerSeries_injective)).2 hne
  rw [eq_div_iff hne', ← map_mul]
  congr 1
  have := deriv_log_mul (F := F) i
  rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_one]
  exact this

lemma eval_rat {n : ℕ} (h : MvPolynomial (Fin n) F) :
    associatedEvaluation (formalLogarithm (F := F) (n := n)) (rationalPolynomial h) =
      algebraMap (PowerSeries F) (LaurentSeries F) (logarithmSubstitution n h) := by
  induction h using MvPolynomial.induction_on with
  | C a =>
    simp only [rationalPolynomial, logarithmSubstitution, associatedEvaluation, MvPolynomial.map_C,
      MvPolynomial.eval₂Hom_C, MvPolynomial.aeval_C]
    rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, algebraMap_poly, Polynomial.coe_C]
    rfl
  | add p q hp hq =>
    simp only [rationalPolynomial, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p j hp =>
    simp only [rationalPolynomial, map_mul, MvPolynomial.map_X] at hp ⊢
    rw [hp]
    simp [associatedEvaluation, logarithmSubstitution]

lemma logSub_injective [CharZero F] {n : ℕ} :
    Function.Injective (logarithmSubstitution (F := F) n) := by
  intro h1 h2 e
  have hP := evaluation_injective (n := n) (F := F) logarithmKernel formalLogarithm primitives
    (trivial_constants n)
  have h3 : associatedEvaluation (formalLogarithm (F := F) (n := n)) (rationalPolynomial h1) =
      associatedEvaluation formalLogarithm (rationalPolynomial h2) := by
    rw [eval_rat, eval_rat, e]
  exact MvPolynomial.map_injective _ (algebraMap F (RatFunc F)).injective (hP h3)

lemma derivativeIter_eq (m : ℕ) (f : PowerSeries F) :
    OAI.NCHitting.derivativeIter m f = (PowerSeries.derivative F)^[m] f := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', OAI.NCHitting.derivativeIter, ih]

lemma dL_iter_alg (m : ℕ) (p : PowerSeries F) :
    dL^[m] (algebraMap (PowerSeries F) (LaurentSeries F) p) =
      algebraMap (PowerSeries F) (LaurentSeries F) ((PowerSeries.derivative F)^[m] p) := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dL_algebraMap_powerSeries, ih]

lemma alg_wronskian [CharZero F] {n q : ℕ} (g : Fin q → MvPolynomial (Fin n) F) :
    algebraMap (PowerSeries F) (LaurentSeries F)
        (OAI.NCHitting.wronskian (fun j => logarithmSubstitution n (g j))) =
      associatedEvaluation formalLogarithm (derivationWronskian logarithmKernel g) := by
  have h1 := RingHom.map_det (algebraMap (PowerSeries F) (LaurentSeries F))
    (OAI.NCHitting.wronskianMatrix (fun j => logarithmSubstitution n (g j)))
  have h2 := RingHom.map_det (associatedEvaluation (F := F) (formalLogarithm (n := n)))
    (Matrix.of fun (m j : Fin q) =>
      (linearDerivation logarithmKernel)^[m.val] (rationalPolynomial (g j)))
  unfold OAI.NCHitting.wronskian derivationWronskian
  refine Eq.trans h1 (Eq.trans ?_ h2.symm)
  congr 1
  ext m j : 2
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, OAI.NCHitting.wronskianMatrix, Matrix.of_apply]
  rw [eval_linearDerivation_iterate _ _ primitives, eval_rat, dL_iter_alg, derivativeIter_eq]

lemma dI_sum {k : ℕ} (m : ℕ) (c : Fin k → F) (b : Fin k → PowerSeries F) :
    OAI.NCHitting.derivativeIter m (∑ l, c l • b l) =
      ∑ l, c l • OAI.NCHitting.derivativeIter m (b l) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [OAI.NCHitting.derivativeIter]
    rw [ih, map_sum]
    simp [map_smul]

lemma wronskian_ne_zero [CharZero F] {q : ℕ} (ψ : Fin q → PowerSeries F)
    (hli : LinearIndependent F ψ) : OAI.NCHitting.wronskian ψ ≠ 0 := by
  classical
  set W := Submodule.span F (Set.range ψ) with hWdef
  haveI : FiniteDimensional F W := FiniteDimensional.span_of_finite F (Set.finite_range ψ)
  have hfr : Module.finrank F W = q := by rw [finrank_span_eq_card hli]; simp
  obtain ⟨k, b, a, hbli, hbspan, ha, hb, hz⟩ :=
    OAI.NCHitting.hasOrderBasis_of_finrank_le q W hfr.le
  have hk : k = q := by
    have := finrank_span_eq_card hbli
    rw [hbspan, hfr] at this
    simpa using this.symm
  subst hk
  obtain ⟨hw, _⟩ := OAI.NCHitting.wronskian_order_sum b a ha hb hz
  have hmem : ∀ j, ∃ c : Fin k → F, ∑ l, c l • b l = ψ j := fun j => by
    have : ψ j ∈ Submodule.span F (Set.range b) := by
      rw [hbspan]; exact Submodule.subset_span ⟨j, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun F).1 this
  choose C hC using hmem
  let M : Matrix (Fin k) (Fin k) F := Matrix.of C
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hv
    rw [Fintype.linearIndependent_iff] at hli
    funext j
    refine hli v ?_ j
    have e : ∑ j, v j • ψ j = ∑ l, (∑ j, v j * M j l) • b l := by
      simp_rw [← hC, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
      rfl
    rw [e]
    have : ∀ l, ∑ j, v j * M j l = 0 := fun l => by
      have := congrFun hvM l
      simpa [Matrix.vecMul, dotProduct] using this
    simp [this]
  have hmat : OAI.NCHitting.wronskianMatrix ψ =
      OAI.NCHitting.wronskianMatrix b * (M.map (algebraMap F (PowerSeries F))).transpose := by
    refine Matrix.ext fun m j => ?_
    simp only [OAI.NCHitting.wronskianMatrix, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply]
    rw [← hC j, dI_sum]
    exact Finset.sum_congr rfl (fun l _ => by rw [Algebra.smul_def, mul_comm]; rfl)
  unfold OAI.NCHitting.wronskian
  have e : (M.map (algebraMap F (PowerSeries F))).det = algebraMap F (PowerSeries F) M.det :=
    (RingHom.map_det _ M).symm
  rw [hmat, Matrix.det_mul, Matrix.det_transpose, e]
  refine mul_ne_zero hw ?_
  exact (map_ne_zero_iff _ (algebraMap F (PowerSeries F)).injective).2 hdet

lemma pderiv_mem_partialSpace {n : ℕ} (f : MvPolynomial (Fin n) F) (i : Fin n)
    {h : MvPolynomial (Fin n) F} (hh : h ∈ partialSpace f) :
    MvPolynomial.pderiv i h ∈ partialSpace f := by
  unfold partialSpace at *
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨w ++ [i], by simp [iteratedPartial, List.foldl_append]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [Derivation.map_smul]; exact Submodule.smul_mem _ _ hx

lemma order_le_natDegree (W : PowerSeries F) (hW : W ≠ 0) (A C : Polynomial F) (hC : C ≠ 0)
    (h : algebraMap (PowerSeries F) (LaurentSeries F) W =
      algebraMap (RatFunc F) (LaurentSeries F)
        (algebraMap (Polynomial F) (RatFunc F) A / algebraMap (Polynomial F) (RatFunc F) C)) :
    W.order.toNat ≤ A.natDegree := by
  have hC' : algebraMap (RatFunc F) (LaurentSeries F) (algebraMap (Polynomial F) (RatFunc F) C) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (RatFunc F) (LaurentSeries F)).injective).2
      (RatFunc.algebraMap_ne_zero hC)
  have e : algebraMap (PowerSeries F) (LaurentSeries F) (W * (C : PowerSeries F)) =
      algebraMap (PowerSeries F) (LaurentSeries F) (A : PowerSeries F) := by
    rw [map_mul, ← algebraMap_poly C, ← algebraMap_poly A, h, map_div₀]
    exact div_mul_cancel₀ _ hC'
  have e' : W * (C : PowerSeries F) = (A : PowerSeries F) :=
    (HahnSeries.ofPowerSeries_injective) e
  have hCne : (C : PowerSeries F) ≠ 0 := by
    intro h0
    exact hC (by exact_mod_cast h0)
  have hA : (A : PowerSeries F) ≠ 0 := by rw [← e']; exact mul_ne_zero hW hCne
  have hA' : A ≠ 0 := fun h0 => hA (by rw [h0]; simp)
  have h1 : (A : PowerSeries F).order ≤ (A.natDegree : ℕ∞) := by
    apply PowerSeries.order_le
    rw [Polynomial.coeff_coe]
    exact Polynomial.leadingCoeff_ne_zero.2 hA'
  rw [← e', PowerSeries.order_mul] at h1
  have h2 : W.order ≤ (A.natDegree : ℕ∞) := le_trans le_self_add h1
  exact ENat.toNat_le_of_le_coe h2

end
end DerivationHitting.Dev.Order

namespace DerivationHitting.Commutative
open DerivationHitting.Dev.Order DerivationHitting.Dev.Common
theorem chk_logarithm_order_bound {F : Type*} [Field F] [CharZero F] {n : ℕ}
    (r : ℕ) (f : MvPolynomial (Fin n) F) (hf : f ≠ 0)
    (hr : hasBoundedPartials f r) :
    ∃ k : ℕ, k < cutoff n r ∧
      PowerSeries.coeff k (logarithmSubstitution n f) ≠ 0 := by
  classical
  obtain ⟨-, hfd⟩ := partial_space_finite_dimensional f
  haveI := hfd
  have hq : Module.finrank F (partialSpace f) ≤ r := by
    have h := hr
    unfold hasBoundedPartials at h
    rw [← Module.finrank_eq_rank] at h
    exact_mod_cast h
  set V := partialSpace f with hV
  set q := Module.finrank F V with hqdef
  let bs : Module.Basis (Fin q) F V := Module.finBasis F V
  let g : Fin q → MvPolynomial (Fin n) F := fun j => (bs j : MvPolynomial (Fin n) F)
  have hli : LinearIndependent F g :=
    bs.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hspan : Submodule.span F (Set.range g) = V := by
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨j, rfl⟩; exact (bs j).2
    · intro v hv
      have h1 : (⟨v, hv⟩ : V) ∈ Submodule.span F (Set.range bs) := by
        rw [bs.span_eq]; trivial
      have := Submodule.mem_map_of_mem (f := V.subtype) h1
      rw [Submodule.map_span, ← Set.range_comp] at this
      exact this
  have hclosed : derivativeClosed g := fun i j => by
    rw [hspan]; exact pderiv_mem_partialSpace f i (bs j).2
  have hfV : f ∈ V := Submodule.subset_span ⟨[], rfl⟩
  let ψ : Fin q → PowerSeries F := fun j => logarithmSubstitution n (g j)
  let φ : MvPolynomial (Fin n) F →ₗ[F] PowerSeries F := (logarithmSubstitution n).toLinearMap
  have hφ : LinearMap.ker φ = ⊥ := LinearMap.ker_eq_bot.2 logSub_injective
  have hψli : LinearIndependent F ψ := hli.map' φ hφ
  have hy : logarithmSubstitution n f ≠ 0 := fun h0 =>
    hf (logSub_injective (by rw [h0, map_zero]))
  have hyspan : logarithmSubstitution n f ∈ Submodule.span F (Set.range ψ) := by
    have h1 : f ∈ Submodule.span F (Set.range g) := by rw [hspan]; exact hfV
    have := Submodule.mem_map_of_mem (f := φ) h1
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact this
  have hqpos : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · exfalso
      haveI : IsEmpty (Fin q) := by rw [h0]; infer_instance
      rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hyspan
      exact hy hyspan
    · exact h0
  have hW := wronskian_ne_zero ψ hψli
  obtain ⟨A, C, hC, hA, -, hAC⟩ := wronskian_degree_bound g hclosed
  have hrel := alg_wronskian g
  rw [hAC] at hrel
  have hrel' : algebraMap (PowerSeries F) (LaurentSeries F) (OAI.NCHitting.wronskian ψ) =
      algebraMap (RatFunc F) (LaurentSeries F)
        (algebraMap (Polynomial F) (RatFunc F) A / algebraMap (Polynomial F) (RatFunc F) C) := by
    rw [hrel]
    simp [associatedEvaluation]
  have hord := order_le_natDegree _ hW A C hC hrel'
  have hb := OAI.NCHitting.order_le_wronskian_add ψ hW _ hy hyspan
  refine ⟨(logarithmSubstitution n f).order.toNat, ?_, PowerSeries.coeff_order hy⟩
  have hqq : q ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hq 2
  have : n * q ^ 2 ≤ n * r ^ 2 := Nat.mul_le_mul_left n hqq
  unfold cutoff
  omega
end DerivationHitting.Commutative
end

theorem solution : type_of% @DerivationHitting.Commutative.chk_logarithm_order_bound := @DerivationHitting.Commutative.chk_logarithm_order_bound
