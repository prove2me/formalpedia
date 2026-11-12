-- Prove2me | solution 1 for DerivationHitting.Commutative.evaluation_injective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:36:13.497501+00:00
-- url     : https://prove2.me/submissions/4b5e4bbe-6284-4778-a1ed-fe2df0000ae3

import Mathlib
import Definitions.Def_DerivationHitting_Commutative_DifferentialData

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

theorem dL_one : dL (1 : LaurentSeries F) = 0 := by
  have := dL_algebraMap_powerSeries (1 : PowerSeries F)
  simpa using this

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


end
end DerivationHitting.Dev.Common
end

section
open scoped RatFunc LaurentSeries
open DerivationHitting.Commutative DerivationHitting.Dev.Common

namespace DerivationHitting.Dev.Inj
noncomputable section

variable {F : Type*} [Field F] {n : ℕ}

lemma rd_one : rationalDerivative (1 : RatFunc F) = 0 := by
  have h := dL_algebraMap_ratFunc (1 : RatFunc F)
  rw [map_one, dL_one] at h
  exact (algebraMap (RatFunc F) (LaurentSeries F)).injective (by rw [← h, map_zero])

/-- degree of an exponent. -/
def dg (m : Fin n →₀ ℕ) : ℕ := m.sum fun _ e => e

lemma dg_add_single (m : Fin n →₀ ℕ) (i : Fin n) : dg (m + Finsupp.single i 1) = dg m + 1 := by
  unfold dg
  rw [Finsupp.sum_add_index' (by simp) (by intros; rfl)]
  simp

lemma coeff_linearDerivation (b : Fin n → RatFunc F) (h : MvPolynomial (Fin n) (RatFunc F))
    (m : Fin n →₀ ℕ) :
    MvPolynomial.coeff m (linearDerivation b h) =
      rationalDerivative (MvPolynomial.coeff m h) +
        ∑ i, b i * (MvPolynomial.coeff (m + Finsupp.single i 1) h * ((m i : RatFunc F) + 1)) := by
  unfold linearDerivation
  rw [MvPolynomial.coeff_add, coeff_timeDerivative, MvPolynomial.coeff_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_pderiv]

lemma coeff_zero_of_dg (h : MvPolynomial (Fin n) (RatFunc F)) (m : Fin n →₀ ℕ)
    (hm : h.totalDegree < dg m) : MvPolynomial.coeff m h = 0 :=
  MvPolynomial.coeff_eq_zero_of_totalDegree_lt hm

lemma coeff_D_top (b : Fin n → RatFunc F) (h : MvPolynomial (Fin n) (RatFunc F)) (d : ℕ)
    (hd : h.totalDegree ≤ d) (m : Fin n →₀ ℕ) (hm : d ≤ dg m) :
    MvPolynomial.coeff m (linearDerivation b h) = rationalDerivative (MvPolynomial.coeff m h) := by
  rw [coeff_linearDerivation]
  have : ∀ i, MvPolynomial.coeff (m + Finsupp.single i 1) h = 0 := fun i =>
    coeff_zero_of_dg h _ (by rw [dg_add_single]; omega)
  simp [this]

theorem key {K : Type*} [Field K] [CharZero K] (b : Fin n → RatFunc K) (P : Fin n → PowerSeries K)
    (hP : arePrimitives b P) (hD : hasTrivialConstants b) :
    ∀ d k : ℕ, ∀ h : MvPolynomial (Fin n) (RatFunc K), associatedEvaluation P h = 0 → h ≠ 0 →
      h.totalDegree = d → (h.support.filter fun m => dg m = d).card = k → False := by
  classical
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro h hΦ hne hdeg hk
  -- a top monomial
  have hsne : h.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.2 (fun h0 => hne (MvPolynomial.support_eq_empty.1 h0))
  obtain ⟨m0, hm0, hsup⟩ := Finset.exists_mem_eq_sup h.support hsne (fun s => s.sum fun _ e => e)
  have hdm0 : dg m0 = d := by rw [← hdeg]; exact hsup.symm
  have ha : MvPolynomial.coeff m0 h ≠ 0 := MvPolynomial.mem_support_iff.1 hm0
  set a := MvPolynomial.coeff m0 h with ha_def
  set g : MvPolynomial (Fin n) (RatFunc K) := MvPolynomial.C a⁻¹ * h with hg_def
  have hgc : ∀ m, MvPolynomial.coeff m g = a⁻¹ * MvPolynomial.coeff m h := fun m =>
    MvPolynomial.coeff_C_mul _ _ _
  have hgs : g.support = h.support := by
    ext m
    simp [MvPolynomial.mem_support_iff, hgc, ha]
  have hgdeg : g.totalDegree = d := by
    rw [← hdeg]; unfold MvPolynomial.totalDegree; rw [hgs]
  have hg1 : MvPolynomial.coeff m0 g = 1 := by rw [hgc, ← ha_def]; exact inv_mul_cancel₀ ha
  have hgΦ : associatedEvaluation P g = 0 := by rw [hg_def, map_mul, hΦ, mul_zero]
  have hetop : ∀ m, d ≤ dg m → MvPolynomial.coeff m (linearDerivation b g) =
      rationalDerivative (MvPolynomial.coeff m g) := fun m hm => coeff_D_top b g d hgdeg.le m hm
  have hΦe : associatedEvaluation P (linearDerivation b g) = 0 := by
    rw [eval_linearDerivation b P hP, hgΦ, dL_zero]
  have hedeg : (linearDerivation b g).totalDegree ≤ d := by
    unfold MvPolynomial.totalDegree
    rw [Finset.sup_le_iff]
    intro m hm
    by_contra hlt
    have hlt' : d < dg m := by simpa [dg] using hlt
    have h1 := hetop m hlt'.le
    have h2 : MvPolynomial.coeff m g = 0 := coeff_zero_of_dg g m (by omega)
    rw [h2, rd_zero] at h1
    exact (MvPolynomial.mem_support_iff.1 hm) h1
  by_cases he0 : linearDerivation b g = 0
  · obtain ⟨c, hc⟩ := (hD g).1 he0
    have hc0 : algebraMap K (RatFunc K) c = 0 := by
      have := hgΦ
      rw [hc] at this
      have h3 : algebraMap (RatFunc K) (LaurentSeries K) (algebraMap K (RatFunc K) c) = 0 := by
        simpa [associatedEvaluation] using this
      exact (algebraMap (RatFunc K) (LaurentSeries K)).injective (by rw [h3, map_zero])
    rw [hc0, map_zero] at hc
    rw [hc] at hg1
    simp at hg1
  · by_cases hlt : (linearDerivation b g).totalDegree < d
    · exact ihd _ hlt _ _ hΦe he0 rfl rfl
    · have heq : (linearDerivation b g).totalDegree = d := le_antisymm hedeg (not_lt.1 hlt)
      refine ihk _ ?_ _ hΦe he0 heq rfl
      rw [← hk, ← hgs]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨m0, ?_, ?_⟩
        · simp [MvPolynomial.mem_support_iff, hg1, hdm0]
        · intro hm
          have h1 := (MvPolynomial.mem_support_iff.1 (Finset.mem_filter.1 hm).1)
          apply h1
          rw [hetop m0 hdm0.ge, hg1, rd_one]
      · intro m hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_filter.1 hm
        refine Finset.mem_filter.2 ⟨?_, hm2⟩
        rw [MvPolynomial.mem_support_iff] at hm1 ⊢
        intro h0
        apply hm1
        rw [hetop m hm2.ge, h0, rd_zero]

end
end DerivationHitting.Dev.Inj

open DerivationHitting.Dev.Inj
namespace DerivationHitting.Commutative
theorem chk_evaluation_injective {F : Type*} [Field F] [CharZero F] {n : ℕ}
    (b : Fin n → RatFunc F) (P : Fin n → PowerSeries F)
    (hP : arePrimitives b P) (hD : hasTrivialConstants b) :
    Function.Injective (associatedEvaluation P) := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  by_contra hne
  exact key b P hP hD _ _ h hh hne rfl rfl
end DerivationHitting.Commutative
end

theorem solution : type_of% @DerivationHitting.Commutative.chk_evaluation_injective := @DerivationHitting.Commutative.chk_evaluation_injective
