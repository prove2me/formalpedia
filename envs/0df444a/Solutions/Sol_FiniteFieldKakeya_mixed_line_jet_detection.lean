-- Prove2me | solution 1 for FiniteFieldKakeya.mixed_line_jet_detection
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:34:49.745588+00:00
-- url     : https://prove2.me/submissions/16f75e86-0ebd-44e6-8c87-a6f4cb7d94ce

import Mathlib
import Definitions.Def_KakeyaPolynomialMethods
import Theorems.Thm_FiniteFieldKakeya_uniform_grid_multiplicity_degree_bound

namespace FCP.Kakeya.DetectionProof

open MvPolynomial

noncomputable def lineMap {σ F : Type*} [CommSemiring F] (a b : σ → F) :
    MvPolynomial σ F →ₐ[F] Polynomial F :=
  MvPolynomial.aeval (fun j => Polynomial.C (a j)+Polynomial.X*Polynomial.C (b j))

lemma linear_natDegree_le {F : Type*} [CommSemiring F] (a b : F) :
    (Polynomial.C a+Polynomial.X*Polynomial.C b).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp
  · exact Polynomial.natDegree_mul_le.trans (by simpa using (Polynomial.natDegree_X_le (R := F)))

lemma lineMap_monomial {σ F : Type*} [CommSemiring F] (a b : σ → F)
    (m : σ →₀ ℕ) (c : F) :
    lineMap a b (monomial m c) = Polynomial.C c *
      ∏ j ∈ m.support, (Polynomial.C (a j)+Polynomial.X*Polynomial.C (b j)) ^ m j := by
  classical
  simp only [lineMap,aeval_monomial,Polynomial.algebraMap_eq,Finsupp.prod]

lemma natDegree_lineMap_monomial_le {σ F : Type*} [CommSemiring F] (a b : σ → F)
    (m : σ →₀ ℕ) (c : F) : (lineMap a b (monomial m c)).natDegree ≤ m.degree := by
  classical
  rw [lineMap_monomial]
  apply Polynomial.natDegree_mul_le.trans
  rw [Polynomial.natDegree_C,zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  exact Polynomial.natDegree_pow_le.trans (by
    simpa using Nat.mul_le_mul_left (m j) (linear_natDegree_le (a j) (b j)))

lemma natDegree_lineMap_le {σ F : Type*} [CommSemiring F] (a b : σ → F)
    (P : MvPolynomial σ F) : (lineMap a b P).natDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum,map_sum]
  apply (Polynomial.natDegree_sum_le _ _).trans
  apply Finset.sup_le
  intro m hm
  exact (natDegree_lineMap_monomial_le a b m _).trans (le_totalDegree hm)

lemma coeff_prod_sum {ι F : Type*} [CommSemiring F] (s : Finset ι)
    (p : ι → Polynomial F) (d : ι → ℕ) (hd : ∀ j ∈ s, (p j).natDegree ≤ d j) :
    (∏ j ∈ s, p j).coeff (∑ j ∈ s, d j) = ∏ j ∈ s, (p j).coeff (d j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj,Finset.sum_insert hj,Finset.prod_insert hj]
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (hd j (Finset.mem_insert_self _ _))]
    · rw [ih (fun k hk => hd k (Finset.mem_insert_of_mem hk))]
    · exact (Polynomial.natDegree_prod_le _ _).trans
        (Finset.sum_le_sum fun k hk => hd k (Finset.mem_insert_of_mem hk))

lemma coeff_lineMap_monomial_top {σ F : Type*} [CommSemiring F] (a b : σ → F)
    (m : σ →₀ ℕ) (c : F) :
    (lineMap a b (monomial m c)).coeff m.degree = c * ∏ j ∈ m.support, b j ^ m j := by
  classical
  rw [lineMap_monomial,Polynomial.coeff_C_mul]
  congr 1
  change Polynomial.coeff (∏ j ∈ m.support, (Polynomial.C (a j)+Polynomial.X*Polynomial.C (b j)) ^ m j) (∑ j ∈ m.support, m j) = _
  rw [coeff_prod_sum m.support _ (fun j => m j)]
  · apply Finset.prod_congr rfl
    intro j hj
    have h := Polynomial.coeff_pow_of_natDegree_le
      (m := m j) (linear_natDegree_le (a j) (b j))
    simpa using h
  · intro j hj
    exact Polynomial.natDegree_pow_le.trans (by
      simpa using Nat.mul_le_mul_left (m j) (linear_natDegree_le (a j) (b j)))

lemma coeff_lineMap_eq_eval_homogeneousComponent {σ F : Type*} [CommSemiring F]
    (a b : σ → F) (P : MvPolynomial σ F) (k : ℕ) (hk : P.totalDegree ≤ k) :
    (lineMap a b P).coeff k = eval b (homogeneousComponent k P) := by
  classical
  conv_lhs => rw [P.as_sum,map_sum,Polynomial.finsetSum_coeff]
  rw [homogeneousComponent_apply,map_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hmk : m.degree = k
  · rw [if_pos hmk,← hmk,coeff_lineMap_monomial_top,eval_monomial]
    rfl
  · rw [if_neg hmk]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hle : m.degree ≤ k := (le_totalDegree hm).trans hk
    exact (natDegree_lineMap_monomial_le a b m _).trans_lt (lt_of_le_of_ne hle hmk)

lemma eval_homogeneousComponent_of_lineMap_eq_zero {σ F : Type*} [CommSemiring F]
    (a b : σ → F) (P : MvPolynomial σ F) (k : ℕ) (hk : P.totalDegree ≤ k)
    (hline : lineMap a b P = 0) : eval b (homogeneousComponent k P) = 0 := by
  rw [← coeff_lineMap_eq_eval_homogeneousComponent a b P k hk,hline,Polynomial.coeff_zero]

end FCP.Kakeya.DetectionProof

section HasseAPI
open scoped BigOperators
open MvPolynomial
namespace KakeyaHasse
variable {σ R : Type*} [Fintype σ] [CommSemiring R]

@[simp] theorem coeff_hasse (i b : σ →₀ ℕ) (P : MvPolynomial σ R) :
    (hasse i P).coeff b = multiChoose (b + i) i * P.coeff (b + i) := rfl

@[simp] theorem hasse_zero (i : σ →₀ ℕ) : hasse i (0 : MvPolynomial σ R) = 0 := by
  ext b
  simp

@[simp] theorem hasse_add (i : σ →₀ ℕ) (P Q : MvPolynomial σ R) :
    hasse i (P + Q) = hasse i P + hasse i Q := by
  ext b
  simp [mul_add]

@[simp] theorem hasse_smul (i : σ →₀ ℕ) (c : R) (P : MvPolynomial σ R) :
    hasse i (c • P) = c • hasse i P := by
  ext b
  simp [smul_eq_mul, mul_left_comm]

@[simp] theorem hasse_zero_index (P : MvPolynomial σ R) : hasse 0 P = P := by
  ext b
  simp [multiChoose]

/-- The Hasse derivative as a linear map. -/
noncomputable def hasseLinear (i : σ →₀ ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R where
  toFun := hasse i
  map_add' := hasse_add i
  map_smul' := hasse_smul i


omit [Fintype σ] in
@[simp] theorem order_add (i j : σ →₀ ℕ) : order (i + j) = order i + order j := by
  classical
  simp [order, Finsupp.sum_add_index]

 theorem support_hasse (i : σ →₀ ℕ) (P : MvPolynomial σ R) {b : σ →₀ ℕ}
    (hb : b ∈ (hasse i P).support) : b + i ∈ P.support := by
  apply mem_support_iff.mpr
  intro hc
  have := mem_support_iff.mp hb
  simp [hc] at this

 theorem order_add_le_degree (i : σ →₀ ℕ) (P : MvPolynomial σ R) {b : σ →₀ ℕ}
    (hb : b ∈ (hasse i P).support) : order b + order i ≤ P.totalDegree := by
  rw [← order_add]
  exact le_totalDegree (support_hasse i P hb)

 theorem totalDegree_hasse_le (i : σ →₀ ℕ) (P : MvPolynomial σ R) :
    (hasse i P).totalDegree ≤ P.totalDegree - order i := by
  classical
  apply Finset.sup_le
  intro b hb
  have := order_add_le_degree i P hb
  change order b ≤ P.totalDegree - order i
  omega

 theorem hasse_eq_zero_of_totalDegree_lt (i : σ →₀ ℕ) (P : MvPolynomial σ R)
    (h : P.totalDegree < order i) : hasse i P = 0 := by
  ext b
  by_contra hb
  have hm : b ∈ (hasse i P).support := mem_support_iff.mpr (by simpa using hb)
  have := order_add_le_degree i P hm
  omega

 theorem multiChoose_comp (b i j : σ →₀ ℕ) :
    (multiChoose (b + j) j : R) * multiChoose (b + j + i) i =
      multiChoose (i + j) i * multiChoose (b + (i + j)) (i + j) := by
  classical
  simp only [multiChoose, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  simp only [Finsupp.add_apply]
  have h := Nat.choose_mul (n := b k + (i k + j k)) (Nat.le_add_right (i k) (j k))
  have hsub : b k + (i k + j k) - i k = b k + j k := by omega
  rw [hsub, Nat.add_sub_cancel_left] at h
  have h' : (b k + j k).choose (j k) * (b k + j k + i k).choose (i k) =
      (i k + j k).choose (i k) * (b k + (i k + j k)).choose (i k + j k) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using h.symm
  simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : R)) h'

 theorem hasse_hasse (i j : σ →₀ ℕ) (P : MvPolynomial σ R) :
    hasse j (hasse i P) = (multiChoose (i + j) i : R) • hasse (i + j) P := by
  ext b
  simp only [coeff_hasse, coeff_smul, smul_eq_mul, ← mul_assoc]
  rw [multiChoose_comp]
  simp [add_assoc, add_comm j i]

 theorem multiChoose_split [DecidableEq σ] (a i : σ →₀ ℕ) (j : σ) :
    (multiChoose a i : R) = ((a j).choose (i j) : R) *
      ∏ k ∈ Finset.univ.erase j, ((a k).choose (i k) : R) := by
  classical
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm

 theorem multiChoose_add_single (a i : σ →₀ ℕ) (j : σ) :
    (multiChoose (a + Finsupp.single j 1) (i + Finsupp.single j 1) : R) =
      multiChoose a (i + Finsupp.single j 1) + multiChoose a i := by
  classical
  rw [multiChoose_split _ _ j, multiChoose_split a (i + Finsupp.single j 1) j,
    multiChoose_split a i j]
  have he : (∏ k ∈ Finset.univ.erase j, (((a + Finsupp.single j 1 : σ →₀ ℕ) k).choose ((i + Finsupp.single j 1 : σ →₀ ℕ) k) : R)) =
      ∏ k ∈ Finset.univ.erase j, ((a k).choose (i k) : R) := by
    apply Finset.prod_congr rfl
    intro k hk
    simp [Finset.ne_of_mem_erase hk]
  have he' : (∏ k ∈ Finset.univ.erase j, ((a k).choose ((i + Finsupp.single j 1 : σ →₀ ℕ) k) : R)) =
      ∏ k ∈ Finset.univ.erase j, ((a k).choose (i k) : R) := by
    apply Finset.prod_congr rfl
    intro k hk
    simp [Finset.ne_of_mem_erase hk]
  rw [he, he']
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.choose_succ_succ', Nat.cast_add]
  ring

 theorem multiChoose_eq_zero_of_not_le (a i : σ →₀ ℕ) (h : ¬ i ≤ a) :
    (multiChoose a i : R) = 0 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, a j < i j := by
    simpa only [Finsupp.le_def, not_forall, not_le] using h
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [Nat.choose_eq_zero_of_lt hj]

 theorem hasse_mul_X_succ (i : σ →₀ ℕ) (j : σ) (P : MvPolynomial σ R) :
    hasse (i + Finsupp.single j 1) (P * X j) =
      hasse (i + Finsupp.single j 1) P * X j + hasse i P := by
  classical
  ext b
  have hm : j ∈ (b + (i + Finsupp.single j 1)).support := by
    simp [Finsupp.mem_support_iff]
  simp only [coeff_hasse, coeff_mul_X', if_pos hm, coeff_add]
  have hsub : b + (i + Finsupp.single j 1) - Finsupp.single j 1 = b + i := by
    simp [← add_assoc]
  rw [hsub]
  have hc := multiChoose_add_single (R := R) (b + i) i j
  rw [← add_assoc, hc, add_mul]
  by_cases hb : j ∈ b.support
  · rw [if_pos hb]
    have hle : Finsupp.single j 1 ≤ b := by
      simpa [Finsupp.single_le_iff, Finsupp.mem_support_iff, Nat.one_le_iff_ne_zero] using hb
    have he : b - Finsupp.single j 1 + (i + Finsupp.single j 1) = b + i := by
      rw [add_comm i, ← add_assoc, tsub_add_cancel_of_le hle]
    rw [he]
  · rw [if_neg hb]
    have hz : (multiChoose (b + i) (i + Finsupp.single j 1) : R) = 0 := by
      apply multiChoose_eq_zero_of_not_le
      intro hle
      have := hle j
      have hb' : b j = 0 := by simpa [Finsupp.mem_support_iff] using hb
      simp [hb'] at this
    simp [hz]

 theorem hasse_mul_X_of_eq_zero (i : σ →₀ ℕ) (j : σ) (P : MvPolynomial σ R)
    (hi : i j = 0) : hasse i (P * X j) = hasse i P * X j := by
  classical
  ext b
  have hm : j ∈ (b + i).support ↔ j ∈ b.support := by
    simp [Finsupp.mem_support_iff, hi]
  simp only [coeff_hasse, coeff_mul_X', hm]
  by_cases hb : j ∈ b.support
  · simp only [if_pos hb]
    have he : b - Finsupp.single j 1 + i = b + i - Finsupp.single j 1 := by
      ext k
      by_cases hk : k = j
      · subst k; simp [hi]
      · simp [hk]
    rw [he]
    congr 1
    unfold multiChoose
    apply Finset.prod_congr rfl
    intro k _
    by_cases hk : k = j
    · subst k; simp [hi]
    · simp [hk]
  · simp [hb]

@[simp] theorem hasse_C (i : σ →₀ ℕ) (c : R) :
    hasse i (C c) = if i = 0 then C c else 0 := by
  classical
  by_cases hi : i = 0
  · simp [hi]
  rw [if_neg hi]
  ext b
  have hbi : b + i ≠ 0 := by
    intro h
    have := (add_eq_zero.mp h).2
    exact hi this
  simp [coeff_C_of_ne_zero hbi]

 theorem hasse_mul_X (i : σ →₀ ℕ) (j : σ) (P : MvPolynomial σ R) :
    hasse i (P * X j) = hasse i P * X j +
      if i j = 0 then 0 else hasse (i - Finsupp.single j 1) P := by
  classical
  by_cases hi : i j = 0
  · simp [hi, hasse_mul_X_of_eq_zero i j P hi]
  · rw [if_neg hi]
    have hle : Finsupp.single j 1 ≤ i := by
      simpa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero] using hi
    have he : i - Finsupp.single j 1 + Finsupp.single j 1 = i :=
      tsub_add_cancel_of_le hle
    have ht := hasse_mul_X_succ (i - Finsupp.single j 1) j P
    rw [he] at ht
    exact ht

/-- Translation of the variables by a point. -/
noncomputable def shift (a : σ → R) (P : MvPolynomial σ R) : MvPolynomial σ R :=
  eval₂ C (fun j => X j + C (a j)) P

/-- Hasse derivatives are the coefficients in the Taylor expansion at a point. -/
 theorem eval_hasse (a : σ → R) (i : σ →₀ ℕ) (P : MvPolynomial σ R) :
    eval a (hasse i P) = (shift a P).coeff i := by
  classical
  induction P using MvPolynomial.induction_on generalizing i with
  | C c =>
      by_cases hi : i = 0 <;> simp [hi, shift, coeff_C, eq_comm]
  | add P Q hp hq =>
      simp only [hasse_add, eval_add, shift, eval₂_add, coeff_add]
      exact congrArg₂ (· + ·) (hp i) (hq i)
  | mul_X P j hp =>
      rw [hasse_mul_X, eval_add, eval_mul, eval_X, hp]
      simp only [shift, eval₂_mul, eval₂_X, mul_add, coeff_add, coeff_mul_X']
      rw [mul_comm _ (C (a j)), coeff_C_mul]
      by_cases hi : i j = 0
      · simp [hi, Finsupp.mem_support_iff, mul_comm]
      · simp only [hi, if_false, hp, Finsupp.mem_support_iff, ne_eq, not_false_eq_true, if_true]
        simp only [shift, mul_comm, add_comm]

/-- Translation commutes with Hasse differentiation. -/
 theorem hasse_shift (a : σ → R) (i : σ →₀ ℕ) (P : MvPolynomial σ R) :
    hasse i (shift a P) = shift a (hasse i P) := by
  ext b
  rw [coeff_hasse, ← eval_hasse, ← eval_hasse, hasse_hasse, smul_eval]
  simp [add_comm]

/-- Taking a Hasse derivative lowers a coefficient-vanishing order by at most its order. -/
 theorem low_coeff_hasse (i : σ →₀ ℕ) (P : MvPolynomial σ R) (m : ℕ)
    (hP : ∀ b, order b < m → P.coeff b = 0) :
    ∀ b, order b + order i < m → (hasse i P).coeff b = 0 := by
  intro b hb
  rw [coeff_hasse, hP (b + i) (by simpa only [order_add] using hb), mul_zero]

omit [Fintype σ] in
/-- Compatibility with Mathlib's total degree of a multi-index. -/
 theorem order_eq_degree (i : σ →₀ ℕ) : order i = i.degree := rfl

/-- Differentiation selects the corresponding homogeneous component. -/
 theorem homogeneousComponent_hasse (m : ℕ) (i : σ →₀ ℕ) (P : MvPolynomial σ R) :
    homogeneousComponent m (hasse i P) =
      hasse i (homogeneousComponent (m + order i) P) := by
  classical
  ext b
  simp only [coeff_homogeneousComponent, coeff_hasse, map_add]
  have he : b.degree + i.degree = m + order i ↔ b.degree = m := by
    rw [order_eq_degree]
    omega
  rw [if_congr he rfl rfl]
  split_ifs <;> simp

end KakeyaHasse

end HasseAPI


namespace FCP.Kakeya.UnivariateMultiplicity

open Polynomial

/-- A polynomial of degree less than `r * |F|` cannot have `r` vanishing jets at every field point. -/
theorem univariate_eq_zero_of_jets {F : Type*} [Field F] [Fintype F]
    (r : ℕ) (P : Polynomial F)
    (hjet : ∀ t : F, ∀ j : ℕ, j < r → (Polynomial.taylor t P).coeff j = 0)
    (hdeg : P.natDegree < r * Fintype.card F) : P = 0 := by
  classical
  by_contra hP
  have hlin (t : F) : (X - C t) ^ r ∣ P := by
    have ht : X ^ r ∣ taylor t P := X_pow_dvd_iff.mpr (hjet t)
    have hh := map_dvd (taylorAlgHom (-t)) ht
    change taylor (-t) (X ^ r) ∣ taylor (-t) (taylor t P) at hh
    simpa only [taylor_X_pow, taylor_taylor, neg_add_cancel,
      taylor_zero, map_neg, sub_eq_add_neg] using hh
  have hcop : Pairwise (fun a b : F => IsCoprime ((X - C a) ^ r) ((X - C b) ^ r)) := by
    intro a b hab
    exact (Polynomial.pairwise_coprime_X_sub_C (Function.injective_id) hab).pow
  have hprod : (∏ t : F, (X - C t) ^ r) ∣ P :=
    Fintype.prod_dvd_of_coprime hcop hlin
  have hdegree : (∏ t : F, (X - C t) ^ r).natDegree = r * Fintype.card F := by
    rw [natDegree_prod_of_monic Finset.univ (fun t : F => (X - C t) ^ r)
      (fun t _ => (monic_X_sub_C t).pow r)]
    simp [natDegree_pow, Nat.mul_comm]
  have hle := natDegree_le_of_dvd hprod hP
  rw [hdegree] at hle
  exact (not_lt_of_ge hle) hdeg

end FCP.Kakeya.UnivariateMultiplicity

namespace FCP.Kakeya.DetectionProof

open MvPolynomial

lemma order_cons_zero {d : ℕ} (i : Fin d →₀ ℕ) : KakeyaHasse.order (i.cons 0) = i.degree := by
  change (i.cons 0).sum (fun _ e => e) = _
  rw [Finsupp.sum_cons,zero_add]
  rfl

lemma topComponent_ne_zero {σ F : Type*} [CommSemiring F]
    (P : MvPolynomial σ F) (hP : P ≠ 0) : homogeneousComponent P.totalDegree P ≠ 0 := by
  classical
  have hs : P.support.Nonempty := support_nonempty.mpr hP
  obtain ⟨m,hm,hmax⟩ := Finset.exists_mem_eq_sup P.support hs (fun m => m.sum (fun _ e => e))
  have hdeg : m.degree = P.totalDegree := hmax.symm
  intro hz
  have hc := congrArg (coeff m) hz
  rw [coeff_homogeneousComponent,if_pos hdeg,coeff_zero] at hc
  exact (mem_support_iff.mp hm) hc

lemma hasse_lines_zero_of_mixed_jets {F : Type*} [Field F] [Fintype F]
    (d r rp : ℕ) (_hr : 0 < r) (_hrrp : r ≤ rp)
    (a : (Fin d → F) → (Fin (d+1) → F)) (P : MvPolynomial (Fin (d+1)) F)
    (hdeg : P.totalDegree < rp * Fintype.card F)
    (hjet : ∀ i : Fin d →₀ ℕ, i.degree < r → ∀ b : Fin d → F, ∀ t : F, ∀ j : ℕ,
      j < rp - i.degree / Fintype.card F →
      (Polynomial.taylor t (lineMap (a b) (Fin.cons 1 b) (KakeyaHasse.hasse (i.cons 0) P))).coeff j = 0) :
    ∀ i : Fin d →₀ ℕ, i.degree < r → ∀ b : Fin d → F,
      lineMap (a b) (Fin.cons 1 b) (KakeyaHasse.hasse (i.cons 0) P) = 0 := by
  intro i hi b
  by_cases hiD : P.totalDegree < i.degree
  · rw [KakeyaHasse.hasse_eq_zero_of_totalDegree_lt _ _ (by rwa [order_cons_zero]),map_zero]
  have hiD' : i.degree ≤ P.totalDegree := by omega
  apply UnivariateMultiplicity.univariate_eq_zero_of_jets (rp-i.degree/Fintype.card F) _ (hjet i hi b)
  have hline := natDegree_lineMap_le (a b) (Fin.cons 1 b) (KakeyaHasse.hasse (i.cons 0) P)
  have hhasse := KakeyaHasse.totalDegree_hasse_le (i.cons 0) P
  rw [order_cons_zero] at hhasse
  have hmul : (rp-i.degree/Fintype.card F)*Fintype.card F =
      rp*Fintype.card F-(i.degree/Fintype.card F)*Fintype.card F := Nat.sub_mul _ _ _
  have hfloor := Nat.div_mul_le_self i.degree (Fintype.card F)
  rw [hmul]
  omega

lemma eval_top_hasse_eq_zero_of_lines_zero {F : Type*} [Field F] {d r : ℕ}
    (a : (Fin d → F) → (Fin (d+1) → F)) (P : MvPolynomial (Fin (d+1)) F)
    (hline : ∀ i : Fin d →₀ ℕ, i.degree < r → ∀ b : Fin d → F,
      lineMap (a b) (Fin.cons 1 b) (KakeyaHasse.hasse (i.cons 0) P) = 0) :
    ∀ i : Fin d →₀ ℕ, i.degree < r → ∀ b : Fin d → F,
      eval (Fin.cons 1 b) (KakeyaHasse.hasse (i.cons 0)
        (homogeneousComponent P.totalDegree P)) = 0 := by
  intro i hi b
  by_cases hiD : P.totalDegree < i.degree
  · have hHdeg : (homogeneousComponent P.totalDegree P).totalDegree ≤ P.totalDegree :=
      (homogeneousComponent_isHomogeneous P.totalDegree P).totalDegree_le
    rw [KakeyaHasse.hasse_eq_zero_of_totalDegree_lt _ _ (by
      rw [order_cons_zero]
      exact hHdeg.trans_lt hiD),map_zero]
  have hiD' : i.degree ≤ P.totalDegree := by omega
  have hle := KakeyaHasse.totalDegree_hasse_le (i.cons 0) P
  rw [order_cons_zero] at hle
  have heval := eval_homogeneousComponent_of_lineMap_eq_zero
    (a b) (Fin.cons 1 b) (KakeyaHasse.hasse (i.cons 0) P)
    (P.totalDegree-i.degree) hle (hline i hi b)
  rw [KakeyaHasse.homogeneousComponent_hasse,order_cons_zero,
    Nat.sub_add_cancel hiD'] at heval
  exact heval

end FCP.Kakeya.DetectionProof


namespace KakeyaDehomogenize

open MvPolynomial

open KakeyaHasse

variable {R : Type*} [CommSemiring R] {d : ℕ}

/-- Set the distinguished first variable to one. -/
noncomputable def dehom : MvPolynomial (Fin (d + 1)) R →+* MvPolynomial (Fin d) R :=
  eval₂Hom C (Fin.cases (C 1) (fun j => X j))

@[simp] theorem dehom_C (c : R) : dehom (d := d) (C c) = C c := by simp [dehom]
@[simp] theorem dehom_X_zero : dehom (d := d) (X 0 : MvPolynomial _ R) = 1 := by
  simp [dehom]
@[simp] theorem dehom_X_succ (j : Fin d) : dehom (X j.succ : MvPolynomial _ R) = X j := by
  simp [dehom]

 theorem cons_zero_sub_single (i : Fin d →₀ ℕ) (j : Fin d) :
    i.cons 0 - Finsupp.single j.succ 1 = (i - Finsupp.single j 1).cons 0 := by
  ext k
  refine Fin.cases ?_ (fun l => ?_) k
  · simp
  · simp [Finsupp.single_apply]

/-- Hasse differentiation in the tail variables commutes with dehomogenization. -/
 theorem hasse_dehom (i : Fin d →₀ ℕ) (P : MvPolynomial (Fin (d + 1)) R) :
    hasse i (dehom P) = dehom (hasse (i.cons 0) P) := by
  classical
  induction P using MvPolynomial.induction_on generalizing i with
  | C c =>
      by_cases hi : i = 0
      · simp [hi]
      · have hi' : i.cons 0 ≠ 0 := Finsupp.cons_ne_zero_of_right hi
        simp [hasse_C, hi, hi']
  | add P Q hp hq => simp [hp, hq]
  | mul_X P j hp =>
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [hasse_mul_X, hp]
      · simp only [map_mul, dehom_X_succ, hasse_mul_X, Finsupp.cons_succ,
          map_add, cons_zero_sub_single]
        by_cases hi : i k = 0 <;> simp [hi, hp]

 theorem dehom_monomial (a : Fin (d + 1) →₀ ℕ) (c : R) :
    dehom (monomial a c) = monomial a.tail c := by
  classical
  change eval₂ C (Fin.cases (C 1) (fun j => X j)) (monomial a c) = _
  rw [eval₂_monomial, monomial_eq]
  simp only [Finsupp.prod_pow, Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ,
    map_one, one_pow, one_mul, Finsupp.tail_apply]

 theorem dehom_eq_sum (P : MvPolynomial (Fin (d + 1)) R) :
    dehom P = ∑ a ∈ P.support, monomial a.tail (P.coeff a) := by
  classical
  conv_lhs => rw [← P.support_sum_monomial_coeff]
  simp only [map_sum, dehom_monomial]

 theorem coeff_dehom (b : Fin d →₀ ℕ) (P : MvPolynomial (Fin (d + 1)) R) :
    (dehom P).coeff b = ∑ a ∈ P.support, if a.tail = b then P.coeff a else 0 := by
  classical
  rw [dehom_eq_sum, coeff_sum]
  simp only [coeff_monomial]

 theorem support_dehom {P : MvPolynomial (Fin (d + 1)) R} {b : Fin d →₀ ℕ}
    (hb : b ∈ (dehom P).support) : ∃ a ∈ P.support, a.tail = b := by
  classical
  have hc := mem_support_iff.mp hb
  rw [coeff_dehom] at hc
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  refine ⟨a, ha, ?_⟩
  by_contra h
  simp [h] at hne

 theorem degree_head_tail (a : Fin (d + 1) →₀ ℕ) :
    a.degree = a 0 + a.tail.degree := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_succ, Finsupp.tail_apply]

 theorem homogeneous_tail_injective (H : MvPolynomial (Fin (d + 1)) R) (k : ℕ)
    (hH : H.IsHomogeneous k) {a b : Fin (d + 1) →₀ ℕ}
    (ha : a ∈ H.support) (hb : b ∈ H.support) (hab : a.tail = b.tail) : a = b := by
  have ha' : a.degree = k := (hH.degree_eq_sum_deg_support ha).symm
  have hb' : b.degree = k := (hH.degree_eq_sum_deg_support hb).symm
  rw [degree_head_tail, hab] at ha'
  rw [degree_head_tail] at hb'
  have h0 : a 0 = b 0 := by omega
  rw [← Finsupp.cons_tail a, ← Finsupp.cons_tail b, hab, h0]

/-- A homogeneous polynomial is determined by its value with the first variable set to one. -/
 theorem homogeneous_eq_zero_of_dehom_eq_zero
    (H : MvPolynomial (Fin (d + 1)) R) (k : ℕ) (hH : H.IsHomogeneous k)
    (hz : dehom H = 0) : H = 0 := by
  classical
  ext a
  by_cases ha : a ∈ H.support
  · have hc := congrArg (MvPolynomial.coeff a.tail) hz
    rw [coeff_dehom, coeff_zero] at hc
    have hs : (∑ b ∈ H.support, if b.tail = a.tail then H.coeff b else 0) = H.coeff a := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro b hb hba
        have hne : b.tail ≠ a.tail := by
          intro he
          exact hba (homogeneous_tail_injective H k hH hb ha he)
        simp [hne]
      · exact fun h => (h ha).elim
    simpa only [hs, coeff_zero] using hc
  · simpa only [coeff_zero] using notMem_support_iff.mp ha

/-- A bound on every tail exponent gives the same strict total-degree bound after dehomogenizing. -/
 theorem totalDegree_dehom_lt (P : MvPolynomial (Fin (d + 1)) R) (r : ℕ) (hr : 0 < r)
    (hP : ∀ a ∈ P.support, ∑ j : Fin d, a j.succ < r) :
    (dehom P).totalDegree < r := by
  classical
  have hle : (dehom P).totalDegree ≤ r - 1 := by
    apply Finset.sup_le
    intro b hb
    obtain ⟨a, ha, rfl⟩ := support_dehom hb
    have := hP a ha
    change a.tail.degree ≤ r - 1
    rw [Finsupp.degree_eq_sum]
    simp only [Finsupp.tail_apply]
    omega
  omega

/-- Evaluating the dehomogenization is evaluation at the corresponding affine point. -/
 theorem eval_dehom (b : Fin d → R) (P : MvPolynomial (Fin (d + 1)) R) :
    eval b (dehom P) = eval (Fin.cons 1 b) P := by
  change eval b (eval₂ C (Fin.cases (C 1) (fun j => X j)) P) = _
  rw [← eval_assoc]
  apply congrArg (fun f : Fin (d + 1) → R => eval f P)
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp

end KakeyaDehomogenize


namespace FCP.Kakeya.DetectionProof

open MvPolynomial

/-- Mixed vanishing on one line in each non-horizontal direction detects every polynomial
in the anisotropic degree range of Bukh--Chao Lemma 9. -/
theorem detection {F : Type*} [Field F] [Fintype F]
    (d r rp : ℕ) (hr : 0 < r) (hrrp : r ≤ rp)
    (a : (Fin d → F) → (Fin (d+1) → F)) (P : MvPolynomial (Fin (d+1)) F)
    (hsupport : ∀ α ∈ P.support,
      (∑ j : Fin d, α j.succ) < r * Fintype.card F ∧
      α.sum (fun _ e => e) < rp * Fintype.card F)
    (hjet : ∀ i : Fin d →₀ ℕ, i.sum (fun _ e => e) < r →
      ∀ b : Fin d → F, ∀ t : F, ∀ j : ℕ,
      j < rp - i.sum (fun _ e => e) / Fintype.card F →
      (Polynomial.taylor t (lineMap (a b) (Fin.cons 1 b)
        (KakeyaHasse.hasse (i.cons 0) P))).coeff j = 0) : P = 0 := by
  classical
  by_contra hP
  have hrp : 0 < rp := hr.trans_le hrrp
  have hdegP : P.totalDegree < rp * Fintype.card F := by
    rw [totalDegree,Finset.sup_lt_iff (Nat.mul_pos hrp Fintype.card_pos)]
    intro α hα
    exact (hsupport α hα).2
  have hline := hasse_lines_zero_of_mixed_jets d r rp hr hrrp a P hdegP hjet
  have heval := eval_top_hasse_eq_zero_of_lines_zero a P hline
  let H := homogeneousComponent P.totalDegree P
  let Q := KakeyaDehomogenize.dehom H
  have hH : H.IsHomogeneous P.totalDegree := homogeneousComponent_isHomogeneous _ _
  have hHne : H ≠ 0 := topComponent_ne_zero P hP
  have hQne : Q ≠ 0 := by
    intro hz
    exact hHne (KakeyaDehomogenize.homogeneous_eq_zero_of_dehom_eq_zero H P.totalDegree hH hz)
  have hQdeg : Q.totalDegree < r * Fintype.card F := by
    apply KakeyaDehomogenize.totalDegree_dehom_lt H _ (Nat.mul_pos hr Fintype.card_pos)
    intro α hα
    change α ∈ (homogeneousComponent P.totalDegree P).support at hα
    rw [support_homogeneousComponent] at hα
    exact (hsupport α (Finset.mem_filter.mp hα).1).1
  have hjQ : ∀ b : Fin d → F, ∀ i : Fin d →₀ ℕ, i.sum (fun _ e => e) < r →
      coeff i (eval₂ C (fun j => X j+C (b j)) Q) = 0 := by
    intro b i hi
    change (KakeyaHasse.shift b Q).coeff i = 0
    rw [← KakeyaHasse.eval_hasse]
    change eval b (KakeyaHasse.hasse i (KakeyaDehomogenize.dehom H)) = 0
    rw [KakeyaDehomogenize.hasse_dehom,KakeyaDehomogenize.eval_dehom]
    exact heval i hi b
  have hbound := FiniteFieldKakeya.uniform_grid_multiplicity_degree_bound d r Q hQne hjQ
  exact (not_lt_of_ge hbound) hQdeg

end FCP.Kakeya.DetectionProof

/-- Bukh--Chao polynomial detection from mixed jets along non-horizontal lines. -/
theorem solution {F : Type*} [Field F] [Fintype F]
    (d r rp : ℕ) (hr : 0 < r) (hrrp : r ≤ rp)
    (a : (Fin d → F) → (Fin (d+1) → F)) (P : MvPolynomial (Fin (d+1)) F)
    (hsupport : ∀ α ∈ P.support,
      (∑ j : Fin d, α j.succ) < r * Fintype.card F ∧
      α.sum (fun _ e => e) < rp * Fintype.card F)
    (hjet : ∀ i : Fin d →₀ ℕ, i.sum (fun _ e => e) < r →
      ∀ b : Fin d → F, ∀ t : F, ∀ j : ℕ,
      j < rp - i.sum (fun _ e => e) / Fintype.card F →
      (Polynomial.taylor t (KakeyaPolynomialMethods.lineMap (a b) (Fin.cons 1 b)
        (KakeyaHasse.hasse (i.cons 0) P))).coeff j = 0) : P = 0 := by
  exact FCP.Kakeya.DetectionProof.detection d r rp hr hrrp a P hsupport hjet
