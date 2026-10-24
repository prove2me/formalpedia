-- Prove2me | solution 1 for FCP.Kakeya.kakeya_finite_field
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:40:17.050791+00:00
-- url     : https://prove2.me/submissions/e6f1bf31-07c4-4821-a823-45a14ff05fa1

import Mathlib
import Definitions.Def_FCP_Kakeya
import Definitions.Def_KakeyaPolynomialMethods
import Theorems.Thm_FiniteFieldKakeya_mixed_line_jet_detection


/- The bounded-monomial enumeration below is reused from moona3k's accepted
Dvir proof, submission fcd1e553-811e-45c7-8ba3-84e630918670 (2026-10-04).
The sharp-bound counting identities following it are new formal work here. -/
namespace FCP.Kakeya.SharpCounting
open Finset Finsupp MvPolynomial Polynomial

theorem funsum_eq (n : ℕ) (d : Fin n →₀ ℕ) : ∑ j, d j = d.sum (fun _ e => e) := by
  classical
  rw [Finsupp.sum]
  exact (Finset.sum_subset (Finset.subset_univ d.support) (fun j _ hj => by
    rw [Finsupp.notMem_support_iff.1 hj])).symm

/-- Hockey stick, in the descending form used below. -/
theorem hockey (n m : ℕ) : ∑ k ∈ Finset.range (m + 1), Nat.choose (m - k + n) n
    = Nat.choose (m + n + 1) (n + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ']
    have hreind : ∑ k ∈ Finset.range (m + 1), Nat.choose (m + 1 - (k + 1) + n) n
        = ∑ k ∈ Finset.range (m + 1), Nat.choose (m - k + n) n :=
      Finset.sum_congr rfl fun k _ => by congr 1; omega
    rw [hreind, ih]
    have h0 : m + 1 - 0 + n = m + 1 + n := by omega
    rw [h0]
    have h := Nat.choose_succ_succ' (m + n + 1) n
    simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] at h ⊢
    exact h.symm

/-! ### Stage 1: counting monomials of bounded total degree -/

/-- Functions `Fin n → ℕ` with coordinate sum `≤ m`. -/
def funLe : (n m : ℕ) → Finset (Fin n → ℕ)
  | 0, _ => Finset.univ
  | n + 1, m => Finset.biUnion (Finset.range (m + 1)) fun k =>
      (funLe n (m - k)).image (fun f => (Fin.cons k f : Fin (n + 1) → ℕ))

theorem mem_funLe : ∀ (n m : ℕ) (f : Fin n → ℕ), f ∈ funLe n m ↔ ∑ j, f j ≤ m := by
  intro n
  induction n with
  | zero =>
    intro m f
    constructor
    · intro _; simp
    · intro _; exact Finset.mem_univ _
  | succ n ih =>
    intro m f
    constructor
    · intro hf
      simp only [funLe, Finset.mem_biUnion, Finset.mem_image] at hf
      obtain ⟨k, hkkm, f', hf'mem, rfl⟩ := hf
      have hsum : ∑ j : Fin (n + 1), Fin.cons k f' j = k + ∑ j, f' j := by
        rw [Fin.sum_univ_succ]
        simp
      have h2 := (ih (m - k) f').1 hf'mem
      have hkm : k ≤ m := by simpa [Finset.mem_range] using hkkm
      simp only [hsum]
      omega
    · intro hsum
      have hle : f 0 ≤ ∑ j, f j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      have hk : f 0 ∈ Finset.range (m + 1) := by
        simp only [Finset.mem_range]
        omega
      refine Finset.mem_biUnion.mpr ⟨f 0, hk, ?_⟩
      have hsplit : ∑ j : Fin (n + 1), f j = f 0 + ∑ j : Fin n, f (Fin.succ j) := by
        rw [Fin.sum_univ_succ]
      have hsub : ∑ j : Fin n, f (Fin.succ j) ≤ m - f 0 := by omega
      refine Finset.mem_image.mpr ⟨fun j => f (Fin.succ j), (ih (m - f 0) _).2 hsub, ?_⟩
      funext j
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · simp
      · simp

theorem card_funLe (n m : ℕ) : (funLe n m).card = Nat.choose (m + n) n := by
  induction n generalizing m with
  | zero => simp [funLe]
  | succ n ih =>
    have hconsinj : ∀ k : ℕ,
        Function.Injective (fun f : Fin n → ℕ => (Fin.cons k f : Fin (n + 1) → ℕ)) := by
      intro k f₁ f₂ h
      have h' : (Fin.cons k f₁ : Fin (n + 1) → ℕ) = (Fin.cons k f₂ : Fin (n + 1) → ℕ) := h
      funext j
      have e1 : (Fin.cons k f₁ : Fin (n + 1) → ℕ) (Fin.succ j) = f₁ j := by simp
      have e2 : (Fin.cons k f₂ : Fin (n + 1) → ℕ) (Fin.succ j) = f₂ j := by simp
      have hc := congrFun h' (Fin.succ j)
      rw [e1, e2] at hc
      exact hc
    have hdisj : (Finset.range (m + 1) : Set ℕ).PairwiseDisjoint fun k =>
        (funLe n (m - k)).image (fun f => (Fin.cons k f : Fin (n + 1) → ℕ)) := by
      intro k _ l _ hkl
      refine Finset.disjoint_right.mpr fun g hg => ?_
      obtain ⟨f₂, _, rfl⟩ := Finset.mem_image.1 hg
      rw [Finset.mem_image]
      intro hmem
      obtain ⟨f₁, _, hfg⟩ := hmem
      exact hkl (by
        have h0 := congrFun hfg 0
        simpa using h0)
    rw [funLe, Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun k _ =>
      card_image_of_injective _ (hconsinj k)), Finset.sum_congr rfl (fun k _ => by rw [ih])]
    exact hockey n m

/-- Monomials of total degree `≤ m` in `n` variables, as finsupps. -/
noncomputable def monoLe (n m : ℕ) : Finset (Fin n →₀ ℕ) :=
  (funLe n m).image Finsupp.equivFunOnFinite.symm

theorem card_monoLe (n m : ℕ) : (monoLe n m).card = Nat.choose (m + n) n := by
  simp only [monoLe]
  rw [Finset.card_image_of_injective _ (Equiv.injective _), card_funLe]

theorem mem_monoLe {n m : ℕ} (d : Fin n →₀ ℕ) :
    d ∈ monoLe n m ↔ d.sum (fun _ e => e) ≤ m := by
  rw [monoLe, Finset.mem_image]
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hpoint : ∑ j, (Finsupp.equivFunOnFinite.symm f) j = ∑ j, f j :=
      Finset.sum_congr rfl fun j _ => rfl
    rw [← funsum_eq n (Finsupp.equivFunOnFinite.symm f), hpoint]
    exact (mem_funLe n m f).1 hf
  · intro h
    refine ⟨Finsupp.equivFunOnFinite d, ?_, Finsupp.equivFunOnFinite.symm_apply_apply d⟩
    refine (mem_funLe n m _).2 ?_
    have hpoint : ∑ j, Finsupp.equivFunOnFinite d j = ∑ j, d j :=
      Finset.sum_congr rfl fun j _ => rfl
    rw [hpoint, funsum_eq n d]
    exact h



/-- Counting points below the graph of a nonnegative integer-valued function. -/
lemma sum_complements {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ)
    (m : ℕ) :
    (∑ x ∈ S, (m + 1 - f x)) =
      ∑ k ∈ Finset.range (m + 1), (S.filter (fun x => f x ≤ k)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_filter]
  have hset : (Finset.range (m + 1)).filter (fun k => f x ≤ k) =
      Finset.Ico (f x) (m + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset]
  simp

lemma sum_complements_funLe (d m : ℕ) :
    (∑ f ∈ funLe d m, (m + 1 - ∑ j, f j)) = (m + d + 1).choose (d + 1) := by
  rw [sum_complements _ _ m]
  have hfilter (k : ℕ) (hk : k ∈ Finset.range (m + 1)) :
      (funLe d m).filter (fun f => ∑ j, f j ≤ k) = funLe d k := by
    ext f
    simp only [Finset.mem_filter, mem_funLe]
    have hkm : k ≤ m := by have := Finset.mem_range.mp hk; omega
    omega
  calc
    _ = ∑ k ∈ Finset.range (m + 1), (k + d).choose d := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hfilter k hk, card_funLe]
    _ = _ := Nat.sum_range_add_choose m d

/-- The total of all degrees in a bounded monomial simplex. -/
lemma sum_degrees_funLe (d m : ℕ) :
    (∑ f ∈ funLe d m, ∑ j, f j) = d * (m + d).choose (d + 1) := by
  have hsum : (∑ f ∈ funLe d m, (m + 1 - ∑ j, f j)) +
      (∑ f ∈ funLe d m, ∑ j, f j) = (m + 1) * (funLe d m).card := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _f ∈ funLe d m, (m + 1) := by
        apply Finset.sum_congr rfl
        intro f hf
        have := (mem_funLe d m f).mp hf
        omega
      _ = _ := by simp [Nat.mul_comm]
  rw [sum_complements_funLe, card_funLe, Nat.choose_succ_succ] at hsum
  have hmul := Nat.choose_succ_right_eq (m + d) d
  simp only [Nat.add_sub_cancel] at hmul
  nlinarith

/-- Exponents with transverse degree less than `R` and total degree less than `D`.
The distinguished (line) coordinate is the first coordinate. -/
noncomputable def anisotropicExponents (d R D : ℕ) : Finset (Fin (d + 1) → ℕ) :=
  ((funLe d (R - 1)).sigma (fun f => Finset.range (D - ∑ j, f j))).image
    (fun z => Fin.cons z.2 z.1)

lemma mem_anisotropicExponents (d R D : ℕ) (hR : 0 < R) (f : Fin (d + 1) → ℕ) :
    f ∈ anisotropicExponents d R D ↔
      (∑ j : Fin d, f j.succ) < R ∧ (∑ j, f j) < D := by
  classical
  simp only [anisotropicExponents, Finset.mem_image, Finset.mem_sigma, Finset.mem_range,
    mem_funLe]
  constructor
  · rintro ⟨⟨g,k⟩, ⟨hg,hk⟩, rfl⟩
    dsimp at hg hk ⊢
    simp only [Fin.cons_succ, Fin.sum_univ_succ, Fin.cons_zero]
    omega
  · rintro ⟨htrans,htotal⟩
    refine ⟨⟨fun j => f j.succ, f 0⟩, ?_, ?_⟩
    · dsimp
      rw [Fin.sum_univ_succ] at htotal
      constructor <;> omega
    · exact Fin.cons_self_tail f

lemma card_anisotropicExponents (d R D : ℕ) (hR : 0 < R) (hRD : R ≤ D) :
    (anisotropicExponents d R D).card =
      (D - R) * (R + d - 1).choose d + (R + d).choose (d + 1) := by
  classical
  have hinj : Function.Injective
      (fun z : (Σ _f : Fin d → ℕ, ℕ) => (Fin.cons z.2 z.1 : Fin (d + 1) → ℕ)) := by
    rintro ⟨f,j⟩ ⟨g,k⟩ h
    have hj : j = k := congrFun h 0
    have hfg : f = g := by
      funext i
      exact congrFun h i.succ
    subst k
    subst g
    rfl
  rw [anisotropicExponents, Finset.card_image_of_injective _ hinj, Finset.card_sigma]
  simp only [Finset.card_range]
  have hform (f : Fin d → ℕ) (hf : f ∈ funLe d (R - 1)) :
      D - ∑ j, f j = (D - R) + (R - ∑ j, f j) := by
    have := (mem_funLe d (R - 1) f).mp hf
    omega
  calc
    _ = ∑ f ∈ funLe d (R - 1), ((D - R) + (R - ∑ j, f j)) :=
      Finset.sum_congr rfl hform
    _ = (D - R) * (funLe d (R - 1)).card +
        ∑ f ∈ funLe d (R - 1), (R - ∑ j, f j) := by
      simp [Finset.sum_add_distrib, Nat.mul_comm]
    _ = _ := by
      rw [card_funLe]
      have hc := sum_complements_funLe d (R - 1)
      have h1 : R - 1 + 1 = R := by omega
      have h2 : R - 1 + d + 1 = R + d := by omega
      have h3 : R - 1 + d = R + d - 1 := by omega
      rw [h1, h2] at hc
      rw [hc, h3]

lemma degree_minus_quotient_le (q k : ℕ) (hq : 0 < q) :
    ((k - k / q : ℕ) : ℝ) ≤ (1 - 1 / (q : ℝ)) * k + 1 := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hmod : ((k % q : ℕ) : ℝ) < q := by exact_mod_cast Nat.mod_lt k hq
  have hdiv : (k : ℝ) = ((k % q : ℕ) : ℝ) + q * ((k / q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div k q).symm
  have hfloor : (k : ℝ) / q - 1 < ((k / q : ℕ) : ℝ) := by
    apply (sub_lt_iff_lt_add).mpr
    apply (div_lt_iff₀ hqR).mpr
    nlinarith
  rw [Nat.cast_sub (Nat.div_le_self k q)]
  have heq : (1 - 1 / (q : ℝ)) * k + 1 = k - ((k : ℝ) / q - 1) := by ring
  rw [heq]
  linarith

lemma high_conditions_bound (d r q : ℕ) (hr : 0 < r) (hq : 0 < q) :
    (∑ f ∈ funLe d (r - 1), ((∑ j, f j) - (∑ j, f j) / q : ℕ) : ℝ) ≤
      (1 - 1 / (q : ℝ)) * d * ((r + d - 1).choose (d + 1) : ℝ) +
        ((r + d - 1).choose d : ℝ) := by
  have hpoint := Finset.sum_le_sum (s := funLe d (r - 1))
    (fun f _ => degree_minus_quotient_le q (∑ j, f j) hq)
  have hdeg : (∑ f ∈ funLe d (r - 1), (∑ j, f j : ℕ) : ℝ) =
      (d : ℝ) * ((r - 1 + d).choose (d + 1) : ℝ) := by
    exact_mod_cast sum_degrees_funLe d (r - 1)
  have hshift : r - 1 + d = r + d - 1 := by omega
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, hdeg, Finset.sum_const,
    nsmul_eq_mul, mul_one, card_funLe, hshift, mul_assoc] using hpoint

/-- The additional line conditions after shared low-degree point conditions are removed. -/
noncomputable def highIndices (d r rp q : ℕ) : Finset (Σ _i : Fin d → ℕ, ℕ) :=
  (funLe d (r - 1)).sigma (fun i =>
    Finset.Ico (rp - ∑ j, i j) (rp - (∑ j, i j) / q))

lemma mem_highIndices (d r rp q : ℕ) (hr : 0 < r) (hrrp : r ≤ rp)
    (i : Fin d → ℕ) (j : ℕ) :
    (⟨i,j⟩ : Σ _i : Fin d → ℕ, ℕ) ∈ highIndices d r rp q ↔
      (∑ k, i k) < r ∧ rp ≤ (∑ k, i k) + j ∧ j < rp - (∑ k, i k) / q := by
  classical
  simp only [highIndices, Finset.mem_sigma, mem_funLe, Finset.mem_Ico]
  omega

lemma card_highIndices (d r rp q : ℕ) (hr : 0 < r) (hrrp : r ≤ rp) :
    (highIndices d r rp q).card =
      ∑ i ∈ funLe d (r - 1), ((∑ j, i j) - (∑ j, i j) / q) := by
  classical
  rw [highIndices, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.card_Ico]
  have hdeg := (mem_funLe d (r - 1) i).mp hi
  have hdiv := Nat.div_le_self (∑ j, i j) q
  omega

lemma card_highIndices_le (d r rp q : ℕ) (hr : 0 < r) (hrrp : r ≤ rp) (hq : 0 < q) :
    ((highIndices d r rp q).card : ℝ) ≤
      (1 - 1 / (q : ℝ)) * d * ((r + d - 1).choose (d + 1) : ℝ) +
        ((r + d - 1).choose d : ℝ) := by
  rw [card_highIndices d r rp q hr hrrp, Nat.cast_sum]
  exact high_conditions_bound d r q hr hq

end FCP.Kakeya.SharpCounting


open Filter Topology

namespace FCP.Kakeya.SharpCounting

/-- A shifted linear natural sequence has its expected slope after normalization. -/
lemma tendsto_linear_sub_div (a b c : ℕ) (ha : 0 < a) :
    Tendsto (fun s : ℕ => ((a * s + b - c : ℕ) : ℝ) / (s : ℝ)) atTop (𝓝 (a : ℝ)) := by
  have h : Tendsto (fun s : ℕ => (a : ℝ) + ((b : ℝ) - c) / s) atTop
      (𝓝 ((a : ℝ) + 0)) := tendsto_const_nhds.add
    (tendsto_const_div_atTop_nhds_zero_nat ((b : ℝ) - c))
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (c + 1)] with s hs
  have hsc : c ≤ a * s + b := by
    have hsa : s ≤ a * s := by simpa using Nat.mul_le_mul_right s ha
    omega
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  rw [Nat.cast_sub hsc, Nat.cast_add, Nat.cast_mul]
  field_simp
  ring

/-- Binomial coefficients with a linearly growing top index have the usual leading term. -/
lemma tendsto_choose_linear (a b c k : ℕ) (ha : 0 < a) :
    Tendsto (fun s : ℕ => ((a * s + b - c).choose k : ℝ) / (s : ℝ) ^ k)
      atTop (𝓝 ((a : ℝ) ^ k / k.factorial)) := by
  have hprod := tendsto_finsetProd (Finset.range k)
    (fun j _ => tendsto_linear_sub_div a b (c + j) ha)
  simp only [Finset.prod_const, Finset.card_range] at hprod
  have h := hprod.div_const (k.factorial : ℝ)
  convert h using 1
  ext s
  rw [Nat.choose_eq_descFactorial_div_factorial,
    Nat.cast_div (Nat.factorial_dvd_descFactorial _ _) (by positivity),
    Nat.descFactorial_eq_prod_range]
  simp only [Nat.cast_prod, Nat.sub_sub, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_range]
  ring

lemma tendsto_choose_linear_lower_order (a b c k : ℕ) (ha : 0 < a) :
    Tendsto (fun s : ℕ => ((a * s + b - c).choose k : ℝ) / (s : ℝ) ^ (k + 1))
      atTop (𝓝 0) := by
  have h := (tendsto_choose_linear a b c k ha).mul
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [mul_zero, pow_succ, div_mul_eq_div_mul_one_div] using h

lemma tendsto_mul_choose_linear (a b c k : ℕ) (ha : 0 < a) :
    Tendsto (fun s : ℕ => (s : ℝ) * ((a * s + b - c).choose k : ℝ) /
        (s : ℝ) ^ (k + 1)) atTop (𝓝 ((a : ℝ) ^ k / k.factorial)) := by
  apply (tendsto_choose_linear a b c k ha).congr'
  filter_upwards [eventually_ge_atTop 1] with s hs
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  rw [pow_succ]
  field_simp [hs0]

/-- The exact binomial inequality whose leading coefficients yield Bukh--Chao's constant. -/
def CountingBound (q d m : ℕ) : Prop :=
  ∀ s : ℕ, 0 < s →
    ((q - 1) * q * s : ℕ) *
        (((q * q * s + d - 1).choose d : ℕ) : ℝ) +
        ((q * q * s + d).choose (d + 1) : ℝ) ≤
      (m : ℝ) * (((2 * q - 1) * s + d).choose (d + 1) : ℝ) +
      (q : ℝ) ^ (d + 1) *
        (((q - 1 : ℕ) : ℝ) / q * d * ((q * s + d - 1).choose (d + 1) : ℝ) +
          ((q * s + d - 1).choose d : ℝ))

lemma leading_coefficients_le (q d m : ℕ) (hq : 2 ≤ q) (h : CountingBound q d m) :
    ((q - 1 : ℕ) : ℝ) * q * ((q * q : ℕ) : ℝ) ^ d / d.factorial +
      ((q * q : ℕ) : ℝ) ^ (d + 1) / (d + 1).factorial ≤
    m * ((2 * q - 1 : ℕ) : ℝ) ^ (d + 1) / (d + 1).factorial +
      (q : ℝ) ^ (d + 1) *
        (((q - 1 : ℕ) : ℝ) / q * d * (q : ℝ) ^ (d + 1) / (d + 1).factorial) := by
  have hq0 : 0 < q := by omega
  have hqq : 0 < q * q := Nat.mul_pos hq0 hq0
  have ht : 0 < 2 * q - 1 := by omega
  have hA := ((tendsto_mul_choose_linear (q * q) d 1 d hqq).const_mul
    (((q - 1 : ℕ) : ℝ) * q)).add
    (tendsto_choose_linear (q * q) d 0 (d + 1) hqq)
  have hL := (tendsto_choose_linear (2 * q - 1) d 0 (d + 1) ht).const_mul (m : ℝ)
  have hB := (((tendsto_choose_linear q d 1 (d + 1) hq0).const_mul
      (((q - 1 : ℕ) : ℝ) / q * d)).add
    (tendsto_choose_linear_lower_order q d 1 d hq0)).const_mul ((q : ℝ) ^ (d + 1))
  have hle := le_of_tendsto_of_tendsto hA (hL.add hB)
  simp only [Nat.sub_zero, add_zero, mul_div_assoc] at hle ⊢
  apply hle
  filter_upwards [eventually_ge_atTop 1] with s hs
  have hs0 : 0 < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  have hh := div_le_div_of_nonneg_right (h s (by omega)) (le_of_lt (pow_pos hs0 (d + 1)))
  push_cast at hh
  convert hh using 1 <;> ring

/-- Passing to leading coefficients in the finite condition count gives the exact sharp constant. -/
lemma sharp_bound_of_counting (q d m : ℕ) (hq : 2 ≤ q) (h : CountingBound q d m) :
    (q : ℝ) ^ (d + 1) / (2 - 1 / (q : ℝ)) ^ d ≤ m := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have ht : 0 < 2 * (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hbase : 0 < 2 - 1 / (q : ℝ) := by
    have heq : 2 - 1 / (q : ℝ) = (2 * q - 1) / q := by field_simp
    rw [heq]
    exact div_pos ht hqR
  have hh := leading_coefficients_le q d m hq h
  rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub (by omega : 1 ≤ 2 * q)] at hh
  norm_num only [Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hh
  have hf : (d.factorial : ℝ) ≠ 0 := by positivity
  have hg : ((d + 1).factorial : ℝ) ≠ 0 := by positivity
  have hfac : ((d + 1).factorial : ℝ) = ((d : ℝ) + 1) * d.factorial := by
    simp [Nat.factorial_succ]
  have halg :
      (((q : ℝ) - 1) * q * (q * q) ^ d / d.factorial +
        (q * q) ^ (d + 1) / (d + 1).factorial -
        (q : ℝ) ^ (d + 1) *
          (((q : ℝ) - 1) / q * d * q ^ (d + 1) / (d + 1).factorial)) *
        (d + 1).factorial =
      (2 * (q : ℝ) - 1) * ((q : ℝ) ^ (d + 1) * q ^ d) := by
    rw [hfac]
    simp only [mul_pow, pow_succ]
    field_simp
    ring
  have hright : ((m : ℝ) * (2 * q - 1) ^ (d + 1) / (d + 1).factorial) *
      (d + 1).factorial = m * (2 * (q : ℝ) - 1) ^ (d + 1) := by
    exact div_mul_cancel₀ _ hg
  have hscaled : (2 * (q : ℝ) - 1) * ((q : ℝ) ^ (d + 1) * q ^ d) ≤
      m * (2 * (q : ℝ) - 1) ^ (d + 1) := by
    rw [← halg, ← hright]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have hcancel : (q : ℝ) ^ (d + 1) * q ^ d ≤ m * (2 * (q : ℝ) - 1) ^ d := by
    apply (mul_le_mul_iff_right₀ ht).mp
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hscaled
  apply (div_le_iff₀ (pow_pos hbase d)).mpr
  apply (mul_le_mul_iff_right₀ (pow_pos hqR d)).mp
  have hid : (2 - 1 / (q : ℝ)) ^ d * q ^ d = (2 * (q : ℝ) - 1) ^ d := by
    rw [← mul_pow]
    congr 1
    field_simp
  calc
    (q : ℝ) ^ d * q ^ (d + 1) = (q : ℝ) ^ (d + 1) * q ^ d := mul_comm _ _
    _ ≤ m * (2 * (q : ℝ) - 1) ^ d := hcancel
    _ = (q : ℝ) ^ d * ((m : ℝ) * (2 - 1 / (q : ℝ)) ^ d) := by
      rw [mul_comm ((q : ℝ) ^ d), mul_assoc, hid]

lemma sharp_bound_of_counting_rat (q d m : ℕ) (hq : 2 ≤ q) (h : CountingBound q d m) :
    (q : ℚ) ^ (d + 1) / (2 - 1 / (q : ℚ)) ^ d ≤ m := by
  apply (Rat.cast_le (K := ℝ)).mp
  push_cast
  exact sharp_bound_of_counting q d m hq h

end FCP.Kakeya.SharpCounting


namespace FCP.Kakeya.SharpRank

/-- Independent monomials cannot outnumber a family of linear conditions that detects every
polynomial supported on those monomials. -/
lemma card_monomials_le_conditions {F σ I : Type*} [Field F] [Fintype I]
    (A : Finset (σ →₀ ℕ)) (L : MvPolynomial σ F →ₗ[F] (I → F))
    (hdetect : ∀ P : MvPolynomial σ F, (∀ a ∈ P.support, a ∈ A) → L P = 0 → P = 0) :
    A.card ≤ Fintype.card I := by
  classical
  let V := MvPolynomial.restrictSupport F (A : Set (σ →₀ ℕ))
  let b := MvPolynomial.basisRestrictSupport F (A : Set (σ →₀ ℕ))
  let T : V →ₗ[F] (I → F) := L.comp V.subtype
  have hinj : Function.Injective T := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro P hP
    apply Subtype.ext
    apply hdetect P.1
    · exact P.2
    · exact hP
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  have hv : Module.finrank F V = A.card := by
    simpa [V, b] using Module.finrank_eq_card_basis b
  simpa only [hv, Module.finrank_fintype_fun_eq_card] using hdim

end FCP.Kakeya.SharpRank


/- Hasse proof lemmas reused from the frozen F3 implementation (commit
3a6837690e730ea6f2da42b2f04073fa399e07bf), with task-local names. The
underlying definitions are imported unchanged from the canonical model. -/
namespace FCP.Kakeya.SharpHasse
open MvPolynomial KakeyaHasse
variable {σ R : Type*} [Fintype σ] [CommSemiring R]

@[simp] theorem coeff_hasse (i b : σ →₀ ℕ) (P : MvPolynomial σ R) :
    (hasse i P).coeff b = multiChoose (b + i) i * P.coeff (b + i) := rfl

@[simp] theorem hasse_zero (i : σ →₀ ℕ) : hasse i (0 : MvPolynomial σ R) = 0 := by
  ext b
  simp only [coeff_hasse, coeff_zero, mul_zero]

@[simp] theorem hasse_add (i : σ →₀ ℕ) (P Q : MvPolynomial σ R) :
    hasse i (P + Q) = hasse i P + hasse i Q := by
  ext b
  simp only [coeff_hasse, coeff_add, mul_add]

@[simp] theorem hasse_smul (i : σ →₀ ℕ) (c : R) (P : MvPolynomial σ R) :
    hasse i (c • P) = c • hasse i P := by
  ext b
  simp only [coeff_hasse, coeff_smul, smul_eq_mul]
  ring

@[simp] theorem hasse_zero_index (P : MvPolynomial σ R) : hasse 0 P = P := by
  ext b
  simp only [coeff_hasse, add_zero, multiChoose, Finsupp.zero_apply, Nat.choose_zero_right, Nat.cast_one,
    Finset.prod_const_one, one_mul]

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
  rw [coeff_hasse, coeff_C_of_ne_zero hbi, mul_zero, coeff_zero]

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

end FCP.Kakeya.SharpHasse

namespace FCP.Kakeya.SharpJets
open MvPolynomial
variable {F σ : Type*} [Field F]

/-- Restriction to an affine line, bundled to expose its linearity. -/
noncomputable def lineMap (a b : σ → F) : MvPolynomial σ F →ₐ[F] Polynomial F :=
  MvPolynomial.aeval (fun j => Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j))

lemma lineMap_shift (a b p : σ → F) (P : MvPolynomial σ F) :
    lineMap a b (SharpHasse.shift p P) = lineMap (a + p) b P := by
  let T : MvPolynomial σ F →ₐ[F] MvPolynomial σ F :=
    MvPolynomial.aeval (fun j => X j + C (p j))
  have h : (lineMap a b).comp T = lineMap (a + p) b := by
    ext j
    simp [lineMap, T]
    ring
  exact DFunLike.congr_fun h P

lemma taylor_lineMap (a b : σ → F) (t : F) (P : MvPolynomial σ F) :
    Polynomial.taylor t (lineMap a b P) = lineMap (a + t • b) b P := by
  have h : (Polynomial.aeval (Polynomial.X + Polynomial.C t)).comp (lineMap a b) =
      lineMap (a + t • b) b := by
    ext j
    simp [lineMap, Polynomial.aeval_def]
    ring
  exact DFunLike.congr_fun h P

lemma lineMap_zero_monomial (b : σ → F) (a : σ →₀ ℕ) (c : F) :
    lineMap 0 b (monomial a c) =
      Polynomial.monomial (KakeyaHasse.order a) (c * a.prod (fun j k => b j ^ k)) := by
  classical
  simp only [lineMap, MvPolynomial.aeval_monomial, Pi.zero_apply, Polynomial.C_0,
    zero_add, Polynomial.algebraMap_apply]
  have hp : ∀ s : Finset σ,
      (∏ j ∈ s, (Polynomial.X * Polynomial.C (b j)) ^ a j) =
        Polynomial.monomial (∑ j ∈ s, a j) (∏ j ∈ s, b j ^ a j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      simp only [Finset.prod_insert hj, Finset.sum_insert hj]
      rw [ih, mul_pow, ← Polynomial.C_pow]
      rw [mul_comm (Polynomial.X ^ a j), Polynomial.C_mul_X_pow_eq_monomial,
        Polynomial.monomial_mul_monomial]
  rw [Finsupp.prod, hp, Polynomial.C_mul_monomial]
  rfl

lemma coeff_lineMap_zero (b : σ → F) (P : MvPolynomial σ F) (k : ℕ)
    (hP : ∀ a, KakeyaHasse.order a = k → P.coeff a = 0) :
    (lineMap 0 b P).coeff k = 0 := by
  classical
  rw [P.as_sum, map_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro a ha
  rw [lineMap_zero_monomial, Polynomial.coeff_monomial]
  split_ifs with hk
  · rw [hP a hk, zero_mul]
  · rfl

variable [Fintype σ]

/-- Pointwise Taylor coefficients of low total order control all mixed line coefficients
of the same order, independently of the line direction. -/
lemma low_point_jet_implies_low_line_jet (a b : σ → F) (t : F)
    (P : MvPolynomial σ F) (i : σ →₀ ℕ) (j M : ℕ)
    (hP : ∀ α, KakeyaHasse.order α < M →
      (SharpHasse.shift (a + t • b) P).coeff α = 0)
    (hij : KakeyaHasse.order i + j < M) :
    (Polynomial.taylor t (lineMap a b (KakeyaHasse.hasse i P))).coeff j = 0 := by
  rw [taylor_lineMap]
  have hs := lineMap_shift (0 : σ → F) b (a + t • b) (KakeyaHasse.hasse i P)
  simp only [zero_add] at hs
  rw [← hs, ← SharpHasse.hasse_shift]
  apply coeff_lineMap_zero
  intro α hα
  apply SharpHasse.low_coeff_hasse i _ M hP α
  omega

end FCP.Kakeya.SharpJets


namespace FCP.Kakeya.SharpInterpolation
open SharpCounting SharpJets

noncomputable def transverseIndex {d : ℕ} (i : Fin d → ℕ) : Fin (d + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cons 0 i)

lemma order_transverseIndex {d : ℕ} (i : Fin d → ℕ) :
    KakeyaHasse.order (transverseIndex i) = ∑ j, i j := by
  rw [KakeyaHasse.order, ← funsum_eq]
  simp [transverseIndex, Fin.sum_univ_succ]

noncomputable def admissibleMonomials (d R D : ℕ) : Finset (Fin (d + 1) →₀ ℕ) :=
  (anisotropicExponents d R D).image Finsupp.equivFunOnFinite.symm

lemma card_admissibleMonomials (d R D : ℕ) :
    (admissibleMonomials d R D).card = (anisotropicExponents d R D).card := by
  classical
  exact Finset.card_image_of_injective _ (Equiv.injective _)

lemma mem_admissibleMonomials (d R D : ℕ) (hR : 0 < R) (α : Fin (d + 1) →₀ ℕ) :
    α ∈ admissibleMonomials d R D ↔
      (∑ j : Fin d, α j.succ) < R ∧ KakeyaHasse.order α < D := by
  classical
  simp only [admissibleMonomials, Finset.mem_image]
  constructor
  · rintro ⟨f,hf,rfl⟩
    have ht := (mem_anisotropicExponents d R D hR f).mp hf
    simpa [KakeyaHasse.order, ← funsum_eq] using ht
  · intro h
    refine ⟨Finsupp.equivFunOnFinite α, ?_, Equiv.symm_apply_apply _ _⟩
    apply (mem_anisotropicExponents d R D hR _).mpr
    simpa [KakeyaHasse.order, ← funsum_eq] using h

section Field
variable {F : Type*} [Field F] [Fintype F] {d : ℕ}

abbrev ConditionIndex (K : Finset (Fin (d + 1) → F)) (r rp q : ℕ) :=
  (↥K × ↥(monoLe (d + 1) (rp - 1))) ⊕
    ((Fin d → F) × F × ↥(highIndices d r rp q))

noncomputable def lowJet (p : Fin (d + 1) → F) (α : Fin (d + 1) →₀ ℕ) :
    MvPolynomial (Fin (d + 1)) F →ₗ[F] F :=
  (MvPolynomial.lcoeff F α).comp
    (MvPolynomial.aeval (fun j => MvPolynomial.X j + MvPolynomial.C (p j))).toLinearMap

noncomputable def mixedJet (a : Fin (d + 1) → F) (b : Fin d → F)
    (t : F) (i : Fin d → ℕ) (j : ℕ) : MvPolynomial (Fin (d + 1)) F →ₗ[F] F :=
  (Polynomial.lcoeff F j).comp ((Polynomial.taylor t).comp
    ((lineMap a (Fin.cons 1 b)).toLinearMap.comp (SharpHasse.hasseLinear (transverseIndex i))))

noncomputable def conditionsMap (K : Finset (Fin (d + 1) → F)) (r rp q : ℕ)
    (a : (Fin d → F) → (Fin (d + 1) → F)) :
    MvPolynomial (Fin (d + 1)) F →ₗ[F] (ConditionIndex K r rp q → F) :=
  LinearMap.pi (fun z => match z with
    | Sum.inl z => lowJet z.1.1 z.2.1
    | Sum.inr z => mixedJet (a z.1) z.1 z.2.1 z.2.2.1.1 z.2.2.1.2)

omit [Field F] in
lemma card_conditionIndex (K : Finset (Fin (d + 1) → F)) (r rp q : ℕ) :
    Fintype.card (ConditionIndex K r rp q) =
      K.card * (rp - 1 + (d + 1)).choose (d + 1) +
        Fintype.card F ^ (d + 1) * (highIndices d r rp q).card := by
  classical
  simp [ConditionIndex, card_monoLe, pow_succ, Nat.mul_assoc]

/-- The full mixed-jet detection statement supplied by the polynomial argument (source Lemma 9). -/
def FullJetDetection (r rp q : ℕ)
    (a : (Fin d → F) → (Fin (d + 1) → F)) : Prop :=
  ∀ P : MvPolynomial (Fin (d + 1)) F,
    (∀ α ∈ P.support, (∑ j : Fin d, α j.succ) < r * q ∧
      KakeyaHasse.order α < rp * q) →
    (∀ (b : Fin d → F) (t : F) (i : Fin d → ℕ), (∑ k, i k) < r →
      ∀ j : ℕ, j < rp - (∑ k, i k) / q → mixedJet (a b) b t i j P = 0) → P = 0

omit [Fintype F] in
lemma conditions_detect (K : Finset (Fin (d + 1) → F)) (r rp q : ℕ)
    (hr : 0 < r) (hrrp : r ≤ rp) (hq : 0 < q)
    (a : (Fin d → F) → (Fin (d + 1) → F))
    (ha : ∀ (b : Fin d → F) (t : F), a b + t • (Fin.cons 1 b : Fin (d + 1) → F) ∈ K)
    (hdetect : FullJetDetection r rp q a)
    (P : MvPolynomial (Fin (d + 1)) F)
    (hsupp : ∀ α ∈ P.support, α ∈ admissibleMonomials d (r * q) (rp * q))
    (hzero : conditionsMap K r rp q a P = 0) : P = 0 := by
  classical
  apply hdetect P
  · intro α hα
    exact (mem_admissibleMonomials d _ _ (Nat.mul_pos hr hq) α).mp (hsupp α hα)
  · intro b t i hi j hj
    by_cases hhigh : rp ≤ (∑ k, i k) + j
    · have hm : (⟨i,j⟩ : Σ _i : Fin d → ℕ, ℕ) ∈ highIndices d r rp q :=
        (mem_highIndices d r rp q hr hrrp i j).mpr ⟨hi,hhigh,hj⟩
      exact congrFun hzero (Sum.inr ⟨b,t,⟨⟨i,j⟩,hm⟩⟩)
    · change (Polynomial.taylor t
        (lineMap (a b) (Fin.cons 1 b) (KakeyaHasse.hasse (transverseIndex i) P))).coeff j = 0
      apply low_point_jet_implies_low_line_jet (a b) (Fin.cons 1 b) t P
        (transverseIndex i) j rp
      · intro α hα
        have hm : α ∈ monoLe (d + 1) (rp - 1) := by
          apply (mem_monoLe α).mpr
          change KakeyaHasse.order α ≤ rp - 1
          omega
        exact congrFun hzero (Sum.inl ⟨⟨_,ha b t⟩,⟨α,hm⟩⟩)
      · rw [order_transverseIndex]
        omega

lemma finite_condition_bound (K : Finset (Fin (d + 1) → F)) (r rp q : ℕ)
    (hr : 0 < r) (hrrp : r ≤ rp) (hq : 0 < q)
    (a : (Fin d → F) → (Fin (d + 1) → F))
    (ha : ∀ (b : Fin d → F) (t : F), a b + t • (Fin.cons 1 b : Fin (d + 1) → F) ∈ K)
    (hdetect : FullJetDetection r rp q a) :
    (anisotropicExponents d (r * q) (rp * q)).card ≤
      K.card * (rp - 1 + (d + 1)).choose (d + 1) +
        Fintype.card F ^ (d + 1) * (highIndices d r rp q).card := by
  classical
  have h := SharpRank.card_monomials_le_conditions
    (admissibleMonomials d (r * q) (rp * q)) (conditionsMap K r rp q a)
    (conditions_detect K r rp q hr hrrp hq a ha hdetect)
  simpa only [card_admissibleMonomials, card_conditionIndex] using h

lemma countingBound_of_detection (K : Finset (Fin (d + 1) → F))
    (a : (Fin d → F) → (Fin (d + 1) → F))
    (ha : ∀ (b : Fin d → F) (t : F), a b + t • (Fin.cons 1 b : Fin (d + 1) → F) ∈ K)
    (hdetect : ∀ s : ℕ, 0 < s → FullJetDetection (Fintype.card F * s)
      ((2 * Fintype.card F - 1) * s) (Fintype.card F) a) :
    CountingBound (Fintype.card F) d K.card := by
  classical
  let q := Fintype.card F
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hq0 : 0 < q := by omega
  intro s hs
  let r := q * s
  let rp := (2 * q - 1) * s
  have hr : 0 < r := Nat.mul_pos hq0 hs
  have hrrp : r ≤ rp := Nat.mul_le_mul_right s (by omega)
  have hrp : 0 < rp := lt_of_lt_of_le hr hrrp
  have hN := finite_condition_bound K r rp q hr hrrp hq0 a ha (hdetect s hs)
  rw [card_anisotropicExponents d (r * q) (rp * q)
    (Nat.mul_pos hr hq0) (Nat.mul_le_mul_right q hrrp)] at hN
  have hNR : (((rp * q - r * q) * (r * q + d - 1).choose d +
      (r * q + d).choose (d + 1) : ℕ) : ℝ) ≤
      ((K.card * (rp - 1 + (d + 1)).choose (d + 1) +
        q ^ (d + 1) * (highIndices d r rp q).card : ℕ) : ℝ) := by
    exact_mod_cast hN
  push_cast at hNR
  have hB := card_highIndices_le d r rp q hr hrrp hq0
  have hB' := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ (q : ℝ) ^ (d + 1))
  have hbound := hNR.trans (add_le_add (le_refl
    ((K.card : ℝ) * ((rp - 1 + (d + 1)).choose (d + 1) : ℝ))) hB')
  have hR : r * q = q * q * s := by dsimp [r]; ring
  have hD : rp * q - r * q = (q - 1) * q * s := by
    rw [← Nat.sub_mul]
    change (((2 * q - 1) * s - q * s) * q) = _
    rw [← Nat.sub_mul]
    have ht : 2 * q - 1 - q = q - 1 := by omega
    rw [ht]
    ring
  have hL : rp - 1 + (d + 1) = rp + d := by omega
  have hcoeff : 1 - 1 / (q : ℝ) = ((q - 1 : ℕ) : ℝ) / q := by
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    field_simp
  rw [hD, hR, hL, hcoeff] at hbound
  exact hbound

end Field

variable {F : Type} [Field F] [Fintype F] {d : ℕ}

/-- Final reduction from the polynomial detection lemma to the original sharp inequality. -/
lemma sharp_succ_of_detection (K : Finset (Fin (d + 1) → F)) (hK : IsKakeyaFinite K)
    (hdetect : ∀ (a : (Fin d → F) → (Fin (d + 1) → F)) (s : ℕ), 0 < s →
      FullJetDetection (Fintype.card F * s) ((2 * Fintype.card F - 1) * s)
        (Fintype.card F) a) :
    (Fintype.card F : ℚ) ^ (d + 1) /
      (2 - 1 / (Fintype.card F : ℚ)) ^ d ≤ K.card := by
  classical
  have hlines : ∀ b : Fin d → F, ∃ a : Fin (d + 1) → F,
      ∀ t : F, a + t • (Fin.cons 1 b : Fin (d + 1) → F) ∈ K := by
    intro b
    apply hK
    intro hzero
    have hh := congrFun hzero 0
    simp at hh
  choose a ha using hlines
  exact sharp_bound_of_counting_rat (Fintype.card F) d K.card Fintype.one_lt_card
    (countingBound_of_detection K a ha (hdetect a))

end FCP.Kakeya.SharpInterpolation
/-- The original sharp finite-field Kakeya inequality. -/
theorem solution (F : Type) [Field F] [Fintype F] (n : ℕ) (hn : 0 < n)
    (K : Finset (Fin n → F)) (hK : FCP.Kakeya.IsKakeyaFinite K) :
    (Fintype.card F : ℚ) ^ n / (2 - 1 / Fintype.card F) ^ (n - 1) ≤ K.card := by
  classical
  cases n with
  | zero => omega
  | succ d =>
    change (Fintype.card F : ℚ) ^ (d + 1) /
      (2 - 1 / (Fintype.card F : ℚ)) ^ d ≤ K.card
    apply FCP.Kakeya.SharpInterpolation.sharp_succ_of_detection K hK
    intro a s hs P hsupport hjet
    apply FiniteFieldKakeya.mixed_line_jet_detection d
      (Fintype.card F * s) ((2 * Fintype.card F - 1) * s)
      (Nat.mul_pos Fintype.card_pos hs)
      (Nat.mul_le_mul_right s (by have := Fintype.one_lt_card (α := F); omega)) a P hsupport
    intro i hi b t j hj
    have hdeg := FCP.Kakeya.SharpCounting.funsum_eq d i
    have hh := hjet b t (fun k => i k) (by rw [hdeg]; exact hi) j
      (by rw [hdeg]; exact hj)
    have he : FCP.Kakeya.SharpInterpolation.transverseIndex (fun k => i k) = i.cons 0 := by
      ext k
      refine Fin.cases ?_ (fun l => ?_) k <;>
        simp [FCP.Kakeya.SharpInterpolation.transverseIndex]
    simpa [FCP.Kakeya.SharpInterpolation.mixedJet, he,
      FCP.Kakeya.SharpHasse.hasseLinear, FCP.Kakeya.SharpJets.lineMap,
      KakeyaPolynomialMethods.lineMap] using hh
