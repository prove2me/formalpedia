-- Prove2me | solution 1 for FourierEntropyApprox.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:04:06.448084+00:00
-- url     : https://prove2.me/submissions/5124d855-a63d-4311-b97d-e9cd598fa146

import Mathlib
import Definitions.Def_FourierEntropyApprox_fourierCoeff
import Definitions.Def_FourierEntropyApprox_entropyFun
import Definitions.Def_FourierEntropyApprox_Ka

section
set_option autoImplicit false
namespace FourierEntropyApprox.Dev.Plancherel
open FourierEntropyApprox

lemma spin_mul_self (b : Bool) : spin b * spin b = 1 := by
  cases b <;> simp [spin]

lemma sum_walsh_dual {n : ℕ} (x y : Cube n) :
    ∑ S : Finset (Fin n), walsh S x * walsh S y = if x = y then (2 : ℝ) ^ n else 0 := by
  have h : ∀ S : Finset (Fin n), walsh S x * walsh S y = ∏ i ∈ S, (spin (x i) * spin (y i)) := by
    intro S; unfold walsh; rw [Finset.prod_mul_distrib]
  simp_rw [h]
  have h2 := Finset.prod_one_add (s := (Finset.univ : Finset (Fin n))) (f := fun i => spin (x i) * spin (y i))
  rw [Finset.powerset_univ] at h2
  rw [← h2]
  split_ifs with hxy
  · subst hxy
    have : ∀ i : Fin n, 1 + spin (x i) * spin (x i) = 2 := by intro i; rw [spin_mul_self]; norm_num
    simp [this]
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hc; push Not at hc; exact hxy (funext hc)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    revert hi
    cases hx : x i <;> cases hy : y i <;> simp [spin]

section general
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

lemma avg_def (F : Cube n → 𝕜) : avg F = ((2 : 𝕜) ^ n)⁻¹ * ∑ x, F x := rfl

lemma fourierCoeff_def (f : Cube n → 𝕜) (S : Finset (Fin n)) :
    fourierCoeff f S = ((2 : 𝕜) ^ n)⁻¹ * ∑ x, f x * (walsh S x : 𝕜) := rfl

lemma cast_two_pow : (((2 : ℝ) ^ n : ℝ) : 𝕜) = (2 : 𝕜) ^ n := by rw [RCLike.ofReal_pow, RCLike.ofReal_ofNat]

lemma two_pow_ne_zero : ((2 : 𝕜) ^ n) ≠ 0 := pow_ne_zero _ two_ne_zero

/-- Fourier inversion `f x = ∑_S f̂(S) χ_S(x)`. -/
lemma fourier_inversion (f : Cube n → 𝕜) (x : Cube n) :
    ∑ S : Finset (Fin n), fourierCoeff f S * (walsh S x : 𝕜) = f x := by
  have hd : ∀ y : Cube n, ∑ S : Finset (Fin n), (walsh S y : 𝕜) * (walsh S x : 𝕜) =
      if y = x then (2 : 𝕜) ^ n else 0 := by
    intro y
    have := congrArg (fun r : ℝ => (r : 𝕜)) (sum_walsh_dual (n := n) y x)
    simp only [RCLike.ofReal_sum, RCLike.ofReal_mul] at this
    rw [this]; split_ifs <;> first | exact cast_two_pow | simp
  calc ∑ S : Finset (Fin n), fourierCoeff f S * (walsh S x : 𝕜)
      = ((2 : 𝕜) ^ n)⁻¹ * ∑ y, f y * ∑ S : Finset (Fin n), (walsh S y : 𝕜) * (walsh S x : 𝕜) := by
        simp_rw [fourierCoeff_def, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun S _ => by ring
    _ = f x := by
        simp_rw [hd]
        simp [mul_ite, Finset.sum_ite_eq']
        rw [mul_comm (f x), ← mul_assoc, inv_mul_cancel₀ two_pow_ne_zero, one_mul]

lemma star_fourierCoeff (f : Cube n → 𝕜) (S : Finset (Fin n)) :
    star (fourierCoeff f S) = ((2 : 𝕜) ^ n)⁻¹ * ∑ x, star (f x) * (walsh S x : 𝕜) := by
  rw [fourierCoeff_def]
  simp only [RCLike.star_def, map_mul, map_sum, map_inv₀, map_pow, map_ofNat, RCLike.conj_ofReal]

/-- Plancherel on the cube. -/
theorem plancherel (f g : Cube n → 𝕜) :
    cubeInner f g = ∑ S : Finset (Fin n), star (fourierCoeff f S) * fourierCoeff g S := by
  have h1 : ∀ x : Cube n, star (f x) * g x =
      ∑ S : Finset (Fin n), star (f x) * (fourierCoeff g S * (walsh S x : 𝕜)) := by
    intro x
    rw [← Finset.mul_sum, fourier_inversion]
  unfold cubeInner
  rw [avg_def]
  simp_rw [h1]
  simp_rw [star_fourierCoeff]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun x _ => ?_
  ring

lemma cubeInner_self (f : Cube n → 𝕜) : cubeInner f f = (l2NormSq f : 𝕜) := by
  unfold cubeInner l2NormSq avg
  simp only [RCLike.ofReal_mul, RCLike.ofReal_sum, RCLike.ofReal_pow, RCLike.ofReal_inv]
  congr 1
  · rw [RCLike.ofReal_ofNat]
  · refine Finset.sum_congr rfl fun x _ => ?_
    show (starRingEnd 𝕜) (f x) * f x = _
    rw [RCLike.conj_mul]

/-- Parseval: `‖f‖₂² = ∑_S ‖f̂(S)‖²`. -/
theorem l2NormSq_eq_sum (f : Cube n → 𝕜) :
    l2NormSq f = ∑ S : Finset (Fin n), ‖fourierCoeff f S‖ ^ 2 := by
  have h := plancherel f f
  rw [cubeInner_self] at h
  have h2 : ∀ S : Finset (Fin n), star (fourierCoeff f S) * fourierCoeff f S
      = ((‖fourierCoeff f S‖ ^ 2 : ℝ) : 𝕜) := by
    intro S
    rw [mul_comm]; simp [RCLike.mul_conj]
  simp_rw [h2] at h
  have h3 : ((l2NormSq f : ℝ) : 𝕜) = ((∑ S : Finset (Fin n), ‖fourierCoeff f S‖ ^ 2 : ℝ) : 𝕜) := by
    rw [h]; simp
  exact_mod_cast h3

end general
end FourierEntropyApprox.Dev.Plancherel

namespace FourierEntropyApprox
end FourierEntropyApprox
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace FourierEntropyApprox.Dev.Thm31
open FourierEntropyApprox

/-- Pointwise Gibbs-type bound. -/
lemma pt (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    Real.negMulLog (x ^ 2) ≤ 2 * (r * x) - 2 * x ^ 2 + 2 * x ^ 2 * (-Real.log r) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hr hx)
  rw [Real.log_div hr.ne' hx.ne'] at h
  have h2 : x ^ 2 * (Real.log r - Real.log x) ≤ x ^ 2 * (r / x - 1) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have e : x ^ 2 * (r / x - 1) = r * x - x ^ 2 := by field_simp
  rw [e] at h2
  rw [Real.negMulLog, Real.log_pow]
  push_cast
  nlinarith

lemma geom_le (N : ℕ) : ∑ k ∈ Finset.Ico 1 (N + 1), ((2 : ℝ) ^ k)⁻¹ ≤ 1 := by
  have : ∀ N : ℕ, ∑ k ∈ Finset.Ico 1 (N + 1), ((2 : ℝ) ^ k)⁻¹ = 1 - ((2 : ℝ) ^ N)⁻¹ := by
    intro N
    induction N with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      have : ((2 : ℝ) ^ (m + 1))⁻¹ = ((2 : ℝ) ^ m)⁻¹ / 2 := by
        rw [pow_succ]; field_simp
      rw [this]; ring
  rw [this]
  have : 0 ≤ ((2 : ℝ) ^ N)⁻¹ := by positivity
  linarith

lemma ka_summable (a : ℝ) : Summable (fun j : ℕ => KaTerm a (j + 1)) := by
  set k := ⌈a⌉₊ with hk
  have h0 : Summable (fun n : ℕ => (n : ℝ) ^ k * (1 / 2 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k (by norm_num)
  have h1 : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ k * (1 / 2 : ℝ) ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr h0
  refine Summable.of_nonneg_of_le (fun j => by unfold KaTerm; positivity)
    (fun j => ?_) (h1.mul_left (4 ^ k))
  unfold KaTerm
  have hx : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) + 3 := by push_cast; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  have h2 : (((j + 1 : ℕ) : ℝ) + 3) ^ a ≤ (((j + 1 : ℕ) : ℝ) + 3) ^ (k : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (Nat.le_ceil a)
  rw [Real.rpow_natCast] at h2
  have h3 : (((j + 1 : ℕ) : ℝ) + 3) ≤ 4 * ((j + 1 : ℕ) : ℝ) := by
    push_cast; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  have h4 : (((j + 1 : ℕ) : ℝ) + 3) ^ k ≤ (4 * ((j + 1 : ℕ) : ℝ)) ^ k :=
    pow_le_pow_left₀ (by positivity) h3 k
  rw [mul_pow] at h4
  have h5 : ((2 : ℝ) ^ (j + 1))⁻¹ = (1 / 2 : ℝ) ^ (j + 1) := by rw [one_div, inv_pow]
  rw [h5]
  have h6 : 0 ≤ (1 / 2 : ℝ) ^ (j + 1) := by positivity
  calc (1 / 2 : ℝ) ^ (j + 1) * (((j + 1 : ℕ) : ℝ) + 3) ^ a
      ≤ (1 / 2 : ℝ) ^ (j + 1) * (4 ^ k * ((j + 1 : ℕ) : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (h2.trans h4) h6
    _ = 4 ^ k * (((j + 1 : ℕ) : ℝ) ^ k * (1 / 2 : ℝ) ^ (j + 1)) := by ring

section core
open Classical
variable {ι : Type*} [Fintype ι] (c : ι → ℂ) (p : ℕ → ι → ℂ)

def Good (j : ℕ) (S : ι) : Prop := c S ≠ 0 ∧ ‖c S - p (j + 2) S‖ ≤ ‖c S‖ / 2

noncomputable def idx (S : ι) : ℕ :=
  if h : ∃ j, 1 ≤ j ∧ Good c p j S then Nat.find h else 0

lemma idx_spec {S : ι} (h : ∃ j, 1 ≤ j ∧ Good c p j S) :
    1 ≤ idx c p S ∧ Good c p (idx c p S) S := by
  unfold idx; rw [dif_pos h]; exact Nat.find_spec h

lemma idx_min {S : ι} (h : ∃ j, 1 ≤ j ∧ Good c p j S) {k : ℕ} (hk : k < idx c p S)
    (hk1 : 1 ≤ k) : ¬ Good c p k S := by
  unfold idx at hk; rw [dif_pos h] at hk
  intro hg; exact Nat.find_min h hk ⟨hk1, hg⟩

lemma exists_good (hD : ∀ j, 1 ≤ j → ∑ S, ‖c S - p j S‖ ^ 2 ≤ ((2 : ℝ) ^ j)⁻¹)
    {S : ι} (hS : c S ≠ 0) : ∃ j, 1 ≤ j ∧ Good c p j S := by
  have hpos : 0 < ‖c S‖ ^ 2 := by have := norm_pos_iff.mpr hS; positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨max m 1, le_max_right _ _, hS, ?_⟩
  have h1 := hD (max m 1 + 2) (by omega)
  have h2 : ‖c S - p (max m 1 + 2) S‖ ^ 2 ≤ ∑ T, ‖c T - p (max m 1 + 2) T‖ ^ 2 :=
    Finset.single_le_sum (f := fun T => ‖c T - p (max m 1 + 2) T‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ S)
  have h3 : ((2 : ℝ) ^ (max m 1 + 2))⁻¹ ≤ (1 / 2 : ℝ) ^ m / 4 := by
    have : ((2 : ℝ) ^ (max m 1 + 2))⁻¹ = (1 / 2 : ℝ) ^ (max m 1) / 4 := by
      rw [pow_add, one_div, inv_pow]; field_simp; norm_num
    rw [this]
    have : (1 / 2 : ℝ) ^ (max m 1) ≤ (1 / 2 : ℝ) ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left _ _)
    linarith
  have h4 : ‖c S - p (max m 1 + 2) S‖ ^ 2 ≤ (‖c S‖ / 2) ^ 2 := by nlinarith
  exact le_of_sq_le_sq (by simpa using h4) (by positivity) |>.trans (le_refl _)

lemma good_le {S : ι} {j : ℕ} (h : Good c p j S) : ‖c S‖ ≤ 2 * ‖p (j + 2) S‖ := by
  have := norm_sub_norm_le (c S) (p (j + 2) S)
  have := h.2
  linarith

variable (hD : ∀ j, 1 ≤ j → ∑ S, ‖c S - p j S‖ ^ 2 ≤ ((2 : ℝ) ^ j)⁻¹)

/-- The set of nonzero coefficients. -/
noncomputable def Zs : Finset ι := Finset.univ.filter (fun S => c S ≠ 0)

include hD in
lemma tail (k : ℕ) (hk : 1 ≤ k) :
    ∑ S ∈ (Zs c).filter (fun S => k < idx c p S), ‖c S‖ ^ 2 ≤ ((2 : ℝ) ^ k)⁻¹ := by
  have h1 : ∀ S ∈ (Zs c).filter (fun S => k < idx c p S),
      ‖c S‖ ^ 2 ≤ 4 * ‖c S - p (k + 2) S‖ ^ 2 := by
    intro S hS
    simp only [Zs, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    have hng := idx_min c p (exists_good c p hD hS.1) hS.2 hk
    have : ‖c S‖ / 2 < ‖c S - p (k + 2) S‖ := by
      by_contra hh; exact hng ⟨hS.1, not_lt.mp hh⟩
    have h0 : 0 ≤ ‖c S‖ := norm_nonneg _
    nlinarith
  calc ∑ S ∈ (Zs c).filter (fun S => k < idx c p S), ‖c S‖ ^ 2
      ≤ ∑ S ∈ (Zs c).filter (fun S => k < idx c p S), 4 * ‖c S - p (k + 2) S‖ ^ 2 :=
        Finset.sum_le_sum h1
    _ = 4 * ∑ S ∈ (Zs c).filter (fun S => k < idx c p S), ‖c S - p (k + 2) S‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ 4 * ∑ S, ‖c S - p (k + 2) S‖ ^ 2 := by
        gcongr
        intro S _; exact Finset.mem_univ S
    _ ≤ 4 * ((2 : ℝ) ^ (k + 2))⁻¹ := by gcongr; exact hD (k + 2) (by omega)
    _ = ((2 : ℝ) ^ k)⁻¹ := by rw [pow_add]; field_simp; norm_num


section core2

/-- Largest index. -/
noncomputable def Nmax : ℕ := Finset.univ.sup (idx c p)

include hD in
lemma idx_mem {S : ι} (hS : S ∈ Zs c) : idx c p S ∈ Finset.Ico 1 (Nmax c p + 1) := by
  have hS' : c S ≠ 0 := by simpa [Zs] using hS
  have h1 := (idx_spec c p (exists_good c p hD hS')).1
  have h2 : idx c p S ≤ Nmax c p := Finset.le_sup (f := idx c p) (Finset.mem_univ S)
  simp only [Finset.mem_Ico]; omega

include hD in
lemma fiber_sum (F : ι → ℝ) :
    ∑ S ∈ Zs c, F S = ∑ j ∈ Finset.Ico 1 (Nmax c p + 1),
      ∑ S ∈ (Zs c).filter (fun S => idx c p S = j), F S :=
  (Finset.sum_fiberwise_of_maps_to (g := idx c p) (fun S hS => idx_mem c p hD hS) F).symm

lemma rho_le (hρ : ∑ S, ‖c S‖ ^ 2 ≤ 1) : ∑ S ∈ Zs c, ‖c S‖ ^ 2 ≤ 1 :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => by positivity)) hρ

include hD in
lemma mu_le (hρ : ∑ S, ‖c S‖ ^ 2 ≤ 1) (j : ℕ) (hj : 1 ≤ j) :
    ∑ S ∈ (Zs c).filter (fun S => idx c p S = j), ‖c S‖ ^ 2 ≤ 2 * ((2 : ℝ) ^ j)⁻¹ := by
  rcases Nat.eq_or_lt_of_le hj with h | h
  · subst h
    calc _ ≤ ∑ S ∈ Zs c, ‖c S‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
      _ ≤ 1 := rho_le c hρ
      _ = 2 * ((2 : ℝ) ^ 1)⁻¹ := by norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    calc _ ≤ ∑ S ∈ (Zs c).filter (fun S => k < idx c p S), ‖c S‖ ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro S hS
            simp only [Finset.mem_filter] at hS ⊢
            exact ⟨hS.1, by omega⟩
          · intro _ _ _; positivity
      _ ≤ ((2 : ℝ) ^ k)⁻¹ := tail c p hD k (by omega)
      _ = 2 * ((2 : ℝ) ^ (k + 1))⁻¹ := by rw [pow_succ]; field_simp

/-- The weight `r_j`. -/
noncomputable def Bf (j : ℕ) : ℝ := max 1 (∑ S, ‖p (j + 2) S‖)

lemma Bf_pos (j : ℕ) : 0 < Bf p j := lt_of_lt_of_le one_pos (le_max_left _ _)

noncomputable def rr (j : ℕ) : ℝ := ((2 : ℝ) ^ j)⁻¹ / (2 * Bf p j)

lemma rr_pos (j : ℕ) : 0 < rr p j := by
  have := Bf_pos p j
  unfold rr; positivity

include hD in
lemma T1 : ∑ S ∈ Zs c, rr p (idx c p S) * ‖c S‖ ≤ 1 := by
  rw [fiber_sum c p hD]
  refine le_trans (Finset.sum_le_sum (g := fun j => ((2 : ℝ) ^ j)⁻¹) ?_) (geom_le _)
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
  have e : ∑ S ∈ (Zs c).filter (fun S => idx c p S = j), rr p (idx c p S) * ‖c S‖
      = rr p j * ∑ S ∈ (Zs c).filter (fun S => idx c p S = j), ‖c S‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [(Finset.mem_filter.mp hS).2]
  rw [e]
  have h2 : ∑ S ∈ (Zs c).filter (fun S => idx c p S = j), ‖c S‖ ≤ 2 * Bf p j := by
    have h3 : ∀ S ∈ (Zs c).filter (fun S => idx c p S = j), ‖c S‖ ≤ 2 * ‖p (j + 2) S‖ := by
      intro S hS
      have hS' := Finset.mem_filter.mp hS
      have hc : c S ≠ 0 := by simpa [Zs] using hS'.1
      have := good_le c p (idx_spec c p (exists_good c p hD hc)).2
      rwa [hS'.2] at this
    calc _ ≤ ∑ S ∈ (Zs c).filter (fun S => idx c p S = j), 2 * ‖p (j + 2) S‖ :=
          Finset.sum_le_sum h3
      _ = 2 * ∑ S ∈ (Zs c).filter (fun S => idx c p S = j), ‖p (j + 2) S‖ := by
          rw [Finset.mul_sum]
      _ ≤ 2 * ∑ S, ‖p (j + 2) S‖ := by
          gcongr
          intro S _; exact Finset.mem_univ S
      _ ≤ 2 * Bf p j := by gcongr; exact le_max_right _ _
  calc rr p j * _ ≤ rr p j * (2 * Bf p j) := by
        exact mul_le_mul_of_nonneg_left h2 (rr_pos p j).le
    _ = ((2 : ℝ) ^ j)⁻¹ := by
        have := Bf_pos p j
        unfold rr; field_simp

lemma idx_eq (m N : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ N) :
    (m : ℝ) = 1 + ∑ k ∈ Finset.Ico 1 (N + 1), (if k < m then (1 : ℝ) else 0) := by
  rw [Finset.sum_boole]
  have : (Finset.Ico 1 (N + 1)).filter (fun k => k < m) = Finset.Ico 1 m := by
    ext k; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
  rw [this, Nat.card_Ico]
  push_cast [Nat.cast_sub h1]; ring

include hD in
lemma T3 (hρ : ∑ S, ‖c S‖ ^ 2 ≤ 1) :
    ∑ S ∈ Zs c, ‖c S‖ ^ 2 * (idx c p S : ℝ) ≤ (∑ S ∈ Zs c, ‖c S‖ ^ 2) + 1 := by
  have h1 : ∀ S ∈ Zs c, ‖c S‖ ^ 2 * (idx c p S : ℝ) = ‖c S‖ ^ 2 +
      ∑ k ∈ Finset.Ico 1 (Nmax c p + 1), (if k < idx c p S then ‖c S‖ ^ 2 else 0) := by
    intro S hS
    have hm := Finset.mem_Ico.mp (idx_mem c p hD hS)
    rw [idx_eq (idx c p S) (Nmax c p) hm.1 (by omega), mul_add, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_comm]
  gcongr
  calc ∑ k ∈ Finset.Ico 1 (Nmax c p + 1), ∑ S ∈ Zs c, (if k < idx c p S then ‖c S‖ ^ 2 else 0)
      = ∑ k ∈ Finset.Ico 1 (Nmax c p + 1),
          ∑ S ∈ (Zs c).filter (fun S => k < idx c p S), ‖c S‖ ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_filter]
    _ ≤ ∑ k ∈ Finset.Ico 1 (Nmax c p + 1), ((2 : ℝ) ^ k)⁻¹ := by
        refine Finset.sum_le_sum fun k hk => ?_
        exact tail c p hD k (Finset.mem_Ico.mp hk).1
    _ ≤ 1 := geom_le _

include hD in
lemma T4 (hρ : ∑ S, ‖c S‖ ^ 2 ≤ 1) (a : ℝ) (hK : Summable (fun j : ℕ => KaTerm a (j + 1))) :
    ∑ S ∈ Zs c, ‖c S‖ ^ 2 * ((idx c p S : ℝ) + 3) ^ a ≤ 2 * Ka a := by
  rw [fiber_sum c p hD]
  have h1 : ∀ j ∈ Finset.Ico 1 (Nmax c p + 1),
      ∑ S ∈ (Zs c).filter (fun S => idx c p S = j), ‖c S‖ ^ 2 * ((idx c p S : ℝ) + 3) ^ a
      ≤ 2 * KaTerm a j := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have e : ∑ S ∈ (Zs c).filter (fun S => idx c p S = j), ‖c S‖ ^ 2 * ((idx c p S : ℝ) + 3) ^ a
        = (∑ S ∈ (Zs c).filter (fun S => idx c p S = j), ‖c S‖ ^ 2) * ((j : ℝ) + 3) ^ a := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [(Finset.mem_filter.mp hS).2]
    rw [e]
    have := mu_le c p hD hρ j hj1
    have hpos : 0 ≤ ((j : ℝ) + 3) ^ a := by positivity
    unfold KaTerm
    nlinarith
  refine le_trans (Finset.sum_le_sum h1) ?_
  rw [← Finset.mul_sum]
  gcongr
  rw [Finset.sum_Ico_eq_sum_range]
  have : ∑ k ∈ Finset.range (Nmax c p + 1 - 1), KaTerm a (1 + k)
      = ∑ k ∈ Finset.range (Nmax c p), KaTerm a (k + 1) := by
    simp [add_comm]
  rw [this]
  exact Summable.sum_le_tsum _ (fun k _ => by unfold KaTerm; positivity) hK

end core2

include hD in
theorem core (a C L : ℝ) (hC : 0 < C) (hL : 1 ≤ L) (hρ : ∑ S, ‖c S‖ ^ 2 ≤ 1)
    (hB : ∀ j : ℕ, 1 ≤ j → Real.logb 2 (max 1 (∑ S, ‖p j S‖)) ≤ C * L * ((j : ℝ) + 1) ^ a)
    (hK : Summable (fun j : ℕ => KaTerm a (j + 1))) :
    ∑ S, Real.negMulLog (‖c S‖ ^ 2) / Real.log 2 ≤ 6 + 4 * C * Ka a * L := by
  set t := Real.log 2 with ht
  have ht2 : 1 / 2 < t := by have := Real.log_two_gt_d9; linarith
  have ht0 : 0 < t := by linarith
  have hsum : ∑ S, Real.negMulLog (‖c S‖ ^ 2) = ∑ S ∈ Zs c, Real.negMulLog (‖c S‖ ^ 2) := by
    unfold Zs
    rw [Finset.sum_filter_of_ne]
    intro S _ h hc
    apply h; rw [hc]; simp
  have hpt : ∀ S ∈ Zs c, Real.negMulLog (‖c S‖ ^ 2) ≤
      2 * (rr p (idx c p S) * ‖c S‖) - 2 * ‖c S‖ ^ 2 + 2 * t * (‖c S‖ ^ 2 * (idx c p S : ℝ))
        + 2 * t * ‖c S‖ ^ 2
        + 2 * t * C * L * (‖c S‖ ^ 2 * ((idx c p S : ℝ) + 3) ^ a) := by
    intro S hS
    have hc : c S ≠ 0 := by simpa [Zs] using hS
    have hx : 0 < ‖c S‖ := norm_pos_iff.mpr hc
    set j := idx c p S with hj
    have h1 := pt (‖c S‖) (rr p j) hx (rr_pos p j)
    have hBp := Bf_pos p j
    have hlog : -Real.log (rr p j) = (j : ℝ) * t + t + Real.log (Bf p j) := by
      unfold rr
      rw [Real.log_div (by positivity) (by positivity), Real.log_inv, Real.log_pow,
        Real.log_mul (by norm_num) hBp.ne']
      ring
    have hB' := hB (j + 2) (by omega)
    rw [Real.logb, div_le_iff₀ ht0] at hB'
    have hlogB : Real.log (Bf p j) ≤ C * L * ((j : ℝ) + 3) ^ a * t := by
      have : (((j + 2 : ℕ) : ℝ) + 1) = (j : ℝ) + 3 := by push_cast; ring
      rw [this] at hB'
      exact hB'
    rw [hlog] at h1
    have hx2 : 0 ≤ ‖c S‖ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hlogB hx2
    nlinarith
  have hT1 := T1 c p hD
  have hT3 := T3 c p hD hρ
  have hT4 := T4 c p hD hρ a hK
  have hr := rho_le c hρ
  have hCL : 0 ≤ C * L := by positivity
  have hS := Finset.sum_le_sum hpt
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hS
  rw [← Finset.sum_div, hsum, div_le_iff₀ ht0]
  have h5 := mul_le_mul_of_nonneg_left hT4 (by positivity : 0 ≤ 2 * t * C * L)
  have h6 := mul_le_mul_of_nonneg_left hT3 (by positivity : 0 ≤ 2 * t)
  nlinarith

end core
end FourierEntropyApprox.Dev.Thm31

namespace FourierEntropyApprox
open FourierEntropyApprox.Dev.Thm31 in
theorem chk_theorem_3_1 {n : ℕ} (f : Cube n → ℂ) (a C L : ℝ) (P : ℕ → Cube n → ℂ)
    (hf : l2NormSq f ≤ 1) (ha : 0 ≤ a) (hC : 0 < C) (hL : 1 ≤ L)
    (hP : ∀ j : ℕ, 1 ≤ j → l2NormSq (f - P j) ≤ ((2 : ℝ) ^ j)⁻¹ ∧
      Real.logb 2 (max 1 (spectralNorm (P j))) ≤ C * L * ((j : ℝ) + 1) ^ a) :
    entropyFun f ≤ 6 + 4 * C * Ka a * L := by
  have hsub : ∀ (j : ℕ) (S : Finset (Fin n)),
      fourierCoeff (f - P j) S = fourierCoeff f S - fourierCoeff (P j) S := by
    intro j S
    unfold fourierCoeff avg
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]
  refine core (fun S => fourierCoeff f S) (fun j S => fourierCoeff (P j) S) ?_ a C L hC hL ?_ ?_
    (ka_summable a)
  · intro j hj
    have := (hP j hj).1
    rw [FourierEntropyApprox.Dev.Plancherel.l2NormSq_eq_sum] at this
    simpa [hsub] using this
  · rw [← FourierEntropyApprox.Dev.Plancherel.l2NormSq_eq_sum]; exact hf
  · intro j hj; exact (hP j hj).2
end FourierEntropyApprox
end

theorem solution : type_of% @FourierEntropyApprox.chk_theorem_3_1 := @FourierEntropyApprox.chk_theorem_3_1
