-- Prove2me | solution 1 for FourierEntropyApprox.theorem_3_2_item_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:04:06.363404+00:00
-- url     : https://prove2.me/submissions/16a55c02-ca8a-4fa4-a10a-8da2fa06886c

import Mathlib
import Definitions.Def_FourierEntropyApprox_fourierCoeff
import Definitions.Def_FourierEntropyApprox_majCompose

section
set_option autoImplicit false
namespace FourierEntropyApprox.Dev.Plancherel
open FourierEntropyApprox

lemma spin_mul_self (b : Bool) : spin b * spin b = 1 := by
  cases b <;> simp [spin]

lemma walsh_eq_ite {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    walsh S x = ∏ i, if i ∈ S then spin (x i) else 1 := by
  simp [walsh, Finset.prod_ite_mem]

lemma sum_walsh_mul {n : ℕ} (S T : Finset (Fin n)) :
    ∑ x : Cube n, walsh S x * walsh T x = if S = T then (2 : ℝ) ^ n else 0 := by
  have h : ∀ x : Cube n, walsh S x * walsh T x =
      ∏ i, ((if i ∈ S then spin (x i) else 1) * (if i ∈ T then spin (x i) else 1)) := by
    intro x
    rw [walsh_eq_ite, walsh_eq_ite, Finset.prod_mul_distrib]
  simp_rw [h]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum
    (fun (i : Fin n) => (Finset.univ : Finset Bool))
    (fun i b => (if i ∈ S then spin b else 1) * (if i ∈ T then spin b else 1))]
  have hf : ∀ i : Fin n, ∑ b : Bool, ((if i ∈ S then spin b else 1) * (if i ∈ T then spin b else 1))
      = if (i ∈ S ↔ i ∈ T) then 2 else 0 := by
    intro i
    by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ T <;> simp [h1, h2, spin] <;> norm_num
  simp_rw [hf]
  split_ifs with hST
  · subst hST; simp
  · obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      by_contra hc
      push Not at hc
      exact hST (Finset.ext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

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

/-- Orthogonality of characters. -/
lemma avg_walsh_mul (S T : Finset (Fin n)) :
    avg (fun x => (walsh S x : 𝕜) * (walsh T x : 𝕜)) = if S = T then 1 else 0 := by
  rw [avg_def]
  have h := sum_walsh_mul (n := n) S T
  have h' : ∑ x : Cube n, (walsh S x : 𝕜) * (walsh T x : 𝕜) =
      if S = T then (2 : 𝕜) ^ n else 0 := by
    have := congrArg (fun r : ℝ => (r : 𝕜)) h
    simp only [RCLike.ofReal_sum, RCLike.ofReal_mul] at this
    rw [this]; split_ifs <;> first | exact cast_two_pow | simp
  rw [h']
  split_ifs
  · exact inv_mul_cancel₀ two_pow_ne_zero
  · simp

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
namespace FourierEntropyApprox.Dev.Item2
open FourierEntropyApprox FourierEntropyApprox.Dev.Plancherel

variable {n : ℕ}

lemma fourierCoeff_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (g : ι → Cube n → ℝ)
    (U : Finset (Fin n)) :
    fourierCoeff (fun x => ∑ k ∈ s, c k * g k x) U = ∑ k ∈ s, c k * fourierCoeff (g k) U := by
  rw [fourierCoeff_def]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fourierCoeff_def, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [RCLike.ofReal_real_eq_id, id]
  ring

lemma spectralNorm_sum_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (g : ι → Cube n → ℝ) :
    spectralNorm (fun x => ∑ k ∈ s, c k * g k x) ≤ ∑ k ∈ s, |c k| * spectralNorm (g k) := by
  unfold spectralNorm
  simp_rw [fourierCoeff_sum, Finset.mul_sum]
  calc ∑ U : Finset (Fin n), ‖∑ k ∈ s, c k * fourierCoeff (g k) U‖
      ≤ ∑ U : Finset (Fin n), ∑ k ∈ s, |c k| * ‖fourierCoeff (g k) U‖ := by
        refine Finset.sum_le_sum fun U _ => ?_
        refine (norm_sum_le _ _).trans ?_
        refine le_of_eq (Finset.sum_congr rfl fun k _ => ?_)
        rw [norm_mul, Real.norm_eq_abs]
    _ = ∑ k ∈ s, ∑ U : Finset (Fin n), |c k| * ‖fourierCoeff (g k) U‖ := Finset.sum_comm

lemma walsh_mul (S T : Finset (Fin n)) (x : Cube n) :
    walsh S x * walsh T x = walsh (symmDiff S T) x := by
  rw [walsh_eq_ite, walsh_eq_ite, walsh_eq_ite, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have := spin_mul_self (x i)
  by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ T <;> simp [h1, h2, this, Finset.mem_symmDiff]

lemma spectralNorm_nonneg (P : Cube n → ℝ) : 0 ≤ spectralNorm P :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma spectralNorm_walsh (U : Finset (Fin n)) : spectralNorm (fun x => walsh U x) = 1 := by
  unfold spectralNorm
  have h : ∀ S : Finset (Fin n), fourierCoeff (fun x => walsh U x) S = if U = S then 1 else 0 := by
    intro S
    have := avg_walsh_mul (𝕜 := ℝ) U S
    simpa [fourierCoeff_def, avg_def] using this
  simp [h, apply_ite]

lemma spectralNorm_mul_le (g h : Cube n → ℝ) :
    spectralNorm (fun x => g x * h x) ≤ spectralNorm g * spectralNorm h := by
  have key : (fun x => g x * h x) = fun x =>
      ∑ p : Finset (Fin n) × Finset (Fin n),
        (fourierCoeff g p.1 * fourierCoeff h p.2) * walsh (symmDiff p.1 p.2) x := by
    funext x
    conv_lhs => rw [← fourier_inversion g x, ← fourier_inversion h x]
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← walsh_mul]
    simp only [RCLike.ofReal_real_eq_id, id]
    ring
  rw [key]
  have hs := spectralNorm_sum_le (Finset.univ : Finset (Finset (Fin n) × Finset (Fin n)))
    (fun p => fourierCoeff g p.1 * fourierCoeff h p.2) (fun p x => walsh (symmDiff p.1 p.2) x)
  refine hs.trans ?_
  simp_rw [spectralNorm_walsh, mul_one]
  unfold spectralNorm
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine le_of_eq (Finset.sum_congr rfl fun p _ => ?_)
  rw [abs_mul]
  simp [Real.norm_eq_abs]

lemma spectralNorm_one : spectralNorm (fun _ : Cube n => (1 : ℝ)) = 1 := by
  have := spectralNorm_walsh (n := n) ∅
  simpa [walsh] using this

lemma spectralNorm_pow_le (P : Cube n → ℝ) (k : ℕ) :
    spectralNorm (fun x => P x ^ k) ≤ spectralNorm P ^ k := by
  induction k with
  | zero => simp [spectralNorm_one]
  | succ k ih =>
    have := spectralNorm_mul_le (fun x => P x ^ k) P
    simp_rw [pow_succ]
    calc _ ≤ _ := this
      _ ≤ spectralNorm P ^ k * spectralNorm P := by
        exact mul_le_mul_of_nonneg_right ih (spectralNorm_nonneg P)

lemma norm_maj (t : ℕ) (y : Cube t) : ‖maj t y‖ = 1 := by
  unfold maj; split_ifs <;> simp

lemma sum_maj_sq (t : ℕ) : ∑ S : Finset (Fin t), ‖fourierCoeff (maj t) S‖ ^ 2 = 1 := by
  rw [← l2NormSq_eq_sum]
  unfold l2NormSq
  simp_rw [norm_maj]
  simp

lemma sum_pow_card (t : ℕ) (a : ℝ) :
    ∑ S : Finset (Fin t), a ^ S.card = (1 + a) ^ t := by
  have h := Finset.prod_one_add (s := (Finset.univ : Finset (Fin t))) (f := fun _ => a)
  rw [Finset.powerset_univ] at h
  simpa using h.symm

end FourierEntropyApprox.Dev.Item2

namespace FourierEntropyApprox
open FourierEntropyApprox.Dev.Item2 FourierEntropyApprox.Dev.Plancherel in
theorem chk_theorem_3_2_item_2 {n : ℕ} (P : Cube n → ℝ) (t : ℕ) :
    spectralNorm (majCompose t P) ≤ (1 + spectralNorm P ^ 2) ^ ((t : ℝ) / 2) := by
  set B := spectralNorm P with hB
  have hB0 : 0 ≤ B := spectralNorm_nonneg P
  have h1 : spectralNorm (majCompose t P) ≤ ∑ S : Finset (Fin t), ‖fourierCoeff (maj t) S‖ * B ^ S.card := by
    have := spectralNorm_sum_le (Finset.univ : Finset (Finset (Fin t)))
      (fun S => fourierCoeff (maj t) S) (fun S x => P x ^ S.card)
    refine this.trans (Finset.sum_le_sum fun S _ => ?_)
    rw [← Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (spectralNorm_pow_le P _) (norm_nonneg _)
  have h2 : (∑ S : Finset (Fin t), ‖fourierCoeff (maj t) S‖ * B ^ S.card) ^ 2 ≤ (1 + B ^ 2) ^ t := by
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
    rw [sum_maj_sq, one_mul, ← sum_pow_card]
    refine le_of_eq (Finset.sum_congr rfl fun S _ => ?_)
    rw [← pow_mul, mul_comm, pow_mul]
  have h3 : ((1 + B ^ 2) ^ ((t : ℝ) / 2)) ^ 2 = (1 + B ^ 2) ^ t := by
    rw [← Real.rpow_natCast ((1 + B ^ 2) ^ ((t : ℝ) / 2)) 2, ← Real.rpow_mul (by positivity)]
    have : (t : ℝ) / 2 * ((2 : ℕ) : ℝ) = (t : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast]
  have h4 : 0 ≤ (1 + B ^ 2) ^ ((t : ℝ) / 2) := by positivity
  refine h1.trans ?_
  exact le_of_sq_le_sq (h3 ▸ h2) h4
end FourierEntropyApprox
end

theorem solution : type_of% @FourierEntropyApprox.chk_theorem_3_2_item_2 := @FourierEntropyApprox.chk_theorem_3_2_item_2
