-- Prove2me | solution 1 for FockSPR.blocks_orthogonal_circle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:32.941685+00:00
-- url     : https://prove2.me/submissions/844b7735-0be1-4b6e-a0af-8519b09ba9e1

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
section
@[expose] public section
open Finset Nat Real MeasureTheory
noncomputable section
namespace FockSPR
private lemma freqBlock_unique {n ℓ₁ ℓ₂ : ℕ}
    (h1 : n ∈ freqBlock ℓ₁) (h2 : n ∈ freqBlock ℓ₂) : ℓ₁ = ℓ₂ := by
  simp only [freqBlock, Finset.mem_Icc] at h1 h2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have hsq : (ℓ₁ + 1) ^ 2 ≤ ℓ₂ ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hpos : 0 < (ℓ₁ + 1) ^ 2 := Nat.pos_of_ne_zero (by positivity)
    omega
  · have hsq : (ℓ₂ + 1) ^ 2 ≤ ℓ₁ ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hpos : 0 < (ℓ₂ + 1) ^ 2 := Nat.pos_of_ne_zero (by positivity)
    omega
private lemma fourier_pow (t : AddCircle T) (n : ℕ) :
    ((fourier 1 t : ℂ)) ^ n = (fourier (↑n : ℤ) t : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← fourier_add]; push_cast; ring
private lemma fourier_neg_pow (t : AddCircle T) (n : ℕ) :
    ((fourier (-1 : ℤ) t : ℂ)) ^ n = (fourier (-(↑n : ℤ)) t : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← fourier_add]; congr 1; push_cast; ring_nf
private lemma integral_fourier_ne_zero (k : ℤ) (hk : k ≠ 0) :
    ∫ t : AddCircle T, (fourier k t : ℂ) ∂AddCircle.haarAddCircle = 0 := by
  have h := congr_fun (fourierCoeff_fourier (T := T) 0) (-k)
  simp only [fourierCoeff, fourier_zero, Pi.single_apply, neg_neg, smul_eq_mul, mul_one] at h
  rwa [if_neg (by omega)] at h
private lemma addCircle_integrable {f : AddCircle T → ℂ} (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle :=
  integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)
private lemma continuous_term (c : ℂ) (r : ℝ) (n : ℕ) :
    Continuous (fun t : AddCircle T => c * ((↑r : ℂ) * (fourier 1 t : ℂ)) ^ n) :=
  continuous_const.mul (continuous_const.mul (fourier 1).continuous |>.pow n)
private lemma integrable_term {D : ℕ} (a : Fin D → ℂ) (ℓ₁ ℓ₂ : ℕ) (r : ℝ)
    (i j : Fin D) :
    Integrable (fun t : AddCircle T =>
      (if (i.val + 1) ∈ freqBlock ℓ₁
        then a i * ((↑r : ℂ) * (fourier 1 t : ℂ)) ^ (i.val + 1) else 0) *
      starRingEnd ℂ (if (j.val + 1) ∈ freqBlock ℓ₂
        then a j * ((↑r : ℂ) * (fourier 1 t : ℂ)) ^ (j.val + 1) else 0))
    AddCircle.haarAddCircle := by
  apply addCircle_integrable; apply Continuous.mul
  · split_ifs <;> [exact continuous_term _ _ _; exact continuous_const]
  · exact Complex.continuous_conj.comp
      (by split_ifs <;> [exact continuous_term _ _ _; exact continuous_const])
private lemma integral_cross_term_eq_zero {D : ℕ} (a : Fin D → ℂ) (r : ℝ)
    (k₁ k₂ : Fin D) (hne_k : (k₁.val + 1 : ℕ) ≠ k₂.val + 1) :
    ∫ t : AddCircle T,
      a k₁ * ((↑r : ℂ) * (fourier 1 t : ℂ)) ^ (k₁.val + 1) *
      (starRingEnd ℂ) (a k₂ * ((↑r : ℂ) * (fourier 1 t : ℂ)) ^ (k₂.val + 1))
      ∂AddCircle.haarAddCircle = 0 := by
  set c := a k₁ * starRingEnd ℂ (a k₂) *
    (↑r : ℂ) ^ (k₁.val + 1 + (k₂.val + 1))
  set m := (↑(k₁.val + 1) - ↑(k₂.val + 1) : ℤ) with hm_def
  have key : ∀ t : AddCircle T,
      a k₁ * ((↑r : ℂ) * (fourier 1 t : ℂ)) ^ (k₁.val + 1) *
      (starRingEnd ℂ) (a k₂ * ((↑r : ℂ) * (fourier 1 t : ℂ)) ^ (k₂.val + 1)) =
      c * (fourier m t : ℂ) := by
    intro t
    rw [map_mul (f := starRingEnd ℂ), map_pow (f := starRingEnd ℂ),
        map_mul (f := starRingEnd ℂ) (x := (↑r : ℂ)), Complex.conj_ofReal,
        ← fourier_neg (n := (1 : ℤ)),
        mul_pow (a := (↑r : ℂ)) (b := (fourier 1 t : ℂ)),
        mul_pow (a := (↑r : ℂ)) (b := (fourier (-1 : ℤ) t : ℂ)),
        fourier_pow t (k₁.val + 1), fourier_neg_pow t (k₂.val + 1)]
    simp only [c, m]
    calc a k₁ * ((↑r : ℂ) ^ (k₁.val + 1) *
            (fourier (↑(k₁.val + 1) : ℤ) t : ℂ)) *
          (starRingEnd ℂ (a k₂) * ((↑r : ℂ) ^ (k₂.val + 1) *
            (fourier (-(↑(k₂.val + 1) : ℤ)) t : ℂ)))
        = (a k₁ * starRingEnd ℂ (a k₂) *
            ((↑r : ℂ) ^ (k₁.val + 1) * (↑r : ℂ) ^ (k₂.val + 1))) *
          ((fourier (↑(k₁.val + 1) : ℤ) t : ℂ) *
            (fourier (-(↑(k₂.val + 1) : ℤ)) t : ℂ)) := by ring
      _ = (a k₁ * starRingEnd ℂ (a k₂) *
            (↑r : ℂ) ^ (k₁.val + 1 + (k₂.val + 1))) *
          (fourier (↑(k₁.val + 1) - ↑(k₂.val + 1) : ℤ) t : ℂ) := by
            rw [pow_add, ← fourier_add]; congr 1; ring
  simp_rw [key]
  have hm : m ≠ 0 := by simp only [m]; push_cast; omega
  have h_eq : ∫ t : AddCircle T, c * (fourier m t : ℂ)
      ∂AddCircle.haarAddCircle =
      c * ∫ t : AddCircle T, (fourier m t : ℂ) ∂AddCircle.haarAddCircle :=
    integral_const_mul c _
  rw [h_eq, integral_fourier_ne_zero m hm, mul_zero]
end FockSPR
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Nat Real MeasureTheory
noncomputable section
open FockSPR
namespace FockSPR
theorem _root_.solution {D : ℕ} (a : Fin D → ℂ) {ℓ₁ ℓ₂ : ℕ}
    (_h₁ : 1 ≤ ℓ₁) (_h₂ : 1 ≤ ℓ₂) (hne : ℓ₁ ≠ ℓ₂) (r : ℝ) (_hr : 0 ≤ r) :
    ∫ t : AddCircle T,
      (blockPoly a ℓ₁ (↑r * (fourier 1 t : ℂ))) *
      starRingEnd ℂ (blockPoly a ℓ₂ (↑r * (fourier 1 t : ℂ)))
      ∂AddCircle.haarAddCircle = 0 := by
  simp_rw [blockPoly, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun k₁ _ =>
    integrable_finsetSum _ (fun k₂ _ => integrable_term a ℓ₁ ℓ₂ r k₁ k₂))]
  apply Finset.sum_eq_zero; intro k₁ _
  rw [integral_finsetSum Finset.univ
    (fun k₂ _ => integrable_term a ℓ₁ ℓ₂ r k₁ k₂)]
  apply Finset.sum_eq_zero; intro k₂ _
  split_ifs with h₁' h₂'
  · -- Both conditions hold: use Fourier orthogonality
    exact integral_cross_term_eq_zero a r k₁ k₂
      (fun heq => hne (freqBlock_unique (heq ▸ h₁') h₂'))
  · simp [map_zero]
  · simp
  · simp
end FockSPR
