-- Prove2me | solution 1 for CompressedSensingRadar.gabor_unit_norm_tight_frame
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T13:40:15.395103+00:00
-- url     : https://prove2.me/submissions/dec5c1d3-c715-456f-a08c-aaeca72346cb

import Mathlib
import Definitions.Def_CompressedSensingRadar_Basic
set_option autoImplicit false
open Matrix
namespace CompressedSensingRadar
open scoped Matrix.Norms.L2Operator
open Fin.NatCast

lemma g_norm2_eq {k : Type*} [Fintype k] (v : k → ℂ) : norm2 v = ‖WithLp.toLp 2 v‖ := by
  rw [EuclideanSpace.norm_eq]; rfl

lemma g_specNorm_eq {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k] (A : Matrix m k ℂ) :
    specNorm A = ‖A‖ := by
  rw [Matrix.l2_opNorm_def, ← ContinuousLinearMap.sSup_unitClosedBall_eq_norm]
  unfold specNorm
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨WithLp.toLp 2 v, by rwa [← g_norm2_eq], ?_⟩
    simp [g_norm2_eq]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.ofLp, by rw [g_norm2_eq]; simpa using hx, ?_⟩
    rw [g_norm2_eq]; rfl

lemma g_shift1 (n : ℕ) (f : Fin (n+1) → ℂ) (p : Fin (n+1)) :
    (shiftMat (n+1) *ᵥ f) p = f (p - 1) := by
  simp only [mulVec, dotProduct, shiftMat]
  rw [Finset.sum_eq_single (p - 1)]
  · have : (p : ℕ) = (((p - 1 : Fin (n+1)) : ℕ) + 1) % (n+1) := by
      have h := congrArg Fin.val (sub_add_cancel p 1)
      rw [Fin.val_add] at h
      simp only [Fin.val_one', Nat.add_mod_mod] at h
      exact h.symm
    rw [if_pos this, one_mul]
  · intro q _ hq
    rw [if_neg, zero_mul]
    intro h
    apply hq
    have : p = q + 1 := by
      ext; rw [Fin.val_add]; simpa [Fin.val_one', Nat.add_mod_mod] using h
    rw [this, add_sub_cancel_right]
  · simp

lemma g_shift (n : ℕ) (s : ℕ) (f : Fin (n+1) → ℂ) (p : Fin (n+1)) :
    (shiftMat (n+1) ^ s *ᵥ f) p = f (p - (s : Fin (n+1))) := by
  induction s generalizing f with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, ← mulVec_mulVec, ih, g_shift1]
    congr 1; rw [Nat.cast_succ, sub_sub]

lemma g_entry (n : ℕ) (f : Fin (n+1) → ℂ) (p : Fin (n+1)) (i : Fin ((n+1)^2)) :
    gaborDict (n+1) f p i =
      (omega (n+1) ^ (p : ℕ)) ^ ((i : ℕ) % (n+1)) * f (p - (((i : ℕ) / (n+1) : ℕ) : Fin (n+1))) := by
  simp only [gaborDict, tfShift, modMat, ← mulVec_mulVec, diagonal_pow, mulVec_diagonal, g_shift]
  simp [Pi.pow_apply]

lemma g_prim (n : ℕ) : IsPrimitiveRoot (omega (n+1)) (n+1) := by
  unfold omega; exact_mod_cast Complex.isPrimitiveRoot_exp (n+1) (Nat.succ_ne_zero n)

lemma g_normω (n : ℕ) (a : ℕ) : ‖omega (n+1) ^ a‖ = 1 := by
  rw [norm_pow, (g_prim n).norm'_eq_one (Nat.succ_ne_zero n), one_pow]

lemma g_geo (n : ℕ) (p q : Fin (n+1)) :
    ∑ a : Fin (n+1), (omega (n+1) ^ (p : ℕ)) ^ (a : ℕ) * star ((omega (n+1) ^ (q : ℕ)) ^ (a : ℕ)) =
      if p = q then ((n+1 : ℕ) : ℂ) else 0 := by
  set ω := omega (n+1) with hω
  have hω0 : ω ≠ 0 := by
    intro h; have := g_normω n 1; rw [pow_one, ← hω, h, norm_zero] at this; exact zero_ne_one this
  set ζ := ω ^ (p : ℕ) * (ω ^ (q : ℕ))⁻¹ with hζ
  have hterm : ∀ a : ℕ, (ω ^ (p : ℕ)) ^ a * star ((ω ^ (q : ℕ)) ^ a) = ζ ^ a := by
    intro a
    have h1 : star ((ω ^ (q : ℕ)) ^ a) = ((ω ^ (q : ℕ)) ^ a)⁻¹ := by
      rw [Complex.inv_eq_conj]
      · rfl
      · rw [← pow_mul]; exact g_normω n _
    rw [h1, hζ, mul_pow, inv_pow]
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun a => ζ ^ a) (n+1)]
  split_ifs with hpq
  · subst hpq
    have : ζ = 1 := by rw [hζ, mul_inv_cancel₀ (pow_ne_zero _ hω0)]
    simp [this]
  · have hne : ζ ≠ 1 := by
      intro h
      rw [hζ, mul_inv_eq_one₀ (pow_ne_zero _ hω0)] at h
      exact hpq (Fin.ext ((g_prim n).pow_inj p.isLt q.isLt h))
    have hpow : ζ ^ (n+1) = 1 := by
      rw [hζ, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (p : ℕ), mul_comm (q : ℕ),
        pow_mul, pow_mul, (g_prim n).pow_eq_one, one_pow, one_pow, inv_one, mul_one]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

theorem gabor_unit_norm_tight_frame (N : ℕ) (hN : 0 < N) (f : Fin N → ℂ) (hf : norm2 f = 1) :
    HasUnitAtoms (gaborDict N f) ∧
    gaborDict N f * (gaborDict N f).conjTranspose = (N : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) ∧
    specNorm (gaborDict N f) ^ 2 = N ∧
    (∀ (k j : Fin N) (i : Fin (N ^ 2)), (i : ℕ) / N = (N - (k : ℕ)) % N → (i : ℕ) % N = j →
      blockAtom N f k j = atom (gaborDict N f) i) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n+1 := ⟨N-1, by omega⟩
  have hsum : ∑ q, ‖f q‖ ^ 2 = 1 := by
    unfold norm2 at hf; rwa [Real.sqrt_eq_one] at hf
  have hshift : ∀ s : Fin (n+1), ∑ p, ‖f (p - s)‖ ^ 2 = 1 := fun s => by
    rw [← hsum]; exact Fintype.sum_equiv (Equiv.subRight s) _ _ (fun _ => rfl)
  have hgram : gaborDict (n+1) f * (gaborDict (n+1) f).conjTranspose =
      ((n+1 : ℕ) : ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) := by
    ext p q
    rw [mul_apply]
    simp_rw [conjTranspose_apply, g_entry]
    let e : Fin (n+1) × Fin (n+1) ≃ Fin ((n+1)^2) := finProdFinEquiv.trans (finCongr (sq (n+1)).symm)
    have hev : ∀ x, ((e x : Fin ((n+1)^2)) : ℕ) = x.2 + (n+1) * x.1 := fun x => by
      simp [e, finProdFinEquiv_apply_val]
    have hmod : ∀ x, ((e x : Fin ((n+1)^2)) : ℕ) % (n+1) = x.2 := fun x => by
      rw [hev, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.2.isLt]
    have hdiv : ∀ x, ((e x : Fin ((n+1)^2)) : ℕ) / (n+1) = x.1 := fun x => by
      rw [hev, Nat.add_mul_div_left _ _ (Nat.succ_pos n), Nat.div_eq_of_lt x.2.isLt, zero_add]
    rw [← Equiv.sum_comp e]
    simp_rw [hmod, hdiv, Fin.cast_val_eq_self]
    rw [Fintype.sum_prod_type]
    have : ∀ s : Fin (n+1), ∑ a : Fin (n+1),
        (omega (n+1) ^ (p : ℕ)) ^ (a : ℕ) * f (p - s) * star ((omega (n+1) ^ (q : ℕ)) ^ (a : ℕ) * f (q - s)) =
        (f (p - s) * star (f (q - s))) * ∑ a : Fin (n+1),
          (omega (n+1) ^ (p : ℕ)) ^ (a : ℕ) * star ((omega (n+1) ^ (q : ℕ)) ^ (a : ℕ)) := by
      intro s; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [star_mul']; ring
    simp_rw [this, g_geo]
    rw [Matrix.smul_apply, Matrix.one_apply]
    split_ifs with hpq
    · subst hpq
      have h2 : ∀ s : Fin (n+1), f (p - s) * star (f (p - s)) = ((‖f (p - s)‖ ^ 2 : ℝ) : ℂ) := fun s => by
        rw [Complex.star_def, Complex.mul_conj']; push_cast; rfl
      simp_rw [h2, ← Finset.sum_mul]
      have hs2 : ∑ s : Fin (n+1), ‖f (p - s)‖ ^ 2 = 1 := by
        rw [← hsum]; exact Fintype.sum_equiv (Equiv.subLeft p) _ _ (fun _ => rfl)
      rw [← Complex.ofReal_sum, hs2]; simp
    · simp
  refine ⟨?_, by exact_mod_cast hgram, ?_, ?_⟩
  · intro i
    unfold norm2 atom
    simp_rw [g_entry, norm_mul, ← pow_mul, g_normω, one_mul]
    rw [hshift, Real.sqrt_one]
  · rw [g_specNorm_eq]
    have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (gaborDict (n+1) f)ᴴ
    rw [conjTranspose_conjTranspose, hgram, Matrix.l2_opNorm_conjTranspose] at h1
    rw [sq, ← h1, norm_smul, norm_one, mul_one]
    exact_mod_cast Complex.norm_natCast (n+1)
  · intro k j i h1 h2
    funext p
    unfold blockAtom atom
    rw [g_entry, h1, h2]
    have hk : ((((n + 1 - (k : ℕ)) % (n+1) : ℕ)) : Fin (n+1)) = -k := by
      ext; simp [Fin.val_neg', Fin.val_natCast]
    rw [hk, sub_neg_eq_add, ← pow_mul, mul_comm]

end CompressedSensingRadar
open CompressedSensingRadar in
theorem solution (N : ℕ) (hN : 0 < N) (f : Fin N → ℂ) (hf : norm2 f = 1) :
    HasUnitAtoms (gaborDict N f) ∧
    gaborDict N f * (gaborDict N f).conjTranspose = (N : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) ∧
    specNorm (gaborDict N f) ^ 2 = N ∧
    (∀ (k j : Fin N) (i : Fin (N ^ 2)), (i : ℕ) / N = (N - (k : ℕ)) % N → (i : ℕ) % N = j →
      blockAtom N f k j = atom (gaborDict N f) i) :=
  gabor_unit_norm_tight_frame N hN f hf

