-- Prove2me | solution 1 for FixedPointAA.Main.success_probability
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:38:42.472886+00:00
-- url     : https://prove2.me/submissions/a0130314-668c-4dd7-a0e6-c8d6dcc80dd5

import Definitions.Def_FixedPointAA_Main_Setting
import Theorems.Thm_FixedPointAA_Main_reduction_to_plane
import Theorems.Thm_FixedPointAA_Main_reflections_matrix_form
import Theorems.Thm_FixedPointAA_Main_reflections_as_rotations
import Theorems.Thm_FixedPointAA_Main_sequence_as_A_product
import Theorems.Thm_FixedPointAA_Main_amplitude_chebyshev
import Theorems.Thm_FixedPointAA_Main_chebT_gammaInv

open FixedPointAA.Main
open scoped Matrix

private lemma conj_mul_self_eq_norm_sq (z : ℂ) :
    star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [RCLike.star_def, Complex.conj_mul']
  norm_cast

private lemma dotProduct_self_re_nonneg {N : ℕ} (v : Fin N → ℂ) :
    0 ≤ (star v ⬝ᵥ v).re := by
  simp only [dotProduct, Pi.star_apply, conj_mul_self_eq_norm_sq, Complex.re_sum,
    Complex.ofReal_re]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg ‖v i‖)

private lemma star_dotProduct_comm {N : ℕ} (u v : Fin N → ℂ) :
    star u ⬝ᵥ v = star (star v ⬝ᵥ u) := by
  simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star, mul_comm]

private lemma lam_le_one {N : ℕ} (s T : Fin N → ℂ)
    (hs : star s ⬝ᵥ s = 1) (hT : star T ⬝ᵥ T = 1)
    (lam : ℝ) (hlam : ‖star T ⬝ᵥ s‖ ^ 2 = lam) :
    lam ≤ 1 := by
  set c : ℂ := star T ⬝ᵥ s
  have h1 : star (s - c • T) ⬝ᵥ (s - c • T) = 1 - star c * c := by
    rw [star_sub, star_smul, sub_dotProduct, dotProduct_sub,
      dotProduct_sub, smul_dotProduct, dotProduct_smul,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      hs, hT, star_dotProduct_comm s T]
    change (1 : ℂ) - c * star c - (star c * c - c * (star c * 1)) = 1 - star c * c
    ring
  have h2 := dotProduct_self_re_nonneg (s - c • T)
  rw [h1, conj_mul_self_eq_norm_sq, hlam] at h2
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at h2
  linarith

private lemma vecMulVec_mulVec {N : ℕ} (u v w : Fin N → ℂ) :
    Matrix.vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  dsimp [Matrix.mulVec, dotProduct, Matrix.vecMulVec]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

private lemma proj_refl_isometry {N : ℕ} (u w : Fin N → ℂ) (hu : star u ⬝ᵥ u = 1)
    (e : ℂ) (he : star e * e = 1) :
    star ((1 - (1 - e) • Matrix.vecMulVec u (star u)) *ᵥ w) ⬝ᵥ
      ((1 - (1 - e) • Matrix.vecMulVec u (star u)) *ᵥ w) = star w ⬝ᵥ w := by
  have hmv : (1 - (1 - e) • Matrix.vecMulVec u (star u)) *ᵥ w =
      w - ((1 - e) * (star u ⬝ᵥ w)) • u := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      vecMulVec_mulVec, smul_smul]
  rw [hmv]
  set c : ℂ := star u ⬝ᵥ w
  set k : ℂ := 1 - e
  rw [star_sub, star_smul, sub_dotProduct, dotProduct_sub,
    dotProduct_sub, smul_dotProduct, dotProduct_smul,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    hu, star_dotProduct_comm w u]
  change star w ⬝ᵥ w - (k * c) * star c -
    (star (k * c) * c - (k * c) * (star (k * c) * 1)) = star w ⬝ᵥ w
  rw [star_mul]
  have hk : star k * k - k - star k = 0 := by
    change star (1 - e) * (1 - e) - (1 - e) - star (1 - e) = 0
    rw [star_sub, star_one]
    calc (1 - star e) * (1 - e) - (1 - e) - (1 - star e)
      _ = star e * e - 1 := by ring
      _ = 0 := by rw [he, sub_self]
  calc star w ⬝ᵥ w - k * c * star c - (star c * star k * c - k * c * (star c * star k * 1))
    _ = star w ⬝ᵥ w + (star k * k - k - star k) * (star c * c) := by ring
    _ = star w ⬝ᵥ w := by rw [hk, zero_mul, add_zero]

private lemma star_exp_real_mul_I (x : ℝ) :
    star (Complex.exp ((x : ℂ) * Complex.I)) * Complex.exp ((x : ℂ) * Complex.I) = 1 := by
  rw [conj_mul_self_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow, Complex.ofReal_one]

private lemma star_exp_neg_real_mul_I (x : ℝ) :
    star (Complex.exp (-(x : ℂ) * Complex.I)) * Complex.exp (-(x : ℂ) * Complex.I) = 1 := by
  have : -(x : ℂ) * Complex.I = ((-x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this]
  exact star_exp_real_mul_I (-x)

private lemma G_isometry {N : ℕ} (s T w : Fin N → ℂ)
    (hs : star s ⬝ᵥ s = 1) (hT : star T ⬝ᵥ T = 1) (α β : ℝ) :
    star (G s T α β *ᵥ w) ⬝ᵥ (G s T α β *ᵥ w) = star w ⬝ᵥ w := by
  dsimp [G, Ss, St]
  rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, star_neg,
    neg_dotProduct, dotProduct_neg, neg_neg]
  rw [proj_refl_isometry s _ hs _ (star_exp_neg_real_mul_I α)]
  exact proj_refl_isometry T w hT _ (star_exp_real_mul_I β)

private lemma seqOp_isometry {N : ℕ} (s T : Fin N → ℂ)
    (hs : star s ⬝ᵥ s = 1) (hT : star T ⬝ᵥ T = 1) (α β : ℕ → ℝ) (j : ℕ) :
    star (seqOp s T α β j *ᵥ s) ⬝ᵥ (seqOp s T α β j *ᵥ s) = 1 := by
  induction j with
  | zero =>
    simp [seqOp, hs]
  | succ j ih =>
    simp only [seqOp, ← Matrix.mulVec_mulVec]
    rw [G_isometry s T _ hs hT]
    exact ih

private lemma sVec_unit (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    star (sVec lam) ⬝ᵥ sVec lam = 1 := by
  have hsub : 0 ≤ 1 - lam := by linarith
  simp only [sVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.star_apply, RCLike.star_def,
    Complex.conj_ofReal]
  norm_cast
  rw [← sq, ← sq, Real.sq_sqrt hsub, Real.sq_sqrt h0]
  ring

private lemma tVec_unit : star tVec ⬝ᵥ tVec = 1 := by
  simp [tVec, dotProduct, Fin.sum_univ_two]

private lemma fin2_dotProduct_self_eq_one (v : Fin 2 → ℂ) (hv : star v ⬝ᵥ v = 1) :
    ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 = 1 := by
  have h := congrArg Complex.re hv
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply,
    conj_mul_self_eq_norm_sq, Complex.add_re, Complex.ofReal_re, Complex.one_re] at h
  exact h

theorem solution {N : ℕ} (s T : Fin N → ℂ)
    (hs : star s ⬝ᵥ s = 1) (hT : star T ⬝ᵥ T = 1)
    (lam : ℝ) (hlam : ‖star T ⬝ᵥ s‖ ^ 2 = lam) (hlam0 : 0 < lam)
    (l : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ‖star T ⬝ᵥ (seqOp s T (alpha l δ) (beta l δ) l *ᵥ s)‖ ^ 2 =
      PL (2 * l + 1) lam δ := by
  have hlam1 : lam ≤ 1 := lam_le_one s T hs hT lam hlam
  rw [reduction_to_plane s T hs hT lam hlam hlam0 (alpha l δ) (beta l δ) l]
  set v : Fin 2 → ℂ := seqOp (sVec lam) tVec (alpha l δ) (beta l δ) l *ᵥ sVec lam
  have hv_unit : star v ⬝ᵥ v = 1 :=
    seqOp_isometry (sVec lam) tVec (sVec_unit lam hlam0.le hlam1) tVec_unit (alpha l δ) (beta l δ) l
  have hv_norm : ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 = 1 := fin2_dotProduct_self_eq_one v hv_unit
  have ht_dot : star tVec ⬝ᵥ v = v 1 := by
    simp [tVec, dotProduct, Fin.sum_univ_two]
  obtain ⟨⟨ω, hω, θ, hv_eq⟩, _⟩ := sequence_as_A_product lam δ hlam0 hlam1 hδ0 hδ1 l
  change v = ω • ((R 0 θ * Aprod (blochAngle lam) (zeta l δ) (2 * l + 1)) *ᵥ tbarVec) at hv_eq
  set u : Fin 2 → ℂ := Aprod (blochAngle lam) (zeta l δ) (2 * l + 1) *ᵥ tbarVec
  have hR : R 0 θ = Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) •
      !![1, 0; 0, Complex.exp ((θ : ℂ) * Complex.I)] := by
    have hrot := (reflections_as_rotations lam hlam0.le hlam1 0 θ).2
    have hmat := (reflections_matrix_form lam hlam0.le hlam1 0 θ).2
    rw [hmat] at hrot
    calc R 0 θ
      _ = (Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)) • R 0 θ := by
          rw [← Complex.exp_add]
          have : -((θ / 2 : ℝ) : ℂ) * Complex.I + ((θ / 2 : ℝ) : ℂ) * Complex.I = 0 := by ring
          rw [this, Complex.exp_zero, one_smul]
      _ = Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) •
            (Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) • R 0 θ) := by
          rw [mul_smul]
      _ = Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) •
            !![1, 0; 0, Complex.exp ((θ : ℂ) * Complex.I)] := by
          rw [← hrot]
  have hv0 : v 0 = ω * (Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) * u 0) := by
    rw [hv_eq, ← Matrix.mulVec_mulVec]
    change (ω • (R 0 θ *ᵥ u)) 0 = _
    rw [hR]
    simp [dotProduct, Fin.sum_univ_two]
  have hv0_norm : ‖v 0‖ = ‖amp (blochAngle lam) (zeta l δ) (2 * l + 1)‖ := by
    have hexp : ‖Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      have : -((θ / 2 : ℝ) : ℂ) * Complex.I = ((-(θ / 2) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [hv0, norm_mul, norm_mul, hω, hexp, one_mul, one_mul]
    rfl
  have hcos : Real.cos (blochAngle lam / 2) = Real.sqrt (1 - lam) := by
    dsimp [blochAngle]
    have : 2 * Real.arcsin (Real.sqrt lam) / 2 = Real.arcsin (Real.sqrt lam) := by ring
    rw [this, Real.cos_arcsin, Real.sq_sqrt hlam0.le]
  have hamp := amplitude_chebyshev lam δ hlam0 hlam1 hδ0 hδ1 l
  have hcheb := chebT_gammaInv δ hδ0 hδ1 (2 * l + 1) (by omega)
  rw [hcos, hcheb, mul_comm (Real.sqrt (1 - lam))] at hamp
  have hamp_norm : ‖amp (blochAngle lam) (zeta l δ) (2 * l + 1)‖ ^ 2 =
      δ ^ 2 * chebT (2 * l + 1) (gammaInv (2 * l + 1) δ * Real.sqrt (1 - lam)) ^ 2 := by
    rw [hamp, Complex.norm_real, Real.norm_eq_abs, sq_abs, one_div, div_inv_eq_mul]
    ring
  rw [ht_dot]
  dsimp [PL]
  rw [hv0_norm, hamp_norm] at hv_norm
  linarith
