-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.averaging_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:40:58.702514+00:00
-- url     : https://prove2.me/submissions/2c7014f7-9130-438e-90d8-dd565bbf7cf7

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragingVanishes
import Theorems.Thm_Formalism_FourierDecayAlt_P_GeometricRayBounds_exists_dir
import Theorems.Thm_Formalism_FourierDecayAlt_P_GeometricRayBounds_p_sum_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_GeometricRayBounds_nexp
import Theorems.Thm_Formalism_FourierDecayAlt_P_GeometricRayBounds_geom_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_GeometricRayBounds_exp_ne_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open GeometricRayBounds
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C6.AveragingZero := by
  intro β hβ V _ _ p s w a C' x₁ hw H j0
  classical
  set c : Fin s → ℂ := fun j => β * (w j - w j0) with hcdef
  have hc : ∀ j ∈ Finset.univ.erase j0, c j ≠ 0 := by
    intro j hj
    have hj' : j ≠ j0 := Finset.ne_of_mem_erase hj
    exact mul_ne_zero hβ (sub_ne_zero.2 fun h => hj' (hw h))
  obtain ⟨u, hu0, hu⟩ := exists_dir (Finset.univ.erase j0) c hc
  have hunorm : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hsum0 : 0 ≤ ∑ j, |(c j * u).re| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set K0 : ℝ := 1 + ∑ j, |(c j * u).re| with hK0
  have hK0pos : 0 < K0 := by linarith
  set t : ℝ := Real.pi / K0 with ht
  have htpos : 0 < t := div_pos Real.pi_pos hK0pos
  have hphase : ∀ j, |t * (c j * u).re| < 2 * Real.pi := by
    intro j
    have hle : |(c j * u).re| ≤ ∑ j, |(c j * u).re| :=
      Finset.single_le_sum (f := fun j => |(c j * u).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    rw [abs_mul, abs_of_pos htpos, ht, div_mul_eq_mul_div, div_lt_iff₀ hK0pos]
    nlinarith [Real.pi_pos]
  set q : Fin s → ℂ := fun j => Complex.exp (Complex.I * ((t * (c j * u).re : ℝ) : ℂ)) with hqdef
  have hq1 : ∀ j ∈ Finset.univ.erase j0, q j ≠ 1 := fun j hj =>
    exp_ne_one (mul_ne_zero htpos.ne' (hu j hj)) (hphase j)
  have hqn : ∀ j, ‖q j‖ = 1 := fun j => nexp _
  have hpsi : ∀ j (x : ℂ), G.psi β (-(w j0) * x) * G.psi β (w j * x) =
      Complex.exp (Complex.I * (((c j * x).re : ℝ) : ℂ)) := by
    intro j x
    rw [show c j * x = β * (-(w j0) * x) + β * (w j * x) by simp only [hcdef]; ring, Complex.add_re,
      Complex.ofReal_add, mul_add, Complex.exp_add]
    rfl
  have hpsin : ∀ x : ℂ, ‖G.psi β x‖ = 1 := fun x => nexp _
  set Kc : ℝ := ∑ j ∈ Finset.univ.erase j0, 2 / ‖q j - 1‖ * p (a j) with hKc
  have hC' : 0 ≤ C' := by
    obtain ⟨N, hN⟩ := exists_nat_gt (|x₁| / ‖u‖ + 1)
    have hq0 : 0 ≤ |x₁| / ‖u‖ := div_nonneg (abs_nonneg _) hunorm.le
    have hNu : 0 < (N : ℝ) * ‖u‖ := mul_pos (by linarith) hunorm
    have hx : x₁ ≤ ‖((N : ℝ) : ℂ) * u‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)]
      have h2 := (div_lt_iff₀ hunorm).1 (by linarith : |x₁| / ‖u‖ < N)
      linarith [le_abs_self x₁]
    have h1 := (apply_nonneg p _).trans (H _ hx)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)] at h1
    exact (div_nonneg_iff.1 h1).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hNu))
  have hmain : ∀ N : ℕ, 0 < N → x₁ ≤ N * ‖u‖ → p (a j0) ≤ (C' / ‖u‖ + Kc) / N := by
    intro N hN hx₁
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    set x : ℕ → ℂ := fun m => (((N : ℝ) + m * t : ℝ) : ℂ) * u with hxdef
    have hxn : ∀ m : ℕ, (N : ℝ) * ‖u‖ ≤ ‖x m‖ := by
      intro m
      have hmt : 0 ≤ (m : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) htpos.le
      simp only [hxdef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg (Nat.cast_nonneg _) hmt)]
      gcongr
      linarith
    have hT : ∀ m : ℕ, p (∑ j, G.psi β (w j * x m) • a j) ≤ C' / (N * ‖u‖) := by
      intro m
      calc _ ≤ C' / ‖x m‖ := H _ (hx₁.trans (hxn m))
        _ ≤ C' / (N * ‖u‖) := div_le_div_of_nonneg_left hC' (mul_pos hNpos hunorm) (hxn m)
    set coef : Fin s → ℂ := fun j =>
      ∑ m ∈ Finset.range N, G.psi β (-(w j0) * x m) * G.psi β (w j * x m) with hcoef
    have hid : ∑ m ∈ Finset.range N, G.psi β (-(w j0) * x m) • ∑ j, G.psi β (w j * x m) • a j =
        ∑ j, coef j • a j := by
      simp only [Finset.smul_sum, smul_smul, hcoef, Finset.sum_smul]
      exact Finset.sum_comm
    have hc0 : coef j0 = N := by
      have h0 : c j0 = 0 := by simp only [hcdef, sub_self, mul_zero]
      simp only [hcoef, hpsi, h0, zero_mul, Complex.zero_re, Complex.ofReal_zero, mul_zero,
        Complex.exp_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hcj : ∀ j ∈ Finset.univ.erase j0, ‖coef j‖ ≤ 2 / ‖q j - 1‖ := by
      intro j hj
      have hterm : ∀ m : ℕ, G.psi β (-(w j0) * x m) * G.psi β (w j * x m) =
          Complex.exp (Complex.I * (((N : ℝ) * (c j * u).re : ℝ) : ℂ)) * q j ^ m := by
        intro m
        rw [hpsi, show c j * x m = (((N : ℝ) + m * t : ℝ) : ℂ) * (c j * u) by simp only [hxdef]; ring,
          Complex.re_ofReal_mul]
        simp only [hqdef]
        rw [← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      simp only [hcoef, hterm, ← Finset.mul_sum, norm_mul, nexp, one_mul]
      exact geom_bound (q j) (hqn j) (hq1 j hj) N
    have hsplit : ∑ j, coef j • a j = coef j0 • a j0 + ∑ j ∈ Finset.univ.erase j0, coef j • a j :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ j0)).symm
    have hpa : (N : ℝ) * p (a j0) ≤ N * (C' / (N * ‖u‖)) + Kc := by
      have e1 : (N : ℝ) * p (a j0) = p (coef j0 • a j0) := by
        rw [hc0, map_smul_eq_mul]
        simp
      rw [e1]
      have e2 : coef j0 • a j0 =
          (∑ m ∈ Finset.range N, G.psi β (-(w j0) * x m) • ∑ j, G.psi β (w j * x m) • a j) -
            ∑ j ∈ Finset.univ.erase j0, coef j • a j := by
        rw [hid, hsplit]
        abel
      rw [e2]
      refine (map_sub_le_add p _ _).trans (add_le_add ?_ ?_)
      · refine (p_sum_le p _ _).trans ?_
        calc ∑ m ∈ Finset.range N, p (G.psi β (-(w j0) * x m) • ∑ j, G.psi β (w j * x m) • a j)
            = ∑ m ∈ Finset.range N, p (∑ j, G.psi β (w j * x m) • a j) := by
              refine Finset.sum_congr rfl fun m _ => ?_
              rw [map_smul_eq_mul, hpsin, one_mul]
          _ ≤ ∑ m ∈ Finset.range N, C' / (N * ‖u‖) := Finset.sum_le_sum fun m _ => hT m
          _ = N * (C' / (N * ‖u‖)) := by simp
      · refine (p_sum_le p _ _).trans ?_
        refine Finset.sum_le_sum fun j hj => ?_
        rw [map_smul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hcj j hj) (apply_nonneg p _)
    have e3 : (N : ℝ) * (C' / (N * ‖u‖)) = C' / ‖u‖ := by
      field_simp
    rw [e3] at hpa
    rw [le_div_iff₀ hNpos]
    linarith
  have hnn := apply_nonneg p (a j0)
  by_contra hne
  have hδ : 0 < p (a j0) := lt_of_le_of_ne hnn (Ne.symm hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (|x₁| / ‖u‖) ((C' / ‖u‖ + Kc) / p (a j0)))
  have hN1 : |x₁| / ‖u‖ < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : (C' / ‖u‖ + Kc) / p (a j0) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (abs_nonneg _) hunorm.le) hN1
  have hx₁ : x₁ ≤ N * ‖u‖ := by
    have h2 := (div_lt_iff₀ hunorm).1 hN1
    linarith [le_abs_self x₁]
  have hb := hmain N (by exact_mod_cast hNpos) hx₁
  rw [div_lt_iff₀ hδ] at hN2
  rw [le_div_iff₀ hNpos] at hb
  nlinarith
end Formalism.FourierDecayAlt.P
