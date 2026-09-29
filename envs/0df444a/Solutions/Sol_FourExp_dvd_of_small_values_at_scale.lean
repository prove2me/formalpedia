-- Prove2me | solution 1 for FourExp.dvd_of_small_values_at_scale
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:16:25.49245+00:00
-- url     : https://prove2.me/submissions/9484d50c-5208-4c31-be35-b243d026833b

import Mathlib
import Theorems.Thm_FourExp_dvd_of_small_values

open Polynomial

namespace FourExpDvdAtScale

/-- `log (B u) ≤ c u` for all large `u`. -/
lemma log_small (B c : ℝ) (hB : 0 < B) (hc : 0 < c) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ u, Y ≤ u → Real.log (B * u) ≤ c * u := by
  refine ⟨4 * B / c ^ 2 + 1, by positivity, fun u hu => ?_⟩
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  have h1 := Real.log_le_rpow_div (x := B * u) (by positivity) (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at h1
  have hsq := Real.sq_sqrt (show 0 ≤ B * u by positivity)
  have hsn := Real.sqrt_nonneg (B * u)
  have hcu : 4 * B ≤ c ^ 2 * u := by
    have : 4 * B / c ^ 2 ≤ u := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h2 : 2 * Real.sqrt (B * u) ≤ c * u := by
    by_contra hlt
    rw [not_le] at hlt
    have hpos : 0 < c * u := by positivity
    nlinarith
  have : Real.sqrt (B * u) / (1 / 2) = 2 * Real.sqrt (B * u) := by ring
  linarith

end FourExpDvdAtScale

open FourExpDvdAtScale in
theorem solution (α : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : ℝ, ∀ u v : ℝ, U ≤ u → 1 ≤ v → v ≤ u → ∀ P Q : ℤ[X], Irreducible Q →
      (∀ i, |(P.coeff i : ℝ)| ≤ Real.exp u) → (P.natDegree : ℝ) ≤ v →
      (∀ i, |(Q.coeff i : ℝ)| ≤ Real.exp (3 * u)) → (Q.natDegree : ℝ) ≤ (1 + ε / 2) * v →
      ‖aeval α P‖ < Real.exp (-((4 + ε) * (u * v))) →
      ‖aeval α Q‖ < Real.exp (-((4 + ε) * (u * v))) → Q ∣ P := by
  set B : ℝ := (1 + ‖α‖) * (2 + ε / 2) with hBdef
  have hB : 0 < B := by positivity
  obtain ⟨Y, -, hY⟩ := log_small B (ε / (4 * (2 + ε / 2))) hB (by positivity)
  refine ⟨max Y (4 * Real.log 2 / ε + 1),
    fun u v hU hv1 hvu P Q hirr hPH hd hQH hdz hPsmall hQsmall => ?_⟩
  have huY : Y ≤ u := le_trans (le_max_left _ _) hU
  have hu2 : 4 * Real.log 2 / ε + 1 ≤ u := le_trans (le_max_right _ _) hU
  have hv0 : 0 < v := by linarith
  have hu0 : 0 < u := by linarith
  set d : ℕ := P.natDegree with hddef
  set δ : ℕ := Q.natDegree with hδdef
  -- the three factors of the resultant bound
  have hfac1 : ((1 + ‖α‖) * ((d + δ : ℕ) : ℝ)) ^ (d + δ) ≤ Real.exp (ε / 4 * (u * v)) := by
    rcases Nat.eq_zero_or_pos (d + δ) with hm | hm
    · rw [hm, pow_zero]; exact Real.one_le_exp (by positivity)
    · have hm1 : (1 : ℝ) ≤ ((d + δ : ℕ) : ℝ) := by exact_mod_cast hm
      set bb : ℝ := (1 + ‖α‖) * ((d + δ : ℕ) : ℝ) with hbb
      have hb1 : 1 ≤ bb := by
        have : (1 : ℝ) ≤ 1 + ‖α‖ := by linarith [norm_nonneg α]
        nlinarith
      have hmv : ((d + δ : ℕ) : ℝ) ≤ (2 + ε / 2) * v := by
        push_cast
        have : (δ : ℝ) ≤ (1 + ε / 2) * v := hdz
        linarith
      have hbv : bb ≤ B * u := by
        rw [hbb, hBdef]
        have : (2 + ε / 2) * v ≤ (2 + ε / 2) * u := mul_le_mul_of_nonneg_left hvu (by positivity)
        have h0 : 0 ≤ 1 + ‖α‖ := by positivity
        calc (1 + ‖α‖) * ((d + δ : ℕ) : ℝ) ≤ (1 + ‖α‖) * ((2 + ε / 2) * u) :=
              mul_le_mul_of_nonneg_left (hmv.trans this) h0
          _ = (1 + ‖α‖) * (2 + ε / 2) * u := by ring
      have hlogb : Real.log bb ≤ ε / (4 * (2 + ε / 2)) * u :=
        (Real.log_le_log (by linarith) hbv).trans (hY u huY)
      have hlogb0 : 0 ≤ Real.log bb := Real.log_nonneg hb1
      calc bb ^ (d + δ) = Real.exp (((d + δ : ℕ) : ℝ) * Real.log bb) := by
            rw [← Real.exp_log (by linarith : 0 < bb), ← Real.exp_nat_mul, Real.log_exp]
        _ ≤ Real.exp (ε / 4 * (u * v)) := by
            apply Real.exp_le_exp.mpr
            calc ((d + δ : ℕ) : ℝ) * Real.log bb ≤ ((2 + ε / 2) * v) * Real.log bb :=
                  mul_le_mul_of_nonneg_right hmv hlogb0
              _ ≤ ((2 + ε / 2) * v) * (ε / (4 * (2 + ε / 2)) * u) :=
                  mul_le_mul_of_nonneg_left hlogb (by positivity)
              _ = ε / 4 * (u * v) := by field_simp
  have hfac2 : Real.exp u ^ δ * Real.exp (3 * u) ^ d ≤ Real.exp ((4 + ε / 2) * (u * v)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hu0 : 0 ≤ u := by linarith
    have h1 : (δ : ℝ) * u ≤ (1 + ε / 2) * v * u := mul_le_mul_of_nonneg_right hdz hu0
    have h2 : (d : ℝ) * (3 * u) ≤ v * (3 * u) := mul_le_mul_of_nonneg_right hd (by linarith)
    nlinarith
  have hfac3 : ‖aeval α P‖ + ‖aeval α Q‖ < 2 * Real.exp (-((4 + ε) * (u * v))) := by linarith
  have hsmall : ((1 + ‖α‖) * ((d + δ : ℕ) : ℝ)) ^ (d + δ) * Real.exp u ^ δ * Real.exp (3 * u) ^ d
      * (‖aeval α P‖ + ‖aeval α Q‖) < 1 := by
    have hpos1 : 0 ≤ ((1 + ‖α‖) * ((d + δ : ℕ) : ℝ)) ^ (d + δ) := by positivity
    have hpos2 : 0 ≤ Real.exp u ^ δ * Real.exp (3 * u) ^ d := by positivity
    have hA : ((1 + ‖α‖) * ((d + δ : ℕ) : ℝ)) ^ (d + δ) * (Real.exp u ^ δ * Real.exp (3 * u) ^ d)
        ≤ Real.exp (ε / 4 * (u * v)) * Real.exp ((4 + ε / 2) * (u * v)) :=
      mul_le_mul hfac1 hfac2 hpos2 (Real.exp_pos _).le
    have hS0 : 0 ≤ ‖aeval α P‖ + ‖aeval α Q‖ := by positivity
    have hlhs : ((1 + ‖α‖) * ((d + δ : ℕ) : ℝ)) ^ (d + δ) * Real.exp u ^ δ * Real.exp (3 * u) ^ d
        * (‖aeval α P‖ + ‖aeval α Q‖)
        ≤ (Real.exp (ε / 4 * (u * v)) * Real.exp ((4 + ε / 2) * (u * v)))
          * (‖aeval α P‖ + ‖aeval α Q‖) := by
      have := mul_le_mul_of_nonneg_right hA hS0
      calc _ = ((1 + ‖α‖) * ((d + δ : ℕ) : ℝ)) ^ (d + δ) * (Real.exp u ^ δ * Real.exp (3 * u) ^ d)
            * (‖aeval α P‖ + ‖aeval α Q‖) := by ring
        _ ≤ _ := this
    have hE : 0 < Real.exp (ε / 4 * (u * v)) * Real.exp ((4 + ε / 2) * (u * v)) := by positivity
    have hlt := mul_lt_mul_of_pos_left hfac3 hE
    have hfinal : Real.exp (ε / 4 * (u * v)) * Real.exp ((4 + ε / 2) * (u * v))
        * (2 * Real.exp (-((4 + ε) * (u * v)))) = 2 * Real.exp (-(ε / 4 * (u * v))) := by
      rw [show Real.exp (ε / 4 * (u * v)) * Real.exp ((4 + ε / 2) * (u * v))
          * (2 * Real.exp (-((4 + ε) * (u * v))))
          = 2 * (Real.exp (ε / 4 * (u * v)) * Real.exp ((4 + ε / 2) * (u * v))
            * Real.exp (-((4 + ε) * (u * v)))) by ring]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    have hlog2 : Real.log 2 ≤ ε / 4 * (u * v) := by
      have huv : u ≤ u * v := by nlinarith
      have : 4 * Real.log 2 / ε ≤ u := by linarith
      have h' : Real.log 2 ≤ ε / 4 * u := by
        rw [div_le_iff₀ hε] at this
        linarith
      nlinarith
    have htwo : 2 * Real.exp (-(ε / 4 * (u * v))) ≤ 1 := by
      have h1 : Real.exp (-(ε / 4 * (u * v))) ≤ Real.exp (-Real.log 2) :=
        Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]
        norm_num
      rw [h2] at h1
      linarith
    linarith
  exact FourExp.dvd_of_small_values P Q hirr α (Real.exp u) (Real.exp (3 * u))
    (Real.one_le_exp (by linarith)) (Real.one_le_exp (by linarith)) hPH hQH hsmall

#print axioms solution
