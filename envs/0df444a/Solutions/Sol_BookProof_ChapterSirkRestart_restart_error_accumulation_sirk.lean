-- Prove2me | solution 1 for BookProof.ChapterSirkRestart.restart_error_accumulation_sirk
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:28:47.298844+00:00
-- url     : https://prove2.me/submissions/3ae2c16b-8a68-4407-813c-2593b01fda16

import Definitions.Def_ChapterSirkRestart
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
namespace SirkRestartAux
open Filter Topology BookProof.ChapterH6 BookProof.ChapterSirkRestart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem sirk_error_decay_exponential (C Dmin h nv : ℝ) (hh : 0 < h) :
    Tendsto (fun m : ℕ => sirkBound C Dmin h nv m) atTop (𝓝 0) := by
  have hlin : Tendsto (fun m : ℕ => -(h * (m : ℝ))) atTop atBot := by
    have : Tendsto (fun m : ℕ => h * (m : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop hh tendsto_natCast_atTop_atTop
    exact tendsto_neg_atTop_atBot.comp this
  have hexp : Tendsto (fun m : ℕ => Real.exp (-(h * (m : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have := ((hexp.const_mul (2 * C)).mul_const Dmin).mul_const nv
  simpa [sirkBound, mul_zero, zero_mul] using this

private theorem norm_pow_apply_le_of_contraction (S : E →L[ℂ] E) (hS : ∀ w : E, ‖S w‖ ≤ ‖w‖)
    (n : ℕ) (v : E) : ‖(S ^ n) v‖ ≤ ‖v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : ((S ^ (n + 1)) v) = S ((S ^ n) v) := by
      rw [pow_succ']; rfl
    rw [hstep]
    exact le_trans (hS _) ih

private theorem restart_error_accumulation (U S : E →L[ℂ] E) (eps : ℝ)
    (hU : ∀ w : E, ‖U w‖ ≤ ‖w‖) (hS : ∀ w : E, ‖S w‖ ≤ ‖w‖)
    (hstep : ∀ w : E, ‖U w - S w‖ ≤ eps * ‖w‖)
    (n : ℕ) (v : E) :
    ‖(U ^ n) v - (S ^ n) v‖ ≤ n * eps * ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have heps : 0 ≤ eps := by
    have h0 : (0 : ℝ) ≤ eps * ‖v‖ := le_trans (norm_nonneg _) (hstep v)
    nlinarith
  induction n with
  | zero => simp
  | succ n ih =>
    have hUstep : ((U ^ (n + 1)) v) = U ((U ^ n) v) := by rw [pow_succ']; rfl
    have hSstep : ((S ^ (n + 1)) v) = S ((S ^ n) v) := by rw [pow_succ']; rfl
    have hsplit : U ((U ^ n) v) - S ((S ^ n) v)
        = U ((U ^ n) v - (S ^ n) v) + (U ((S ^ n) v) - S ((S ^ n) v)) := by
      rw [map_sub]; abel
    have h1 : ‖U ((U ^ n) v - (S ^ n) v)‖ ≤ n * eps * ‖v‖ :=
      le_trans (hU _) ih
    have h2 : ‖U ((S ^ n) v) - S ((S ^ n) v)‖ ≤ eps * ‖v‖ := by
      refine le_trans (hstep _) ?_
      exact mul_le_mul_of_nonneg_left
        (norm_pow_apply_le_of_contraction S hS n v) heps
    rw [hUstep, hSstep, hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have : ((n : ℝ) + 1) * eps * ‖v‖ = n * eps * ‖v‖ + eps * ‖v‖ := by ring
    simp only [Nat.cast_add, Nat.cast_one]
    linarith

private theorem restart_error_accumulation_sirk (U S : E →L[ℂ] E) (C Dmin h : ℝ) (m : ℕ)
    (hU : ∀ w : E, ‖U w‖ ≤ ‖w‖) (hS : ∀ w : E, ‖S w‖ ≤ ‖w‖)
    (hstep : ∀ w : E, ‖U w - S w‖ ≤ sirkBound C Dmin h 1 m * ‖w‖)
    (n : ℕ) (v : E) :
    ‖(U ^ n) v - (S ^ n) v‖ ≤ n * sirkBound C Dmin h 1 m * ‖v‖ :=
  restart_error_accumulation U S _ hU hS hstep n v

private theorem comp_pow_of_comm (U Om : E →L[ℂ] E) (hcomm : Om.comp U = U.comp Om) (n : ℕ) :
    Om.comp (U ^ n) = (U ^ n).comp Om := by
  induction n with
  | zero => ext w; simp
  | succ n ih =>
    have hpow : (U ^ (n + 1)) = U.comp (U ^ n) := by
      rw [pow_succ']; rfl
    ext w
    have h1 : Om (U ((U ^ n) w)) = U (Om ((U ^ n) w)) :=
      congrArg (fun f : E →L[ℂ] E => f ((U ^ n) w)) hcomm
    have h2 : Om ((U ^ n) w) = (U ^ n) (Om w) :=
      congrArg (fun f : E →L[ℂ] E => f w) ih
    simp only [hpow, ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [h1, h2]

private theorem brst_leakage_zero_of_exact (U Om : E →L[ℂ] E)
    (hcomm : Om.comp U = U.comp Om) (n : ℕ) (v : E) (hv : Om v = 0) :
    Om ((U ^ n) v) = 0 := by
  have h : Om ((U ^ n) v) = (U ^ n) (Om v) :=
    congrArg (fun f : E →L[ℂ] E => f v) (comp_pow_of_comm U Om hcomm n)
  rw [h, hv, map_zero]

private theorem brst_leakage_bound (U S Om : E →L[ℂ] E) (eps : ℝ)
    (hU : ∀ w : E, ‖U w‖ ≤ ‖w‖) (hS : ∀ w : E, ‖S w‖ ≤ ‖w‖)
    (hstep : ∀ w : E, ‖U w - S w‖ ≤ eps * ‖w‖)
    (hcomm : Om.comp U = U.comp Om)
    (n : ℕ) (v : E) (hv : Om v = 0) :
    ‖Om ((S ^ n) v)‖ ≤ ‖Om‖ * (n * eps * ‖v‖) := by
  have hexact : Om ((U ^ n) v) = 0 := brst_leakage_zero_of_exact U Om hcomm n v hv
  have hsplit : Om ((S ^ n) v) = -(Om ((U ^ n) v - (S ^ n) v)) := by
    rw [map_sub, hexact]
    abel
  rw [hsplit, norm_neg]
  refine le_trans (Om.le_opNorm _) ?_
  exact mul_le_mul_of_nonneg_left
    (restart_error_accumulation U S eps hU hS hstep n v) (norm_nonneg _)

private theorem restart_error_tendsto_zero (C Dmin h nv : ℝ) (n : ℕ) (hh : 0 < h) :
    Tendsto (fun m : ℕ => (n : ℝ) * sirkBound C Dmin h nv m) atTop (𝓝 0) := by
  have := (sirk_error_decay_exponential C Dmin h nv hh).const_mul (n : ℝ)
  simpa using this

end SirkRestartAux

-- Generated from ChapterSirkRestart.lean — theorem BookProof.ChapterSirkRestart.restart_error_accumulation_sirk
open BookProof.ChapterSirkRestart







noncomputable section

open Filter Topology


open BookProof.ChapterH6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
open SirkRestartAux

theorem solution (U S : E →L[ℂ] E) (C Dmin h : ℝ) (m : ℕ)
    (hU : ∀ w : E, ‖U w‖ ≤ ‖w‖) (hS : ∀ w : E, ‖S w‖ ≤ ‖w‖)
    (hstep : ∀ w : E, ‖U w - S w‖ ≤ sirkBound C Dmin h 1 m * ‖w‖)
    (n : ℕ) (v : E) :
    ‖(U ^ n) v - (S ^ n) v‖ ≤ n * sirkBound C Dmin h 1 m * ‖v‖ := restart_error_accumulation U S _ hU hS hstep n v

#print axioms solution
