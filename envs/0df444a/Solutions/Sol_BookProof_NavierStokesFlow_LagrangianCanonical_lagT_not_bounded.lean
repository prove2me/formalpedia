-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianCanonical.lagT_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:34.06552+00:00
-- url     : https://prove2.me/submissions/46017b50-94e2-4ce3-9895-8098fc3546de

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — solution of BookProof.NavierStokesFlow.LagrangianCanonical.lagT_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_omega_pos
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_lagT_coreState
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_norm_coreState
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical

















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent














variable (nu : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (hnu : 0 < nu) :
    ¬ ∃ C : ℝ, ∀ v : lpFiniteModes Vel,
      ‖(lagT nu v : L2I Vel)‖ ≤ C * ‖(v : L2I Vel)‖ := by

  rintro ⟨C, hC⟩
  have hw : 0 < omega nu := omega_pos nu hnu
  set n : ℕ := ⌈|C| / (3 * omega nu)⌉₊ + 1 with hn
  have h3 : 0 < 3 * omega nu := by linarith
  have hn1 : |C| / (3 * omega nu) + 1 ≤ (n : ℝ) := by
    have := Nat.le_ceil (|C| / (3 * omega nu))
    rw [hn]
    push_cast
    linarith
  have hdiv : |C| / (3 * omega nu) * (3 * omega nu) = |C| := div_mul_cancel₀ _ (ne_of_gt h3)
  have hmul : (|C| / (3 * omega nu) + 1) * (3 * omega nu) ≤ (n : ℝ) * (3 * omega nu) :=
    mul_le_mul_of_nonneg_right hn1 (le_of_lt h3)
  have hbig : C < 3 * omega nu * (n : ℝ) := by
    have hCa : C ≤ |C| := le_abs_self C
    nlinarith [hmul, hdiv]
  have hb := hC (coreState (fun _ => n))
  rw [lagT_coreState nu, norm_coreState] at hb
  have hlam : lagLam nu (fun _ => n) = 3 * omega nu * (n : ℝ) + 3 * omega nu / 2 := by
    simp only [lagLam, Fin.sum_univ_three]
    ring
  rw [hlam] at hb
  simp only [Submodule.coe_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    norm_coreState, mul_one] at hb
  have hpos : 0 ≤ 3 * omega nu * (n : ℝ) + 3 * omega nu / 2 := by positivity
  rw [abs_of_nonneg hpos] at hb
  linarith
