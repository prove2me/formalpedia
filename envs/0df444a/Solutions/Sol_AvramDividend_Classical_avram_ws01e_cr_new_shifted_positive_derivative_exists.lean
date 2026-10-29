-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_cr_new_shifted_positive_derivative_exists
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:52:27.512492+00:00
-- url     : https://prove2.me/submissions/3c64cee0-344f-4609-928e-23102ba52487

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_shifted_levy_psi_analytic_on_positive
import Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_derivative_lower
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_strictly_above_shift
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q phi lam : ℝ) (hq : 0 < q) (hphi : 0 < phi)
    (hroot : X.ψ phi = q) (hlam : 0 < lam) :
    ∃ m : ℝ, 0 < m ∧ HasDerivAt X.ψ m (phi + lam) := by
  have han := avram_ws01e_b_shifted_levy_psi_analytic_on_positive X phi q hphi lam hlam
  have hd : DifferentiableAt ℝ (fun β : ℝ => X.ψ (phi + β) - q) lam := han.differentiableAt
  have hd2 : DifferentiableAt ℝ (fun x : ℝ => (X.ψ (phi + (x - phi)) - q) + q) (phi + lam) := by
    refine DifferentiableAt.add_const q ?_
    have : DifferentiableAt ℝ (fun β : ℝ => X.ψ (phi + β) - q) ((phi + lam) - phi) := by
      simpa using hd
    exact this.comp (phi + lam) ((differentiableAt_id).sub_const phi)
  have heq : (fun x : ℝ => (X.ψ (phi + (x - phi)) - q) + q) = X.ψ := by
    funext x; ring_nf
  rw [heq] at hd2
  have hgt := levy_psi_root_strictly_above_shift X q phi lam hq hphi hlam hroot
  have := esscher_levy_positive_root_derivative_lower X (X.ψ (phi + lam)) (phi + lam)
    (deriv X.ψ (phi + lam)) (by linarith) (by linarith) rfl hd2.hasDerivAt
  exact ⟨_, this.2, hd2.hasDerivAt⟩
