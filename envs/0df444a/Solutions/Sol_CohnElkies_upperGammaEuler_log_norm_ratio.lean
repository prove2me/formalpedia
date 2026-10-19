-- Prove2me | solution 1 for CohnElkies.upperGammaEuler_log_norm_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/e33ea161-81bb-4492-a256-8bec65006c79

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaEuler_real_factor_norm
import Theorems.Thm_CohnElkies_upperGammaEuler_complex_factor_pos

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {m : ℝ} (hm : 0 < m) (b : ℝ)
    {n : ℕ} (hn : 0 < n) :
    Real.log
      (‖Complex.GammaSeq
          ((m : ℂ) + Complex.I * (b : ℂ)) n‖ /
        ‖Complex.GammaSeq (m : ℂ) n‖) =
      -(∑ k ∈ Finset.range (n + 1),
        Real.log
          (‖(m : ℂ) + Complex.I * (b : ℂ) + (k : ℂ)‖ /
            (m + (k : ℝ)))) := by
  classical
  let z : ℂ := (m : ℂ) + Complex.I * (b : ℂ)
  have hpow : ‖(n : ℂ) ^ z‖ = ‖(n : ℂ) ^ (m : ℂ)‖ := by
    rw [Complex.norm_natCast_cpow_of_pos hn,
      Complex.norm_natCast_cpow_of_pos hn]
    simp [z]
  have hpown : ‖(n : ℂ) ^ (m : ℂ)‖ ≠ 0 :=
    (Complex.norm_natCast_cpow_pos_of_pos hn (m : ℂ)).ne'
  have hfactorial : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hreal (k : ℕ) : 0 < m + (k : ℝ) := by
    positivity
  have hcomplex (k : ℕ) : 0 < ‖z + (k : ℂ)‖ := by
    simpa [z] using! upperGammaEuler_complex_factor_pos hm b k
  have hprodreal :
      (∏ k ∈ Finset.range (n + 1),
        (m + (k : ℝ))) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr
      (fun k hk => (hreal k).ne')
  have hprodcomplex :
      (∏ k ∈ Finset.range (n + 1),
        ‖z + (k : ℂ)‖) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr
      (fun k hk => (hcomplex k).ne')
  have hratio :
      ‖Complex.GammaSeq z n‖ /
          ‖Complex.GammaSeq (m : ℂ) n‖ =
        (∏ k ∈ Finset.range (n + 1),
          (‖z + (k : ℂ)‖ / (m + (k : ℝ))))⁻¹ := by
    rw [Complex.GammaSeq, Complex.GammaSeq,
      norm_div, norm_div, norm_mul, norm_mul,
      norm_prod, norm_prod, hpow]
    simp_rw [upperGammaEuler_real_factor_norm hm]
    rw [Finset.prod_div_distrib]
    simp only [norm_natCast]
    field_simp [hpown, hfactorial, hprodreal, hprodcomplex]
  change Real.log (‖Complex.GammaSeq z n‖ /
      ‖Complex.GammaSeq (m : ℂ) n‖) = _
  rw [hratio, Real.log_inv, Real.log_prod]
  intro k hk
  exact div_ne_zero (hcomplex k).ne' (hreal k).ne'
end CohnElkies
