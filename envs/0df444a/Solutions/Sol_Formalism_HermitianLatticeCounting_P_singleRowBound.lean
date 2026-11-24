-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.singleRowBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:25.073797+00:00
-- url     : https://prove2.me/submissions/d12f77fb-9f81-4f7f-9d15-032b835a51fe

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExponentInequalityNondegenerateMid
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_exponent_inequality_single
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pow_eq_exp_mul_log
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_heightParameter_rpow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_parameterRange_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : SingleRowBound := by
  unfold SingleRowBound
  intro C hC
  refine ⟨16 * C ^ 32, ?_⟩
  intro k r f b g v NT Gam hPar
  obtain ⟨hm4, hmf, hfk, hlb, hlk, hlC0, hlC, hlg, hl20, hl2, hX, hg0, hb0, hv0, hlv, hNT0, hlNT,
    hGam0, hlG0, hlG⟩ := parameterRange_bounds C hC k (2 * r + 2) f b g v NT Gam hPar
  have hC0 : 0 < C := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hR : (1 : ℝ) ≤ r := by
    have h := hm4
    push_cast at h
    linarith
  have hMR : ((2 * r + 2 : ℕ) : ℝ) = 2 * (r : ℝ) + 2 := by push_cast; ring
  have hcore := exponent_inequality_single C k f ((2 * r + 2 : ℕ) : ℝ) (Real.log b) (Real.log k) (Real.log g) (Real.log C)
    (Real.log 2) hC hm4 hmf hfk hlb hlk hlC0 hlC hlg hl20 hl2 hX r (Real.log Gam) hR hMR hlG
  have hg1 : 0 < g⁻¹ ^ (2 * r + 1) := pow_pos (inv_pos.2 hg0) _
  have hk1 : 0 < ((k : ℝ) ^ r)⁻¹ := inv_pos.2 (pow_pos hk0 _)
  have hin : 0 < C * g⁻¹ ^ (2 * r + 1) * ((k : ℝ) ^ r)⁻¹ := mul_pos (mul_pos hC0 hg1) hk1
  have e4 : Real.sqrt ((C * g⁻¹ ^ (2 * r + 1) * ((k : ℝ) ^ r)⁻¹) ^ (k * f)) =
      Real.exp (((k : ℝ) * f) * (Real.log C - (2 * r + 1) * Real.log g - r * Real.log k) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (pow_pos hin _), Real.log_pow,
      Real.log_mul (mul_pos hC0 hg1).ne' hk1.ne', Real.log_mul hC0.ne' hg1.ne', Real.log_pow, Real.log_inv,
      Real.log_inv, Real.log_pow]
    congr 1
    push_cast
    ring
  rw [pow_eq_exp_mul_log C hC0 f, heightParameter_rpow C (2 * r + 2) f b _ hb0, ← Real.exp_log hGam0, e4]
  simp only [← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)
end Formalism.HermitianLatticeCounting.P
