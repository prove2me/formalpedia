-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.critical_threshold_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:05.108751+00:00
-- url     : https://prove2.me/submissions/6c76ea44-4117-4cc3-a7a7-43c1011ade65

import Definitions.Def_Formalism_FlagUnipotentLattices_UnitSumBound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ConstantProductFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLatticeCounting.LocalIntegralStructure
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.LocalIntegralStructure.TcritForm := by
  intro k r T' g v rd Vd VV Tc hT' hg hv hrd hVd hVV hTc h
  have hpi := Real.pi_pos
  have hρ : 0 < rd ^ (((2 * r + 1 : ℕ) : ℝ) / 2) := Real.rpow_pos_of_pos hrd _
  generalize rd ^ (((2 * r + 1 : ℕ) : ℝ) / 2) = ρ at h hρ ⊢
  have hka : 0 < Real.pi / v := by positivity
  generalize Real.pi / v = ka at h hka ⊢
  generalize (2 * r + 2) * (2 * r + 1) / 2 = N at h ⊢
  rw [pow_add, pow_add, pow_mul, mul_comm k, pow_mul] at h
  rw [mul_pow, div_pow, inv_pow, div_pow, div_pow]
  have h1 : 0 < (g ^ (2 * r + 2)) ^ k := by positivity
  have h2 : 0 < (ka ^ (2 * r + 1)) ^ k := by positivity
  have h3 : 0 < Tc ^ k := by positivity
  have h4 : 0 < T' ^ k := by positivity
  have h5 : 0 < g ^ N := by positivity
  have h6 : 0 < ka ^ N := by positivity
  generalize (g ^ (2 * r + 2)) ^ k = A at h h1 ⊢
  generalize (ka ^ (2 * r + 1)) ^ k = B at h h2 ⊢
  generalize Tc ^ k = C at h h3 ⊢
  generalize T' ^ k = D at h4 ⊢
  generalize g ^ N = E at h h5 ⊢
  generalize ka ^ N = F at h h6 ⊢
  field_simp at h ⊢
  linear_combination h
end Formalism.HermitianLatticeCounting.P
