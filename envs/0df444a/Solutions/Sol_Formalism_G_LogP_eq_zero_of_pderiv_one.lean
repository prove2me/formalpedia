-- Prove2me | solution 1 for Formalism.G.LogP.eq_zero_of_pderiv_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:34.010428+00:00
-- url     : https://prove2.me/submissions/93ba0951-d270-421e-8c9a-f81471e88158

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Theorems.Thm_Formalism_G_LogP_isUnit_natCast_succ
import Theorems.Thm_Formalism_G_LogP_subst_X0_zero_eq_rescale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]
namespace Formalism.G.LogP
theorem _root_.solution [Algebra ℚ R] {h : MvPowerSeries (Fin 2) R}
    (hD : MvPowerSeries.pderiv R 1 h = 0)
    (h0 : h.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = 0) : h = 0 := by
  rw [subst_X0_zero_eq_rescale] at h0
  ext n
  rw [map_zero]
  by_cases hn : n 1 = 0
  · have h1 := congrArg (MvPowerSeries.coeff n) h0
    rw [MvPowerSeries.coeff_rescale, map_zero] at h1
    have hprod : (n.prod fun s m => (![1, 0] : Fin 2 → R) s ^ m) = 1 := by
      rw [Finsupp.prod]
      apply Finset.prod_eq_one
      intro s hs
      fin_cases s
      · simp
      · exact absurd hn (Finsupp.mem_support_iff.mp hs)
    rw [hprod, one_mul] at h1
    exact h1
  · have hm : n = (n - Finsupp.single 1 1) + Finsupp.single 1 1 := by
      ext i
      fin_cases i <;> simp <;> omega
    have h1 := congrArg (MvPowerSeries.coeff (n - Finsupp.single 1 1)) hD
    rw [MvPowerSeries.coeff_pderiv, map_zero, ← hm] at h1
    have hu : IsUnit ((((n - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 : ℕ) : R) + 1) := isUnit_natCast_succ _
    exact (hu.mul_left_eq_zero).mp h1
end Formalism.G.LogP
