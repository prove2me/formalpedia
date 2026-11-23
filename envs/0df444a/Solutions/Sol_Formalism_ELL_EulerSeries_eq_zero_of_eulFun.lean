-- Prove2me | solution 1 for Formalism.ELL.EulerSeries.eq_zero_of_eulFun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:58:53.024783+00:00
-- url     : https://prove2.me/submissions/3fdbf31d-551d-4cdd-aa8a-3cc01b1c02e7

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ConstantCoeffLogOnePlus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.EulerSeries
open Formalism.G Formalism.ELL
variable {K : Type*} [NormedField K] [CharZero K] {σ : Type} [DecidableEq σ]
namespace Formalism.ELL.EulerSeries
theorem _root_.solution (F : MvPowerSeries σ K) (h0 : MvPowerSeries.constantCoeff F = 0)
    (h : eulFun F = 0) : F = 0 := by
  ext d
  rw [map_zero]
  by_cases hd : d = 0
  · subst hd
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h0
  · have h1 := congrArg (MvPowerSeries.coeff d) h
    rw [coeff_eulFun, map_zero] at h1
    have hdeg : ((d.degree : ℕ) : K) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact fun h' => hd ((Finsupp.degree_eq_zero_iff d).mp h')
    exact (mul_eq_zero.mp h1).resolve_left hdeg
end Formalism.ELL.EulerSeries
