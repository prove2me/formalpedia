-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.homogeneity_natural_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:41:25.002604+00:00
-- url     : https://prove2.me/submissions/9e264cc0-7251-441a-a6a5-e634d1334f2c

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MvPolynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open PartialDerivativeAlgebra
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C6.SSNatHomog := by
  intro m m' E _ _ OO h1 h2 w w' Gv T T' th hGv hT hT' _ _
  simp only [C6.unitOf]
  rw [h1, h2, smul_smul, smul_smul]
  congr 1
  have hc : 0 < Real.sqrt (T * T') := Real.sqrt_pos.mpr (mul_pos hT hT')
  have hab : Real.sqrt (T / Gv) * Real.sqrt (T' / Gv) = Real.sqrt (T * T') / Gv := by
    rw [← Real.sqrt_mul (div_nonneg hT.le hGv.le),
      show T / Gv * (T' / Gv) = (T * T') / (Gv * Gv) by ring,
      Real.sqrt_div' _ (mul_self_nonneg Gv), Real.sqrt_mul_self hGv.le]
  have hab' : ((Real.sqrt (T / Gv) : ℝ) : ℂ) * ((Real.sqrt (T' / Gv) : ℝ) : ℂ)
      = ((Real.sqrt (T * T') : ℝ) : ℂ) / (Gv : ℂ) := by
    rw [← Complex.ofReal_mul, hab, Complex.ofReal_div]
  have hc' : ((Real.sqrt (T * T') : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hG' : (Gv : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hGv.ne'
  rw [mul_assoc, hab']
  field_simp
end Formalism.FourierDecayAlt.P
