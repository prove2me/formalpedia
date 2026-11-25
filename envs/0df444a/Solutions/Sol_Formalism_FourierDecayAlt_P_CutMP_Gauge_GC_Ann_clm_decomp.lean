-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.clm_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:59:32.666664+00:00
-- url     : https://prove2.me/submissions/7f86b4ba-5649-4516-bce0-f89fb1ae82a8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtPrim
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FderivDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
    L v = (1 / 2 : ℂ) * (L 1 - I * L I) * v + (1 / 2 : ℂ) * (L 1 + I * L I) * (starRingEnd ℂ v) := by

  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, v = x + y * I := ⟨v.re, v.im, (Complex.re_add_im v).symm⟩
  have e : (x : ℂ) + y * I = x • (1 : ℂ) + y • I := by rw [Complex.real_smul, Complex.real_smul, mul_one]
  have hL : L ((x : ℂ) + y * I) = (x : ℂ) * L 1 + (y : ℂ) * L I := by
    rw [e, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  rw [hL]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination ((y : ℂ) * L I) * Complex.I_sq
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
