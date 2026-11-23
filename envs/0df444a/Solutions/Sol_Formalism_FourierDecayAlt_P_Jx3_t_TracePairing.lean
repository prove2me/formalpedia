-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx3.t_TracePairing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:44.705795+00:00
-- url     : https://prove2.me/submissions/48d2c5bb-6fb0-4d1e-987f-f6703436f424

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_trace_places

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3
namespace Formalism.FourierDecayAlt.P.Jx3
theorem _root_.solution : TracePairing := by
  intro E _ _ _ g c l t hg hc
  have hg' : (g : ℝ) ≠ 0 := by positivity
  rw [trace_places, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [dm, semb, cemb, AddMonoidHom.comp_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    LinearMap.toAddMonoidHom_coe, LinearMap.smul_apply, LinearMap.id_apply, Complex.inner,
    PiLp.smul_apply, map_mul, map_div₀, map_natCast, Complex.conj_ofReal, Complex.conj_conj,
    Complex.real_smul]
  have : (↑c * w.embedding t) * (((2 / ((g : ℝ) * c) : ℝ) : ℂ) * w.embedding l) =
      ((2 / (g : ℝ) : ℝ) : ℂ) * (w.embedding l * w.embedding t) := by
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
    push_cast; field_simp
  have h2 : w.embedding l * w.embedding t / (g : ℂ) =
      ((1 / (g : ℝ) : ℝ) : ℂ) * (w.embedding l * w.embedding t) := by
    have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
    push_cast; field_simp
  rw [this, h2, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring
end Formalism.FourierDecayAlt.P.Jx3
