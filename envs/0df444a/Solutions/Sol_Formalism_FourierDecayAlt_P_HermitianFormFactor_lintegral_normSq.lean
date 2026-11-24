-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.lintegral_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:19:42.661195+00:00
-- url     : https://prove2.me/submissions/256ff3f8-6b54-4214-a859-f67f07570655

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (ψ : ℝ → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ z : ℂ, ψ (Complex.normSq z) = ENNReal.ofReal Real.pi * ∫⁻ s in Set.Ioi (0 : ℝ), ψ s := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have h1 : ∀ p : ℝ × ℝ, Complex.normSq (Complex.polarCoord.symm p) = p.1 ^ 2 := by
    intro p
    rw [Complex.normSq_eq_norm_sq, Complex.norm_polarCoord_symm, sq_abs]
  simp_rw [h1]
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ (by fun_prop)]
  simp only [smul_eq_mul, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Ioo]
  have him : (fun x : ℝ => x ^ 2) '' Set.Ioi (0 : ℝ) = Set.Ioi 0 := by
    ext s
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact pow_pos (show (0 : ℝ) < x from hx) 2
    · intro hs
      exact ⟨Real.sqrt s, Real.sqrt_pos.2 hs, Real.sq_sqrt (le_of_lt hs)⟩
  have h2 := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.Ioi (0 : ℝ)) (f := fun x : ℝ => x ^ 2)
    (f' := fun x => 2 * x) measurableSet_Ioi
    (fun x _ => by simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt)
    (fun x hx y hy hxy => by
      have hx' : (0 : ℝ) ≤ x := le_of_lt hx
      have hy' : (0 : ℝ) ≤ y := le_of_lt hy
      exact (pow_left_inj₀ hx' hy' two_ne_zero).1 hxy) ψ
  rw [him] at h2
  rw [h2, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  have e1 : ENNReal.ofReal (Real.pi - -Real.pi) = ENNReal.ofReal Real.pi * 2 := by
    rw [show Real.pi - -Real.pi = Real.pi * 2 by ring, ENNReal.ofReal_mul Real.pi_pos.le]; simp
  have e2 : ENNReal.ofReal |2 * x| = 2 * ENNReal.ofReal x := by
    rw [abs_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num)]; simp
  simp only [e1, e2]
  ring
end Formalism.FourierDecayAlt.P.HermitianFormFactor
