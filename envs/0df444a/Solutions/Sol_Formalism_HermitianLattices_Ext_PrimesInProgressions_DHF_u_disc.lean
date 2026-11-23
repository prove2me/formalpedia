-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.u_disc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:19.760507+00:00
-- url     : https://prove2.me/submissions/83a22363-beb9-44b1-a7de-b44a1cc3d86f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
theorem _root_.solution (η : ℝ) (hη : 0 < η) (w : ℂ) (hw : η ≤ w.re) :
    ‖(η : ℂ) / w‖ ^ 2 ≤ ((η : ℂ) / w).re := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw
    linarith
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.2 hw0
  rw [norm_div, div_pow, Complex.sq_norm, Complex.sq_norm, Complex.div_re, Complex.normSq_ofReal,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  have h1 : η * η ≤ η * w.re := mul_le_mul_of_nonneg_left hw hη.le
  simp only [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hn.le)
end Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
