-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx2.t_BlockLattices
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:14.98356+00:00
-- url     : https://prove2.me/submissions/0e4c5457-4ecf-4daf-8fdf-77c27efc8030

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_idl_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_sqrt_idl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx2
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped nonZeroDivisors ComplexConjugate
namespace Formalism.FourierDecayAlt.P.Jx2
theorem _root_.solution : BlockLattices := by
  intro hLG _ hN E _ _ _ hU g r b s hg
  have F1 := hLG E hU g (S6.nuBlock r b 1) 1 hg
  have Fs := hLG E hU g (S6.nuBlock r b s) s hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    exact F1.2.2.2.2.1 hl
  · intro l hl
    exact Fs.2.2.2.2.1 hl
  · intro l hl
    exact Fs.2.2.2.2.2.2.1 hl
  · exact idl_ne_zero hN E g (-1) (-(S6.nuBlock r b s + 1)) hg
  · exact idl_ne_zero hN E g (-1) (-(S6.nuBlock r b s)) hg
  · simp only [S6.liftIdl, S6.dualIdl, S6.nuBlock]
    congr 1
    push_cast
    ring
  · have hν : S6.nuBlock r b s + 1 = (2 * r + 4 : ℤ) - 2 * b - s := by
      simp only [S6.nuBlock]
      ring
    rw [show S6.dualIdl E g (S6.nuBlock r b s) = S6.idl E g (-1) (-(S6.nuBlock r b s + 1)) from rfl,
      sqrt_idl hN E g _ hg, hν]
  · rw [show S6.liftIdl E g (S6.nuBlock r b s) = S6.idl E g (-1) (-(S6.nuBlock r b s)) from rfl,
      sqrt_idl hN E g _ hg]
    try rfl
end Formalism.FourierDecayAlt.P.Jx2
