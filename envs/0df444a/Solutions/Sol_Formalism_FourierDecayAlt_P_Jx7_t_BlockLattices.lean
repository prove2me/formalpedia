-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.t_BlockLattices
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:45.700625+00:00
-- url     : https://prove2.me/submissions/60056694-f73a-4a7b-9139-7ec13827f769

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_idl_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_sqrt_idl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution : BlockLattices := by
  intro hL hI hN E _ _ _ hU g r b s hg
  obtain ⟨-, -, -, -, f5, -, -, -, -, -, -, -⟩ := hL E hU g (S6.nuBlock r b 1) 1 hg
  obtain ⟨-, -, -, -, k5, -, k7, -, -, -, -, -⟩ := hL E hU g (S6.nuBlock r b s) s hg
  refine ⟨fun l hl => f5 hl, fun l hl => k5 hl, fun l hl => k7 hl, idl_ne_zero hN E g _ _ hg,
    idl_ne_zero hN E g _ _ hg, ?_, ?_, ?_⟩
  · have := (hI E g r b ((s + 1 : ℕ) : ℤ)).1
    rw [this]; congr 2; push_cast; ring
  · unfold S6.dualIdl
    rw [sqrt_idl hN E g _ hg]
    congr 4; unfold S6.nuBlock; ring
  · unfold S6.liftIdl
    rw [sqrt_idl hN E g _ hg]
    congr 4
end Formalism.FourierDecayAlt.P.Jx7
