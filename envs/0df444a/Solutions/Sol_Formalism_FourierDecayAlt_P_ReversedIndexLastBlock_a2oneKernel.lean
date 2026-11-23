-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.a2oneKernel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:51.226879+00:00
-- url     : https://prove2.me/submissions/5345b7d4-de67-432f-b047-0434375228a2

import Definitions.Def_Formalism_HermitianCurvature_StatementA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondKernelPropertyKernel
import Theorems.Thm_Formalism_FourierDecayAlt_P_ReversedIndexLastBlock_a2one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
open Formalism.DoubleCosetMeasures
namespace Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
theorem _root_.solution : Formalism.FourierDecayAlt.A.LevelOneKernelPair := by
  intro K _ _ _ R l l' t t' ψ C _ _ e lam m1 m2 m3 m4 h1 h2
  have e1 := a2one K R l t ψ C e lam m1 m2 h1
  have e2 := a2one K R l' t' ψ C e lam m3 m4 h2
  have h3 := e1.symm.trans e2
  rw [Submodule.Quotient.eq] at h3
  obtain ⟨r, hr⟩ := LinearMap.mem_range.mp h3
  rw [← hr]
  exact r.2
end Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
