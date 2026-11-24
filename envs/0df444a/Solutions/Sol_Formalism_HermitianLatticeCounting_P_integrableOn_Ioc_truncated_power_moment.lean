-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.integrableOn_Ioc_truncated_power_moment
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:45.571517+00:00
-- url     : https://prove2.me/submissions/60331157-a6e8-4087-b2dc-32de91abe996

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gl_cut_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {K L : ℝ} (hK : 0 ≤ K) :
    IntegrableOn (fun y : ℝ => y * TruncationCutoff K L y) (Set.Ioc 0 L) := by
  have hE : Set.EqOn (fun y : ℝ => y * TruncationCutoff K L y) (fun y => y) (Set.Ioc 0 L) :=
    fun y hy => gl_cut_le hK hy.1 hy.2
  refine IntegrableOn.congr_fun ?_ hE.symm measurableSet_Ioc
  exact (continuous_id'.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
end Formalism.HermitianLatticeCounting.P
