-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.measurableSet_sBox
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:47.277739+00:00
-- url     : https://prove2.me/submissions/a409efb8-32b4-4f03-9e67-77e990c966a3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoTsumDivPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemIdealLatticeIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_sBox_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology MeasureTheory Pointwise
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution : MeasurableSet (sBox F) := by
  rw [sBox_eq]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Ioc).prod MeasurableSet.univ
end Formalism.HermitianLattices.Ext.L3.BoxSum
