-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormResidues.conjO_sum_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:32.675846+00:00
-- url     : https://prove2.me/submissions/48f4e567-87ac-400c-ac68-3a3100287a17

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.HermitianLattices.Ext.L3.NormResidues
namespace Formalism.HermitianLattices.Ext.L3.NormResidues
theorem _root_.solution {M : ℕ} (y : Fin M → 𝓞 K) :
    conjO K (∑ i, conjO K (y i) * y i) = ∑ i, conjO K (y i) * y i := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, conjO_conjO, mul_comm]
end Formalism.HermitianLattices.Ext.L3.NormResidues
