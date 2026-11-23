-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.eulerFac_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:33:43.518747+00:00
-- url     : https://prove2.me/submissions/f125bc23-999b-4459-8c9a-328afd342929

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit

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
open Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
namespace Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
theorem _root_.solution (M : ℕ) (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.eulerFac K M P = if Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P then (1 + smallTerm M P)⁻¹
      else (1 + smallTerm M P) ^ (-(1 : ℝ) / 2) := by
  unfold Formalism.HermitianLatticesTheory.eulerFac smallTerm
  split_ifs with hc <;> simp only [← sub_eq_add_neg]
end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
