-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.conjIdeal_conjIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:16:49.729895+00:00
-- url     : https://prove2.me/submissions/3ba58fe9-8c33-43b1-986a-c1f24ea7bbc9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSubMemOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjIdeal_eq_comap

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
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) = P := by
  ext x
  simp only [conjIdeal_eq_comap, Ideal.mem_comap, conjO_conjO]
end Formalism.HermitianLattices.Ext.L3
