-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.mem_conjIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:15.348728+00:00
-- url     : https://prove2.me/submissions/90cc1d49-ce6b-4c95-9644-1510b2480b31

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapNeZeroOfMemHcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjIdeal_eq_comap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.WA
theorem _root_.solution (p : Ideal (𝓞 K)) (r : 𝓞 K) :
    r ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p ↔ conjO K r ∈ p := by
  rw [conjIdeal_eq_comap, Ideal.mem_comap]
end Formalism.HermitianLattices.Ext.L3.WA
