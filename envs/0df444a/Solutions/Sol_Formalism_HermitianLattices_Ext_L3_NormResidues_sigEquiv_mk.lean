-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormResidues.sigEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:02.873969+00:00
-- url     : https://prove2.me/submissions/7383bc9d-f90b-46ce-9535-0c76a974fb4e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne

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
theorem _root_.solution (P : Ideal (𝓞 K)) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (x : 𝓞 K) :
    sigEquiv P hc (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (conjO K x) := rfl
end Formalism.HermitianLattices.Ext.L3.NormResidues
