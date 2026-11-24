-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormResidues.vecEquiv_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:33.231213+00:00
-- url     : https://prove2.me/submissions/121813c6-e894-4561-8b76-2064005f966c

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
open NormResidues
open Formalism.HermitianLattices.Ext.L3.NormResidues
namespace Formalism.HermitianLattices.Ext.L3.NormResidues
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P)
    (M : ℕ) (x : Fin M → 𝓞 K ⧸ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) (i : Fin M) :
    (vecEquiv hP hc M x).1 i = (pairLift hP hc (x i)).1 := rfl
end Formalism.HermitianLattices.Ext.L3.NormResidues
