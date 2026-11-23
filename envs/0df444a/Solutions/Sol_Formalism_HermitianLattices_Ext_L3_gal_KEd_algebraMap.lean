-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.gal_KEd_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:38.783824+00:00
-- url     : https://prove2.me/submissions/a297cac7-5a8a-4b30-84c6-45d12f78f9fa

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandDA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (w : K) (hw0 : w ≠ 0) (hw : star w = -w) (d : cmF K) [Fact (Irreducible (polE d))]
  [Fact (Irreducible (polKE d (skewSq w hw)))]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (τ : KEd d (skewSq w hw) ≃ₐ[Ed d] KEd d (skewSq w hw)) (a : cmF K) :
    τ (algebraMap (cmF K) (KEd d (skewSq w hw)) a) = algebraMap (cmF K) (KEd d (skewSq w hw)) a :=
  τ.commutes (algebraMap (cmF K) (Ed d) a)
end Formalism.HermitianLattices.Ext.L3
