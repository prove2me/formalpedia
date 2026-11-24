-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.QuadAdj.conj_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:11.164844+00:00
-- url     : https://prove2.me/submissions/1eed71c6-8ff3-47d0-80b4-42b2a4e565f9

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandDA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.QuadAdj
variable {F : Type*} [Field F] (c : F)
namespace Formalism.HermitianLattices.Ext.L3.QuadAdj
theorem _root_.solution : conj c (AdjoinRoot.root _) = -AdjoinRoot.root _ := conjHom_root c
end Formalism.HermitianLattices.Ext.L3.QuadAdj
