-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.cZ_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:35:33.15428+00:00
-- url     : https://prove2.me/submissions/96bcf883-77cd-4cdd-9c5e-3a0fd7fe97fe

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_zFRDirichlet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution : 0 < cZ :=
  lt_min (Classical.choose_spec Formalism.ZeroFreeDirichlet.zFRDirichlet).1 (by norm_num)
end Formalism.HermitianLattices.Ext.PrimesInProgressions
