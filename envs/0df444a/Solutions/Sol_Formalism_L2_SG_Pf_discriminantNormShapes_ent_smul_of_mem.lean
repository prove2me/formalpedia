-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.ent_smul_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:13:19.310775+00:00
-- url     : https://prove2.me/submissions/94ea31b6-79e5-40f6-898e-3cbd3183e214

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_EntOfMapEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {c : Type} [Fintype c] [DecidableEq c]
namespace Formalism.L2.SG.Pf.discriminantNormShapes
theorem _root_.solution {J : Ideal (𝓞 K)} {x : 𝓞 K} (hx : x ∈ J) (A : Matrix c c (𝓞 K)) :
    Ent J (x • A) := fun i j => J.mul_mem_right _ hx
end Formalism.L2.SG.Pf.discriminantNormShapes
