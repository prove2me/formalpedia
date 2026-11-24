-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.ent_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:19:26.336163+00:00
-- url     : https://prove2.me/submissions/ae60574c-f05e-445d-a395-f0a2137e80a0

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
theorem _root_.solution {J : Ideal (𝓞 K)} {A B : Matrix c c (𝓞 K)} (hA : Ent J A) (hB : Ent J B) :
    Ent J (A - B) := fun i j => J.sub_mem (hA i j) (hB i j)
end Formalism.L2.SG.Pf.discriminantNormShapes
