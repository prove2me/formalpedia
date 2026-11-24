-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.ent_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:18:40.888412+00:00
-- url     : https://prove2.me/submissions/a83897f7-b443-4f66-92ee-9518dd6725c7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_EntOfMapEqZero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow


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
theorem _root_.solution (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) {A : Matrix c c (𝓞 K)}
    (hA : Ent (extP K 𝔭 ^ k) A) : Ent (extP K 𝔭 ^ k) Aᴴ := fun i j => conjO_mem_pow hF 𝔭 k _ (hA j i)
end Formalism.L2.SG.Pf.discriminantNormShapes
