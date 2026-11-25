-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.mem_skSet_of_solve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:12:12.569521+00:00
-- url     : https://prove2.me/submissions/505ffeeb-f822-450c-84c2-f7070b734e83

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapesBis
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagQConjTranspose
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_form_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}
namespace Formalism.L2.SG.Pf.discriminantNormShapes
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    {Y P W Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y)
    (hW : Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a)
    (hZ : W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z = 0) :
    Y + Z * diagQ K 𝔭 k a ∈ skSet K 𝔭 k a := by
  show (Y + Z * diagQ K 𝔭 k a)ᴴ * diagQ K 𝔭 k a * (Y + Z * diagQ K 𝔭 k a) = diagQ K 𝔭 k a
  have h := form_shift hPY hW Z
  rw [hZ, Matrix.mul_zero, Matrix.zero_mul] at h
  exact sub_eq_zero.mp h
end Formalism.L2.SG.Pf.discriminantNormShapes
