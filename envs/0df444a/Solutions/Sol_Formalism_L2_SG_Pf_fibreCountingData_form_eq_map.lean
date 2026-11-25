-- Prove2me | solution 1 for Formalism.L2.SG.Pf.fibreCountingData.form_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:49:13.693385+00:00
-- url     : https://prove2.me/submissions/50903857-443a-4b67-b95d-2b5a76353268

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DivMulMemSPOfSub
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CondZIff
import Theorems.Thm_Formalism_L2_SG_Pf_fibreCountingData_diagQ_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_mk


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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.fibreCountingData
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsMaximal] {k : ℕ}
local notation "mk" => Ideal.Quotient.mk (extP K 𝔭 ^ k)
variable {m : ℕ} (a : Fin m → 𝓞 F)
variable {a}
namespace Formalism.L2.SG.Pf.fibreCountingData
theorem _root_.solution (Y : Matrix (Fin m) (Fin m) (𝓞 K)) [Fact (IsFixF K F)] :
    (Y.map mk)ᴴ * diagQ K 𝔭 k a * Y.map mk - diagQ K 𝔭 k a = (gramO a Y).map mk := by
  have hs : Function.Semiconj (Ideal.Quotient.mk (extP K 𝔭 ^ k)) star star :=
    fun x => (idealPowerSpanBounds.star_mk 𝔭 k x).symm
  have e : ∀ M : Matrix (Fin m) (Fin m) (𝓞 K),
      M.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = (Ideal.Quotient.mk (extP K 𝔭 ^ k)).mapMatrix M :=
    fun _ => rfl
  rw [e (gramO a Y)]
  unfold gramO
  rw [map_sub, map_mul, map_mul, ← e, ← e, ← e, diagQ_eq, Matrix.conjTranspose_map _ hs]
end Formalism.L2.SG.Pf.fibreCountingData
