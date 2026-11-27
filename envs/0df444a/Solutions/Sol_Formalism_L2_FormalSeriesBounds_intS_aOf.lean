-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.intS_aOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:36:17.715422+00:00
-- url     : https://prove2.me/submissions/0fb5d48f-c04d-4861-a23b-11667ad123e7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstStepSecondHalfCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieProj
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerateOfUnitSeriesIntegral
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mul
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_mul
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_pow
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_sum
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_u1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (h : IntS V Y.u1) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) : IntS V (Y.aOf u) := by
  intro ν
  show V.Ge 0 (∑ i, u i ^ V.l * MvPowerSeries.coeff
    (Finsupp.single ((0 : Fin 2), i) V.l + ν.mapDomain (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2))) Y.u1)
  exact VF.Ge.sum fun i _ => by simpa using ((hu i).pow V.l).mul (h _)
end Formalism.L2.FormalSeriesBounds
