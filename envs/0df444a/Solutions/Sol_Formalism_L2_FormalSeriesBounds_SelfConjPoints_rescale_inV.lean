-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.SelfConjPoints.rescale_inV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:59:55.839675+00:00
-- url     : https://prove2.me/submissions/2bf6eaec-a606-4d35-8d10-f85723618b16

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RescaleInV
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjPoints_hsX
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_rescale
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.SelfConjPoints
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
namespace Formalism.L2.FormalSeriesBounds.SelfConjPoints
theorem _root_.solution (w : Fin 2 → C) (j : Fin 2) (f : PowerSeries C) :
    MvPowerSeries.rescale w (inV j f) = inV j (PowerSeries.rescale (w j) f) := by
  have hw : MvPowerSeries.HasSubst (w • MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  have hc : MvPowerSeries.HasSubst (fun _ : Unit => (w j • PowerSeries.X : PowerSeries C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by
      show MvPowerSeries.constantCoeff (w j • (PowerSeries.X : PowerSeries C)) = 0
      rw [MvPowerSeries.smul_eq_C_mul, map_mul,
        show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries C) = 0 from MvPowerSeries.constantCoeff_X (), mul_zero]
  unfold inV
  rw [MvPowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst]
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply (hsX j) hw, MvPowerSeries.subst_comp_subst_apply hc (hsX j)]
  congr 1
  funext u
  rw [MvPowerSeries.subst_X hw, ← MvPowerSeries.coe_substAlgHom (hsX j), map_smul, MvPowerSeries.coe_substAlgHom (hsX j)]
  have h1 : MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries (Fin 2) C)) (PowerSeries.X : PowerSeries C) =
      MvPowerSeries.X j := MvPowerSeries.subst_X (hsX j) ()
  rw [h1]
  rfl
end Formalism.L2.FormalSeriesBounds.SelfConjPoints
