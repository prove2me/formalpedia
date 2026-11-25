-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.subst_ev_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:49:06.92298+00:00
-- url     : https://prove2.me/submissions/6e933d33-61ae-44d1-8d72-7af394424781

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_rescale
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_fin_two_eq_one_sub_of_ne__93512bbd28f7


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (h : PS C 2 dd) (g : Fin 2) (a : Fin 2 → Pt C 1 dd) (hag : a g = 0)
    (hao : ∀ g', g' ≠ g → a g' = pt C dd 0) :
    MvPowerSeries.subst (fun q : Fin 1 × Fin dd => (MvPowerSeries.X (1 - g, q.2) : PS C 2 dd)) (ev a h) =
      MvPowerSeries.rescale (fun s : Fin 2 × Fin dd => if s.1 = g then (0 : C) else 1) h := by
  have hbS : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => (MvPowerSeries.X (1 - g, q.2) : PS C 2 dd)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => MvPowerSeries.constantCoeff_X _
  have haS : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin dd => a p.1 p.2) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s
    by_cases hs : s.1 = g
    · rw [hs, hag]; simp
    · rw [hao _ hs]; exact MvPowerSeries.constantCoeff_X _
  unfold ev
  rw [MvPowerSeries.subst_comp_subst_apply haS hbS, MvPowerSeries.rescale_eq_subst]
  congr 1
  funext s
  by_cases hs : s.1 = g
  · have h1 : a s.1 s.2 = 0 := by rw [hs, hag]; rfl
    rw [h1, ← MvPowerSeries.coe_substAlgHom hbS, map_zero]
    simp [hs]
  · have h1 : a s.1 s.2 = MvPowerSeries.X ((0 : Fin 1), s.2) := by rw [hao _ hs]; rfl
    rw [h1, MvPowerSeries.subst_X hbS]
    have h2 : s = (1 - g, s.2) := Prod.ext (fin_two_eq_one_sub_of_ne' g s.1 hs) rfl
    simp only [Pi.smul_apply', if_neg hs, one_smul]
    rw [← h2]
end Formalism.L2.FormalSeriesBounds
