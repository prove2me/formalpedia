-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_of_ev_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:31:39.392863+00:00
-- url     : https://prove2.me/submissions/af803faa-ca85-41aa-a67a-6d14e6d91d03

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_fin_two_eq_one_sub_of_ne__93512bbd28f7
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (h : PS C 2 dd) (g : Fin 2) (a : Fin 2 → Pt C 1 dd) (hag : a g = 0)
    (hao : ∀ g', g' ≠ g → a g' = pt C dd 0) (hz : ev a h = 0) :
    ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0 := by
  intro e he
  set b : Fin 1 × Fin dd → PS C 2 dd := fun q => X (1 - g, q.2) with hb
  have hbS : HasSubst b := hasSubst_of_constantCoeff_zero fun q => constantCoeff_X _
  have haS : HasSubst (fun p : Fin 2 × Fin dd => a p.1 p.2) := by
    apply hasSubst_of_constantCoeff_zero
    intro s
    by_cases hs : s.1 = g
    · rw [hs, hag]; simp
    · rw [hao _ hs]; exact constantCoeff_X _
  have key : MvPowerSeries.subst b (ev a h) =
      rescale (fun s : Fin 2 × Fin dd => if s.1 = g then (0 : C) else 1) h := by
    unfold ev
    rw [subst_comp_subst_apply haS hbS, rescale_eq_subst]
    congr 1
    funext s
    by_cases hs : s.1 = g
    · have h1 : a s.1 s.2 = 0 := by rw [hs, hag]; rfl
      rw [h1, ← coe_substAlgHom hbS, map_zero]
      simp [hs]
    · have h1 : a s.1 s.2 = X ((0 : Fin 1), s.2) := by rw [hao _ hs]; rfl
      rw [h1, subst_X hbS]
      have h2 : s = (1 - g, s.2) := Prod.ext (fin_two_eq_one_sub_of_ne' g s.1 hs) rfl
      simp only [Pi.smul_apply', if_neg hs, one_smul, hb]
      rw [← h2]
  have h3 := congrArg (coeff e) key
  rw [hz, ← coe_substAlgHom hbS, map_zero, map_zero, coeff_rescale] at h3
  have h4 : (e.prod fun s m => (if s.1 = g then (0 : C) else 1) ^ m) = 1 := by
    unfold Finsupp.prod
    apply Finset.prod_eq_one
    intro s hs
    show (if s.1 = g then (0 : C) else 1) ^ e s = 1
    rw [if_neg (he s hs), one_pow]
  rw [h4, one_mul] at h3
  exact h3.symm
end Formalism.L2.FormalSeriesBounds
