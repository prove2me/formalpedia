-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.hStabFB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:09:01.164852+00:00
-- url     : https://prove2.me/submissions/22043b6c-a701-4a87-a850-512cf847eb85

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_bil_smul_left
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_bil_smul_right
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_bil_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_fin_two_eq_zero_or_eq_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_bil_ad
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_raw_first_pairing_eq
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg


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
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution : HStabFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g c q hty
  have hconj : ∀ (g : Fin 2) t a, p.em (1 - g) t (star a) = p.em g t a := by
    intro g t a
    rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
    · show p.em 1 t (star a) = p.em 0 t a
      rw [p.em_conj, star_star]
    · show p.em 0 t (star a) = p.em 1 t a
      rw [p.em_conj]
  obtain ⟨a, ha⟩ := p.em_sep (g, p.ty g c) (g, p.ty (1 - g) q) (fun h => hty (Prod.mk.inj h).2)
  have ha' : V.v (p.em g (p.ty g c) a - p.em g (p.ty (1 - g) q) a) = 0 := ha
  have hb := Y.bil_ad a (p.u g c) (p.u (1 - g) q)
  rw [p.u_eig g c a, p.u_eig (1 - g) q (star a), hconj, bil_smul_left, bil_smul_right, ← sub_mul] at hb
  have hint : V.Ge 0 (bil (Y.B.ad a) (p.u g c) (p.u (1 - g) q)) :=
    bil_int (Y.intAd a) (p.u_int g c) (p.u_int (1 - g) q)
  rw [hb] at hint
  have hβ : V.Ge 0 (bil Y.h (p.u g c) (p.u (1 - g) q)) := by
    unfold VF.Ge at hint ⊢
    rwa [V.v.map_mul, ha', zero_add] at hint
  show V.Ge 0 ((Y.raw p).sg1 (p.u g c) (p.u (1 - g) q))
  rw [Y.raw_first_pairing_eq]
  exact hβ.neg
end Formalism.L2.FormalSeriesBounds
