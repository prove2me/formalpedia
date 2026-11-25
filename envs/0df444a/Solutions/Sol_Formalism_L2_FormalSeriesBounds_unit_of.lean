-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.unit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:41:02.636013+00:00
-- url     : https://prove2.me/submissions/0c9e209d-74be-491d-b89c-bdfcf10ed2ea

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValU
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_IsIU_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_IsIU_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_IsIU_prod
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWtG_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWtG_one
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_one
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mvExp
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_hs
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_pullback_one_var_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_pullback_one_var_prod


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (hP : ProjPullSt Y p) (h1 : BiaddSt Y p)
    (h2 : CrossSt Y p) (h3 : PairSt Y p) : UnitSt Y p := by
  intro hs
  choose π hπi hπc hπp using hP hs
  have hproj : IsProj Y p π := ⟨hπi, hπc, hπp⟩
  obtain ⟨U0, hU0, hE⟩ := h1 hs π hproj
  choose Uc hUc hUceq using h2 hs π hproj
  choose Up hUp hUpeq using h3 hs π hproj

  let W : Orb × Fin 2 → Orb × Fin 2 → PS C 1 dd := fun s s' =>
    if h : s' ≠ barS s then Uc s s' h else 1
  have hW : ∀ s s', IsIU V (W s s') := by
    intro s s'
    by_cases h : s' ≠ barS s
    · simp only [W, dif_pos h]; exact hUc s s' h
    · simp only [W, dif_neg h]; exact IsIU.one
  have hone : pull1 Y p (1 : PS C 1 dd) = 1 := by
    have := VP.pullback_one_var_prod (Y := Y) (p := p) (∅ : Finset Unit) (fun _ => 1)
    simpa using this
  have hA : ∀ s s', pull1 Y p (Aterm Y π s s') =
      pull1 Y p (W s s') * (if s' = barS s then pull1 Y p (Aterm Y π s (barS s)) else 1) := by
    intro s s'
    by_cases h : s' = barS s
    · have h' : ¬ s' ≠ barS s := not_not.2 h
      simp only [W, dif_neg h', if_pos h, hone, one_mul]
      rw [h]
    · simp only [W, dif_pos h, if_neg h, mul_one]
      exact hUceq s s' h
  have hpair : ∏ s : Orb × Fin 2, pull1 Y p (Aterm Y π s (barS s)) =
      ∏ o, (pull1 Y p (Up o) * toAllS o (mvExp (Y.raw (p o)).hRow)) := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun o _ => ?_
    rw [Fin.prod_univ_two]
    have hb0 : barS (o, (0 : Fin 2)) = (o, 1) := by simp [barS]
    have hb1 : barS (o, (1 : Fin 2)) = (o, 0) := by simp [barS]
    rw [hb0, hb1]
    exact hUpeq o
  refine ⟨U0 * (∏ s, ∏ s', W s s') * ∏ o, Up o,
    ((hU0.mul (IsIU.prod _ fun s _ => IsIU.prod _ fun s' _ => hW s s')).mul
      (IsIU.prod _ fun o _ => hUp o)).1,
    ((hU0.mul (IsIU.prod _ fun s _ => IsIU.prod _ fun s' _ => hW s s')).mul
      (IsIU.prod _ fun o _ => hUp o)).2, ?_⟩
  rw [hE]
  rw [Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun s' _ => hA s s']
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  rw [hpair, Finset.prod_mul_distrib, VP.pullback_one_var_mul, VP.pullback_one_var_mul, VP.pullback_one_var_prod, VP.pullback_one_var_prod]
  simp_rw [VP.pullback_one_var_prod]
  ring
end Formalism.L2.FormalSeriesBounds
