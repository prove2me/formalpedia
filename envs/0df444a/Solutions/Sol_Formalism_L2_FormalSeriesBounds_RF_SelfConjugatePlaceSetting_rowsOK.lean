-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.SelfConjugatePlaceSetting.rowsOK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T06:13:34.724332+00:00
-- url     : https://prove2.me/submissions/51ab4ca3-6e2e-45fe-8b9c-94b94828c749

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PderivSubGOff
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCHarm
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_zmod_two_add_one_add_one_eq
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_SelfConjugatePlaceSetting_rkF_eq
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_rkF_eq
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_exists_rowsOK
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_le_sum_map
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_plAt_inj
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rowsOK_prodAll
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2


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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
variable {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
  {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
  {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N}
namespace Formalism.L2.FormalSeriesBounds.RF
namespace SelfConjugatePlaceSetting
theorem _root_.solution (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) :
    ∃ kind : Fin N → Knd 2, RowsOK (X o).G (X o).Alt
      (prodAll (plAt N pl o) fun i => (blkAt L o i).poly (X o) (F o)) kind := by
  have h : ∀ i : Fin (L o).length, ∃ kind : Fin (rowsAt X L o i) → Knd 2,
      RowsOK (X o).G (X o).Alt ((blkAt L o i).poly (X o) (F o)) kind := by
    intro i
    refine exists_rowsOK (X o) (F o) (Or.inl (H.alt o)) (H.hj o) _ fun g t k hk => ?_
    have hsum : ∀ s, (blkAt L o i).wt (X o) 0 s k + (blkAt L o i).wt (X o) 1 (s + 1) k ≤ gaC o s k := by
      intro s
      rw [← H.wt o s k]
      exact le_sum_map (L o) (fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + 1) k) (List.get_mem (L o) i)
    by_cases hg : g = 0
    · subst hg
      have h1 := hsum t
      exact (H.supp o t k (by omega)).2
    · have hg1 : g = 1 := Fin.eq_one_of_ne_zero g hg
      subst hg1
      have h1 := hsum (t + 1)
      rw [zmod_two_add_one_add_one_eq] at h1
      have h2 := (H.supp o (t + 1) k (by omega)).2
      rw [H.rkF_eq o 0 (t + 1)] at h2
      rw [H.rkF_eq o 1 t]
      exact h2
  choose kind hk using h
  exact ⟨_, rowsOK_prodAll _ _ (plAt_inj N H.plinj o) _ kind hk⟩
end SelfConjugatePlaceSetting
end Formalism.L2.FormalSeriesBounds.RF
