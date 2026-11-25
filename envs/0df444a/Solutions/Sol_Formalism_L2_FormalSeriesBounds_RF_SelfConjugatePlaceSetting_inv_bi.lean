-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.SelfConjugatePlaceSetting.inv_bi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:31:27.845885+00:00
-- url     : https://prove2.me/submissions/2f2c10fe-9e46-40c0-b972-a3f097856125

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_SelfConjugatePlaceSetting_inv_minor
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_ConjugatePairPlaceSetting_inv_minor


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
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N} {n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
namespace Formalism.L2.FormalSeriesBounds.RF
namespace SelfConjugatePlaceSetting
theorem _root_.solution (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g g' : Fin 2) (s s' : ZMod 2) {M : ℕ}
    (col : Fin M → Fin N) (k e1 e2 : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col
      (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1 *
        rename ((F o).letter g' s') (minorK C M ((X o).rkF g' s') k) ^ e2)) =
      PsiS r tau gm plc o col
      (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1 *
        rename ((F o).letter g' s') (minorK C M ((X o).rkF g' s') k) ^ e2) := by
  simp only [map_mul, map_pow]
  rw [H.inv_minor plc o g s col k σ i i' hi t, H.inv_minor plc o g' s' col k σ i i' hi t]
end SelfConjugatePlaceSetting
end Formalism.L2.FormalSeriesBounds.RF
