-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.SelfConjugatePlaceSetting.en_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:21:52.272803+00:00
-- url     : https://prove2.me/submissions/72f0ee8a-e987-4ff0-bd1e-50bdae1d75c6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
theorem _root_.solution (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2)
    (q : Fin ((X o).rkF g s)) : ((F o).en g s q).1 = trueT g s := by
  have h1 := (F o).en_ty g s q
  rw [H.hty o g] at h1
  unfold trueT
  generalize ((F o).en g s q).1 = u at h1 ⊢
  split_ifs at h1 ⊢ with hg
  · exact h1
  · subst h1
    have h2 : (1 : ZMod 2) + 1 = 0 := rfl
    rw [add_assoc, h2, add_zero]
end SelfConjugatePlaceSetting
end Formalism.L2.FormalSeriesBounds.RF
