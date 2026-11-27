-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.lab_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:48:39.606295+00:00
-- url     : https://prove2.me/submissions/c757c777-007f-4602-a4a1-2476f923cf26

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PderivSubGOff
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCHarm
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
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N}
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution : ∀ g1 g2 : Fin 2, g1 ≠ g2 → ∀ t : ZMod 2,
    (if g1 = 0 then t else t + 1) = (if g2 = 0 then t + 1 else t + 1 + 1) := by
  decide
end Formalism.L2.FormalSeriesBounds.RF
