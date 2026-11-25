-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.ConjugatePairPlaceSetting.inv_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:22:42.775472+00:00
-- url     : https://prove2.me/submissions/842e97bf-92c8-432f-ab4f-3335a4258ffa

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_rowShift_minor
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_ConjugatePairPlaceSetting_key_letter
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
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → Fin 2 → ZMod d → T} {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (IIof r tau o) (J o)} {F : ∀ o, Flag (X o)} {Z : Finset Orb}
  {ga : Orb → Fin 2 → ZMod d → ℕ → ℕ} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n}
namespace Formalism.L2.FormalSeriesBounds.RF
namespace ConjugatePairPlaceSetting
theorem _root_.solution (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (g : Fin 2) (s : ZMod d) {N : ℕ}
    (col : Fin N → Fin n) (k : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (rename (psiL r tau n o col) (rename ((F o).letter g s) (minorK C N ((X o).rkF g s) k))) =
      rename (psiL r tau n o col) (rename ((F o).letter g s) (minorK C N ((X o).rkF g s) k)) := by
  rw [rename_rename]
  exact rowShift_minor _ (tau o g s) col (fun ρ c => H.key_letter o g s col ρ c) σ i i' hi t k
end ConjugatePairPlaceSetting
end Formalism.L2.FormalSeriesBounds.RF
