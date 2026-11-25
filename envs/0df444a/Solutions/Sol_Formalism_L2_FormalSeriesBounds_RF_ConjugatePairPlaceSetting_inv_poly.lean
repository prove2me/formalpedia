-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.ConjugatePairPlaceSetting.inv_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:24:24.996453+00:00
-- url     : https://prove2.me/submissions/c621790e-3e24-4b0c-81b6-efd44da9766f

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_ConjugatePairPlaceSetting_inv_bi
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_ConjugatePairPlaceSetting_inv_ch
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_ConjugatePairPlaceSetting_inv_monAll
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
theorem _root_.solution (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (b : GlobalTheory d) (col : Fin (b.what₂ (X o).n) → Fin n)
    (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (rename (psiL r tau n o col) (b.poly (X o) (F o))) =
      rename (psiL r tau n o col) (b.poly (X o) (F o)) := by
  rcases b with ⟨g, a, j, y⟩ | ⟨g, a, u⟩ | ⟨g, e, N⟩
  · exact H.inv_bi o _ _ _ _ col _ _ _ σ i i' hi t
  · exact H.inv_ch o _ _ col _ _ σ i i' hi t
  · exact H.inv_monAll o _ col _ σ i i' hi t
end ConjugatePairPlaceSetting
end Formalism.L2.FormalSeriesBounds.RF
