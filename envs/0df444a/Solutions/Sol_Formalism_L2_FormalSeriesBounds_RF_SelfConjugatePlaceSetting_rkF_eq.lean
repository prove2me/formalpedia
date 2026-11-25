-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.SelfConjugatePlaceSetting.rkF_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:31:15.436057+00:00
-- url     : https://prove2.me/submissions/16eff38d-4034-44c5-a98f-c00a643560e0

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IsWHLetterMinorK
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCDeg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_trueT_iff
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
namespace Formalism.L2.FormalSeriesBounds.RF
namespace SelfConjugatePlaceSetting
theorem _root_.solution {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
    {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
    {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
    {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
    {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
    {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N}
    (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2) :
    (X o).rkF g s = r (tau o (trueT g s)) := by
  unfold RowData.rkF
  have e : (Finset.univ.filter fun c : IIs r tau o => ((X o).G g).ty (Sum.inl c) = s) =
      Finset.univ.map (Function.Embedding.sigmaMk (β := fun t => Fin (r (tau o t))) (trueT g s)) := by
    ext ⟨t', c⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.sigmaMk_apply, H.hty]
    rw [trueT_iff]
    constructor
    · rintro rfl
      exact ⟨c, rfl⟩
    · rintro ⟨c', h⟩
      exact (congrArg Sigma.fst h).symm
  rw [e, Finset.card_map, Finset.card_univ, Fintype.card_fin]
end SelfConjugatePlaceSetting
end Formalism.L2.FormalSeriesBounds.RF
