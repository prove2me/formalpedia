-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.SelfConjugatePlaceSetting.inv_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:40:10.770202+00:00
-- url     : https://prove2.me/submissions/c95282e1-45dc-4202-b4c6-1aa75cd9412a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_rowShift_minor_lin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_SelfConjugatePlaceSetting_en_fst
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
theorem _root_.solution (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2) {M : ℕ}
    (col : Fin M → Fin N) (k : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k))) =
      PsiS r tau gm plc o col (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k)) := by
  refine rowShift_minor_lin ((PsiS r tau gm plc o col).comp (rename ((F o).letter g s))) (tau o (trueT g s))
    (fun _ q => gm o (trueT g s) q g)
    (fun x q => ⟨tau o ((F o).en g s x.2).1, ((F o).en g s x.2).2, plc (col x.1, q)⟩) (fun ρ q => plc (col ρ, q)) ?_ ?_
    σ i i' hi t k
  · intro x
    rw [AlgHom.comp_apply, rename_X]
    unfold PsiS
    rw [AlgHom.comp_apply, rename_X]
    unfold subG
    rw [aeval_X]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e2 : gm o ((F o).en g s x.2).1 q g = gm o (trueT g s) q g := by rw [H.en_fst]
    exact congrArg (fun z : C => MvPolynomial.C z * MvPolynomial.X
      (⟨tau o ((F o).en g s x.2).1, ((F o).en g s x.2).2, plc (col x.1, q)⟩ : Letter T r n)) e2
  · intro ρ c q
    show (tau o ((F o).en g s c).1, ((F o).en g s c).2.val, plc (col ρ, q)) = _
    simp only [Prod.mk.injEq]
    exact ⟨congrArg (tau o) (H.en_fst o g s c), H.std o g s c, trivial⟩
end SelfConjugatePlaceSetting
end Formalism.L2.FormalSeriesBounds.RF
