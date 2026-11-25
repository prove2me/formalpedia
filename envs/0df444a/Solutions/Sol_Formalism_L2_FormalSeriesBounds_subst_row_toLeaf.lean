-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.subst_row_toLeaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:31:36.769487+00:00
-- url     : https://prove2.me/submissions/0e178be3-3c5e-4628-b9a3-b216747d1af3

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_kill
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_one_sub_ne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_toW_same
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_toW_other
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_toLeaf_eq_killV

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
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {V : VF C} {d : ℕ} {J : Fin 2 → Type} (G : ∀ g, Cart V d (I g) (J g))
    (g : Fin 2) (a a' : ZMod d) (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (he : ∀ c x, (G g).ty (Sum.inl x) ≠ a → e c x = 0)
    (hv : ∀ b x, (G (1 - g)).ty (Sum.inl x) ≠ a' → v' b x = 0) (F : MvPowerSeries (WV I) C) :
    subst (linS (rowM g e v')) (toLeaf G g a a' F) = subst (linS (rowM g e v')) F := by
  rw [toLeaf_eq_killV]
  refine subst_linS_kill _ _ (fun w hw c => ?_) F
  obtain ⟨g', x⟩ := w
  have hg : g' = g ∨ g' = 1 - g := finset_fin_two_eq_cases g g'
  rcases hg with rfl | rfl
  · have hx : (G g').ty (Sum.inl x) ≠ a := fun h => hw (Or.inl ⟨rfl, h⟩)
    rcases c with c | b
    · show toW g' (e c) _ = 0
      rw [toW_same, he c x hx]
    · show toW (1 - g') (v' b) _ = 0
      rw [toW_other _ _ (one_sub_ne g').symm]
  · have hx : (G (1 - g)).ty (Sum.inl x) ≠ a' := fun h => hw (Or.inr ⟨rfl, h⟩)
    rcases c with c | b
    · show toW g (e c) _ = 0
      rw [toW_other _ _ (one_sub_ne g)]
    · show toW (1 - g) (v' b) _ = 0
      rw [toW_same, hv b x hx]
end Formalism.L2.FormalSeriesBounds
