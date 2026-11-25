-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.toLeaf_eq_killV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:07.303272+00:00
-- url     : https://prove2.me/submissions/8bd25d68-55b5-4633-b3d4-558e6b3e68c3

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_killV

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
    (g : Fin 2) (a a' : ZMod d) (F : MvPowerSeries (WV I) C) :
    toLeaf G g a a' F = killV (OnLeafV G g a a') F := by
  ext μ
  have h1 : coeff μ (toLeaf G g a a' F) = toLeaf G g a a' F μ := rfl
  rw [h1, coeff_killV]
  unfold toLeaf
  by_cases h : ∀ w ∈ μ.support, OnLeafV G g a a' w
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
end Formalism.L2.FormalSeriesBounds
