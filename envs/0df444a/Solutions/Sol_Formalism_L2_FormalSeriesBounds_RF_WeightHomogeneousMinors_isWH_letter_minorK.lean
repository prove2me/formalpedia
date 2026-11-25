-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.isWH_letter_minorK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:34:17.612929+00:00
-- url     : https://prove2.me/submissions/2ce8c332-10fe-4424-9960-e3c1319ef32e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_isWH_rename
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_isWH_minorK_row
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_wRow_letter
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
open Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ}
  {Orb : Type} {tau : Orb → Fin 2 → ZMod d → T} {o0 : Orb} {J0 : Fin 2 → Type} [∀ g, Fintype (J0 g)]
variable (X : RowData C V d (IIof r tau o0) J0) (F : Flag X)
  (hty : ∀ g (x : IIof r tau o0 g), (X.G g).ty (Sum.inl x) = x.1)
  (std : ∀ g t (c : Fin (X.rkF g t)), ((F.en g t c).2 : ℕ) = c.val)
include hty std
namespace Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
theorem _root_.solution {N k : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d) :
    IsWeightedHomogeneous (wRow r tau o0 (N := N) g0 t0 c0) (rename (F.letter g t) (minorK C N (X.rkF g t) k))
      (if k ≤ N ∧ k ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < k then 1 else 0) := by
  apply isWH_rename
  exact isWH_minorK_row (R := C) (g = g0 ∧ t = t0) c0 (fun x => wRow_letter X F hty std g0 t0 c0 g t x)
end Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
