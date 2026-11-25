-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.shift_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:11:23.036971+00:00
-- url     : https://prove2.me/submissions/12a14481-3e4c-401c-a77a-14b57ec404f7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_rowShift_C
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_rowShift_X


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
variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]
variable {N N' : ℕ} (Φ : MvPolynomial (Fin N × Fin N') C →ₐ[C] MvPolynomial (Letter T r n) C) (σ0 : T)
  (w : Fin N → Fin 2 → C) (lt : Fin N × Fin N' → Fin 2 → Letter T r n) (colf : Fin N → Fin 2 → Fin n)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (σ : T) (i i' : Fin (r σ)) (t : C)
    (ρ : Fin N) (c : Fin N') (h : ¬ (σ = σ0 ∧ c.val = i.val)) :
    rowShift r n C σ i i' t (Φ (X (ρ, c))) = Φ (X (ρ, c)) := by
  rw [hΦ, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, rowShift_C, rowShift_X, hlt, if_neg]
  intro e
  apply h
  exact ⟨(congrArg (fun x : T × ℕ × Fin n => x.1) e).symm, congrArg (fun x : T × ℕ × Fin n => x.2.1) e⟩
end Formalism.L2.FormalSeriesBounds.RF
