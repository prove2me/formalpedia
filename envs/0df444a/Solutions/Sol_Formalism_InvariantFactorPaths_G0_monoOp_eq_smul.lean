-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G0.monoOp_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:44:36.745855+00:00
-- url     : https://prove2.me/submissions/5af46d2a-8a0f-4381-9c77-53e6b3a07123

import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ElementarySymmetricExpBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_LePowOddOfFloorLogbLe
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_ElementarySymmetricExpBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Pointwise
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G0
open Formalism.G0
namespace Formalism.InvariantFactorPaths.G0
theorem _root_.solution {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {V : ℕ} (π : R)
    (y : Fin V → Module.End R X) (m : ℕ) (Sv : Fin V → ℕ) (E : Fin V → Bool) :
    monoOp π y m Sv E =
      π ^ (∑ v, if E v = true then 0 else Sv v) • monoOp π y m (fun _ => 0) E := by
  have hl : ∀ (c : Fin V → R) (f : Fin V → Module.End R X) (l : List (Fin V)),
      (l.map fun v => c v • f v).prod = (l.map c).prod • (l.map f).prod := by
    intro c f l
    induction l with
    | nil => simp
    | cons a l ih => rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons,
        List.map_cons, List.prod_cons, smul_mul_smul_comm]
  have hf : (fun v => if E v = true then y v ^ m else (π ^ Sv v) • (1 : Module.End R X)) =
      fun v => π ^ (if E v = true then 0 else Sv v) •
        (if E v = true then y v ^ m else (π ^ (fun _ => 0) v) • (1 : Module.End R X)) := by
    funext v
    by_cases h : E v = true <;> simp [h]
  unfold monoOp
  rw [hf, hl, ← Fin.prod_univ_def, Finset.prod_pow_eq_pow_sum]
end Formalism.InvariantFactorPaths.G0
