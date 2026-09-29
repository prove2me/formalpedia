-- Prove2me | solution 1 for FormalGroup.linCombAdic_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/242579db-7b91-51f5-a836-436cbe561f79

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis

import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_MvFormalGroup_OfFormalGroupV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_linCombAdic_zero_right

set_option autoImplicit false

open MvPowerSeries MvFormalGroup

namespace LinCombZeroRightAsm

variable {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T]

theorem adicEval_rename {σ τ : Type*} [Finite σ] [Finite τ] {w : τ → T} (hw : ∀ t, w t ∈ I.radical)
    (e : σ ↪ τ) (f : MvPowerSeries σ T) :
    adicEval (R := T) I w (rename e f) = adicEval (R := T) I (fun s => w (e s)) f := by
  rw [rename_eq_subst, adicEval_subst (R := T) I hw (HasSubst.X_comp e)]
  congr 1
  funext s
  exact adicEval_X (R := T) I w (e s)

theorem eval_eq_adicEval (F : FormalGroup T) (a b : T) :
    (letI : WithIdeal T := ⟨I⟩; F.eval a b) = adicEval (R := T) I ![a, b] F.toPowerSeries := rfl

theorem val_add_zero_eq_eval (F : FormalGroup T) (Q Q' : Points (ofFormalGroup F) T I) :
    (Q + Q').val 0 = (letI : WithIdeal T := ⟨I⟩; F.eval (Q.val 0) (Q'.val 0)) := by
  letI : WithIdeal T := ⟨I⟩
  rw [Points.val_add, eval_eq_adicEval I]
  show adicEval (R := T) I (Sum.elim Q.val Q'.val) (rename e2 F.toPowerSeries) = _
  have hw : ∀ t, Sum.elim Q.val Q'.val t ∈ I.radical := by
    rintro (j | j)
    · exact Q.mem_radical j
    · exact Q'.mem_radical j
  rw [adicEval_rename I hw e2]
  congr 1
  funext s
  fin_cases s
  · show Sum.elim Q.val Q'.val (e2 0) = Q.val 0
    rw [e2_zero, Sum.elim_inl]
  · show Sum.elim Q.val Q'.val (e2 1) = Q'.val 0
    rw [e2_one, Sum.elim_inr]

theorem val_nsmul_zero_eq_evalNSMul (F : FormalGroup T) (n : ℕ) (P : Points (ofFormalGroup F) T I) :
    (n • P).val 0 = (letI : WithIdeal T := ⟨I⟩; F.evalNSMul n (P.val 0)) := by
  letI : WithIdeal T := ⟨I⟩
  induction n with
  | zero =>
    rw [zero_nsmul, FormalGroup.evalNSMul_zero]
    rfl
  | succ n ih =>
    rw [succ_nsmul, FormalGroup.evalNSMul_succ, val_add_zero_eq_eval I, ih]

end LinCombZeroRightAsm

theorem solution
    {T : Type} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F : FormalGroup T)
    (x y : T) (hx : x ∈ I) (a : ℕ) :
    F.linCombAdic I x y a 0 = (letI : WithIdeal T := ⟨I⟩; F.evalNSMul a x) := by
  letI : WithIdeal T := ⟨I⟩
  let P : Points (ofFormalGroup F) T I := ⟨fun _ => x, fun _ => Ideal.le_radical hx⟩
  have hB := LinCombZeroRightAsm.val_nsmul_zero_eq_evalNSMul I F a P

  show F.eval (F.evalNSMul a x) (F.evalNSMul 0 y) = F.evalNSMul a x
  rw [FormalGroup.evalNSMul_zero, ← hB]
  have h := LinCombZeroRightAsm.val_add_zero_eq_eval I F (a • P) 0
  rw [add_zero, Points.val_zero] at h
  exact h.symm

end S_FormalGroup_linCombAdic_zero_right
end P2MW
export P2MW.S_FormalGroup_linCombAdic_zero_right (solution)
