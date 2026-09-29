-- Prove2me | solution 1 for FormalGroup.evalNSMul_mul_eq_zero_of_eval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a4a923e1-0dea-5042-8e15-7e91e7aa7cc9

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_MvFormalGroup_OfFormalGroupV2
import Theorems.Thm_FormalGroup_exists_ringHom_evalSeries_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_evalNSMul_mul_eq_zero_of_eval_eq_zero

set_option autoImplicit false

open IsLocalRing Polynomial MvPowerSeries MvFormalGroup

namespace TorsionOfRootAsm

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

theorem evalSeries_eq_adicEval (f : PowerSeries T) (x : T) :
    (letI : WithIdeal T := ⟨I⟩; FormalGroup.evalSeries f x) = adicEval (R := T) I (fun _ : Unit => x) f := rfl

theorem val_nsmul_zero_eq_evalNSMul (F : FormalGroup T) (n : ℕ) (P : Points (ofFormalGroup F) T I) :
    (n • P).val 0 = (letI : WithIdeal T := ⟨I⟩; F.evalNSMul n (P.val 0)) := by
  letI : WithIdeal T := ⟨I⟩
  induction n with
  | zero =>
    rw [zero_nsmul, FormalGroup.evalNSMul_zero]
    rfl
  | succ n ih =>
    rw [succ_nsmul, FormalGroup.evalNSMul_succ, Points.val_add, eval_eq_adicEval I]
    show adicEval (R := T) I (Sum.elim (n • P).val P.val) (rename e2 F.toPowerSeries) = _
    have hw : ∀ t, Sum.elim (n • P).val P.val t ∈ I.radical := by
      rintro (j | j)
      · exact (n • P).mem_radical j
      · exact P.mem_radical j
    rw [adicEval_rename I hw e2]
    congr 1
    funext s
    fin_cases s
    · show Sum.elim (n • P).val P.val (e2 0) = (letI : WithIdeal T := ⟨I⟩; F.evalNSMul n (P.val 0))
      rw [e2_zero, Sum.elim_inl, ih]
    · show Sum.elim (n • P).val P.val (e2 1) = P.val 0
      rw [e2_one, Sum.elim_inr]

end TorsionOfRootAsm

theorem solution
    (T : Type*) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (F : FormalGroup T) [F.IsComm] (q : ℕ) [Fact q.Prime]
    (g : T[X]) (hmonic : g.Monic) (hdeg : g.natDegree = q - 1)
    (hdist : ∀ i < q - 1, g.coeff i ∈ maximalIdeal T)
    (v : PowerSeries T) (hv : IsUnit v)
    (hF : F.nthSeries q = PowerSeries.X * (↑g : PowerSeries T) * v)
    (x : T) (hx : x ∈ maximalIdeal T) (hg : g.eval x = 0) (a : ℕ) :
    (letI : WithIdeal T := ⟨maximalIdeal T⟩; F.evalNSMul q (F.evalNSMul a x)) = 0 := by
  letI : WithIdeal T := ⟨maximalIdeal T⟩
  set I : Ideal T := maximalIdeal T with hI

  let P : Points (ofFormalGroup F) T (maximalIdeal T) := ⟨fun _ => x, fun _ => Ideal.le_radical hx⟩
  have hB := TorsionOfRootAsm.val_nsmul_zero_eq_evalNSMul (maximalIdeal T) F

  have hq0 : F.evalNSMul q x = 0 := by
    have h1 : F.evalNSMul q x = (q • P).val 0 := (hB q P).symm
    rw [h1, Points.val_nsmul, nthSeries_ofFormalGroup]
    show adicEval (R := T) (maximalIdeal T) P.val (toMv (F.nthSeries q)) = 0
    rw [toMv_def, TorsionOfRootAsm.adicEval_rename (maximalIdeal T) P.mem_radical e1,
      show (fun s : Unit => P.val (e1 s)) = fun _ : Unit => x from rfl,
      ← TorsionOfRootAsm.evalSeries_eq_adicEval (maximalIdeal T)]
    obtain ⟨e, he, hep⟩ := FormalGroup.exists_ringHom_evalSeries_eq (maximalIdeal T) x hx
    rw [he, hF, map_mul, map_mul, ← Polynomial.coe_X, hep, hep, hg, mul_zero, zero_mul]

  have hqP : q • P = 0 := by
    apply Points.ext
    funext i
    rw [Subsingleton.elim i 0, hB q P, Points.val_zero]
    exact hq0

  have h2 : F.evalNSMul a x = (a • P).val 0 := (hB a P).symm
  rw [h2, ← hB q (a • P), smul_smul, mul_comm, ← smul_smul, hqP, smul_zero, Points.val_zero]

end S_FormalGroup_evalNSMul_mul_eq_zero_of_eval_eq_zero
end P2MW
export P2MW.S_FormalGroup_evalNSMul_mul_eq_zero_of_eval_eq_zero (solution)
