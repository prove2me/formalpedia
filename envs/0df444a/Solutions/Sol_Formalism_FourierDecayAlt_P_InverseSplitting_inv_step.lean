-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseSplitting.inv_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:19:44.467643+00:00
-- url     : https://prove2.me/submissions/46938066-1bbe-4ff6-be0d-9942ba055b81

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InverseSplitting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.InverseSplitting
open C2x2
variable {m : ℕ}
namespace Formalism.FourierDecayAlt.P.InverseSplitting
theorem _root_.solution (w : Equiv.Perm (Fin m)) (l : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ C2.LTset m) :
    ∀ n, Inv w l n (lsStep w l n).1 (lsStep w l n).2 := by
  intro n
  induction n with
  | zero =>
    show Inv w l 0 1 1
    refine ⟨fun i j h => ?_, fun i => by simp, fun i j h => ?_, fun i j h _ => ?_,
      fun i j h _ => ?_, fun i j h => ?_⟩
    · have hne : i ≠ j := ne_of_lt h
      simp [Matrix.one_apply_ne hne]
    · have hne : i ≠ j := fun e => by subst e; omega
      simp [Matrix.one_apply_ne hne]
    · simp [Matrix.one_apply_ne (ne_of_lt h).symm]
    · simp [Matrix.one_apply_ne (ne_of_lt h).symm]
    · rw [Matrix.one_mul]
      by_cases hij : i = j
      · subst hij
        simp [hl.2 i]
      · have hlt : i < j := by
          have hv : i.val ≠ j.val := fun e => hij (Fin.ext e)
          rw [Fin.lt_iff_val_lt_val]
          omega
        rw [Matrix.one_apply_ne hij, hl.1 i j hlt]
  | succ n ih =>
    obtain ⟨hup, hdiag, hfar, hsupA, hsupB, hprod⟩ := ih
    set A := (lsStep w l n).1 with hAdef
    set B := (lsStep w l n).2 with hBdef
    have hA' : ∀ i j, (lsStep w l (n + 1)).1 i j = if i.val = j.val + n + 1 then
        (if w.symm j < w.symm i then l i j - (A * B) i j else 0) else A i j := fun i j => rfl
    have hB' : ∀ i j, (lsStep w l (n + 1)).2 i j = if i.val = j.val + n + 1 then
        (if w.symm j < w.symm i then 0 else l i j - (A * B) i j) else B i j := fun i j => rfl
    refine ⟨fun i j h => ?_, fun i => ?_, fun i j h => ?_, fun i j h hw => ?_,
      fun i j h hw => ?_, fun i j h => ?_⟩
    · have hv : ¬ i.val = j.val + n + 1 := by
        rw [Fin.lt_iff_val_lt_val] at h
        omega
      rw [hA', hB', if_neg hv, if_neg hv]
      exact hup i j h
    · have hv : ¬ i.val = i.val + n + 1 := by omega
      rw [hA', hB', if_neg hv, if_neg hv]
      exact hdiag i
    · have hv : ¬ i.val = j.val + n + 1 := by omega
      rw [hA', hB', if_neg hv, if_neg hv]
      exact hfar i j (by omega)
    · rw [hA']
      split_ifs with hv
      · rfl
      · exact hsupA i j h hw
    · rw [hB']
      split_ifs with hv
      · rfl
      · exact hsupB i j h hw
    · rw [Matrix.mul_apply]
      by_cases hgap : i.val = j.val + n + 1
      ·
        have hji : j ≠ i := fun e => by subst e; omega
        have hAij : A i j = 0 := (hfar i j (by omega)).1
        have hBij : B i j = 0 := (hfar i j (by omega)).2
        have hterm : ∀ k, (lsStep w l (n + 1)).1 i k * (lsStep w l (n + 1)).2 k j =
            A i k * B k j + (if k = j then (lsStep w l (n + 1)).1 i j else 0) +
              (if k = i then (lsStep w l (n + 1)).2 i j else 0) := by
          intro k
          by_cases hkj : k = j
          · subst hkj
            have hv : ¬ k.val = k.val + n + 1 := by omega
            rw [hB' k k, if_neg hv, (hdiag k).2, hAij, if_pos rfl, if_neg hji]
            simp
          by_cases hki : k = i
          · subst hki
            have hv : ¬ k.val = k.val + n + 1 := by omega
            rw [hA' k k, if_neg hv, (hdiag k).1, hBij, if_neg hkj, if_pos rfl]
            simp
          have hv1 : ¬ i.val = k.val + n + 1 := fun e => hkj (Fin.ext (by omega))
          have hv2 : ¬ k.val = j.val + n + 1 := fun e => hki (Fin.ext (by omega))
          rw [hA' i k, hB' k j, if_neg hv1, if_neg hv2, if_neg hkj, if_neg hki]
          simp
        rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq' Finset.univ j, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _),
          if_pos (Finset.mem_univ _), ← Matrix.mul_apply, hA', hB', if_pos hgap, if_pos hgap]
        split_ifs <;> ring
      ·
        have hle : i.val ≤ j.val + n := by omega
        rw [← hprod i j hle, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk1 : i.val = k.val + n + 1
        · have hkj : k < j := by
            rw [Fin.lt_iff_val_lt_val]
            omega
          have hv2 : ¬ k.val = j.val + n + 1 := by omega
          rw [hB' k j, if_neg hv2, (hup k j hkj).2]
          simp
        · rw [hA' i k, if_neg hk1]
          by_cases hk2 : k.val = j.val + n + 1
          · have hik : i < k := by
              rw [Fin.lt_iff_val_lt_val]
              omega
            rw [(hup i k hik).1]
            simp
          · rw [hB' k j, if_neg hk2]
end Formalism.FourierDecayAlt.P.InverseSplitting
