-- Prove2me | solution 1 for CorruptRobustRL.ElimLB.adm_imp_noElim
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:38:53.143989+00:00
-- url     : https://prove2.me/submissions/a1fcf50e-7fe2-4df9-b5e3-59e86ee54cb2

import Mathlib
import Definitions.Def_CorruptRobustRL_ElimLB_MDP
import Definitions.Def_CorruptRobustRL_ElimLB_Setting
import Definitions.Def_CorruptRobustRL_ElimLB_ComboLock

namespace Aux_ElimLB
open CorruptRobustRL.ElimLB

lemma rbar_zero (H A : ℕ) [NeZero A] (x : Fin (H + 1)) (a : Fin A) :
    (comboLock0 H A).rbar x a = 0 := by
  unfold Instance.rbar
  have : ∀ r : ℝ, ((comboLock0 H A).R x a r).toReal * r = 0 := by
    intro r
    change ((PMF.pure (0:ℝ)) r).toReal * r = 0
    rw [PMF.pure_apply]
    by_cases hr : r = 0
    · rw [hr, mul_zero]
    · simp [hr]
  simp only [this, tsum_zero]

lemma vopt_zero (H A : ℕ) [NeZero A] (n : ℕ) (x : Fin (H + 1)) :
    Vopt (comboLock0 H A) n x = 0 := by
  induction n generalizing x with
  | zero => rfl
  | succ k ih =>
    unfold Vopt
    simp only [rbar_zero, ih, mul_zero, Finset.sum_const_zero, add_zero]
    exact Finset.sup'_const _ _

end Aux_ElimLB

open CorruptRobustRL.ElimLB in
theorem solution (H A : ℕ) [NeZero A] (hH : 1 ≤ H) (hA : 2 ≤ A)
    (T : Supervisor (Fin (H + 1)) (Fin A) H) (hT : IsAdmissible (comboLock0 H A) T) :
    NoElim T := by
  have hQ : ∀ h x a, Qstar (comboLock0 H A) H h x a = 0 := by
    intro h x a
    unfold Qstar
    simp [Aux_ElimLB.rbar_zero, Aux_ElimLB.vopt_zero]
  have hV : ∀ h x, VstarAt (comboLock0 H A) H h x = 0 := by
    intro h x
    exact Aux_ElimLB.vopt_zero H A _ x
  intro h hh x
  obtain ⟨hsub, hbounds⟩ := hT h hh x
  refine ⟨?_, fun a => ?_⟩
  · apply Finset.eq_univ_of_forall
    intro a
    apply hsub
    change Qstar (comboLock0 H A) H h x a = VstarAt (comboLock0 H A) H h x
    rw [hQ, hV]
  · apply Finset.sup'_le
    intro a' _
    have h1 := (hbounds a').1
    have h2 := (hbounds a).2
    rw [hQ] at h1 h2
    linarith
