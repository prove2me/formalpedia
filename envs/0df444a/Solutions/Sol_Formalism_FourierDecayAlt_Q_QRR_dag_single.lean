-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.dag_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:11:55.297782+00:00
-- url     : https://prove2.me/submissions/59b025b7-211f-40f5-a911-72f21e011164

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_EllSingleZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
private lemma tau_val_lemma (i : Fin (2 * r + k + 1)) :
    (WeylGroupFacts.tau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl
private lemma tau_tau_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.tau k r (WeylGroupFacts.tau k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [tau_val_lemma]
  split_ifs <;> omega
private lemma sgn_tau_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r (WeylGroupFacts.tau k r i) = WeylGroupFacts.sgn k r i := by
  have hi := i.isLt
  unfold WeylGroupFacts.sgn
  simp only [tau_val_lemma]
  split_ifs <;> first | rfl | omega
private lemma hpk_eq_lemma (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = WeylGroupFacts.tau k r i then WeylGroupFacts.sgn k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk WeylGroupFacts.sgn
  simp only [Fin.ext_iff, tau_val_lemma]
  split_ifs <;> first | rfl | omega | norm_num
private lemma sgn_sq_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r i * WeylGroupFacts.sgn k r i = 1 := by
  unfold WeylGroupFacts.sgn
  split_ifs <;> norm_num
private lemma hpk_sq_lemma : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [hpk_eq_lemma, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, tau_tau_lemma, sgn_tau_lemma]
  by_cases h : i = j
  · subst h
    simp [sgn_sq_lemma]
  · simp [h, Ne.symm h]
private lemma hpk_inv_lemma : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hpk_sq_lemma
private lemma single_ct_lemma (a b : Fin (2 * r + k + 1)) (c : ℂ) :
    (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
  ext x y
  rw [Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.single_apply]
  by_cases h : a = y ∧ b = x
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), star_zero]
private lemma conj_single_lemma (A B : Mx k r) (a b : Fin (2 * r + k + 1)) (c : ℂ)
    (p q : Fin (2 * r + k + 1)) : (A * Matrix.single a b c * B) p q = A p a * c * B b q := by
  simp only [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
end Formalism.FourierDecayAlt.Q.QRR
end
end

set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.QRR
theorem _root_.solution (a b : Fin (2 * r + k + 1)) (c : ℂ) :
    dag k r (Matrix.single a b c) = Matrix.single (WeylGroupFacts.tau k r b) (WeylGroupFacts.tau k r a)
      (WeylGroupFacts.sgn k r (WeylGroupFacts.tau k r b) * star c * WeylGroupFacts.sgn k r (WeylGroupFacts.tau k r a)) := by
  unfold dag
  rw [hpk_inv_lemma, single_ct_lemma]
  ext p q
  rw [conj_single_lemma, hpk_eq_lemma, hpk_eq_lemma, Matrix.single_apply]
  by_cases hp : p = WeylGroupFacts.tau k r b
  · subst hp
    by_cases hq : q = WeylGroupFacts.tau k r a
    · subst hq
      simp [tau_tau_lemma, sgn_tau_lemma]
    · simp [hq, Ne.symm hq]
  · have hb : b ≠ WeylGroupFacts.tau k r p := fun h => hp (by rw [h, tau_tau_lemma])
    simp [hb, Ne.symm hp]
end Formalism.FourierDecayAlt.Q.QRR
