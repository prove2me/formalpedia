-- Prove2me | solution 1 for Formalism.QuantumDeterminants.GBasic.PJP_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:34:04.274492+00:00
-- url     : https://prove2.me/submissions/388a6ff1-b8df-4902-b48e-de5b2a1b6f38

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_sig
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_lo
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_hi
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_mid
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_eq_sig_iff
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_inj
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Pk_star

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.GBasic
namespace Formalism.QuantumDeterminants.GBasic
theorem _root_.solution (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ((Pk k r)ᴴ * Formalism.REAL.Jm (epsK k r) * Pk k r) i j = Hpk k r i j := by
  have hi := i.isLt
  have hj := j.isLt
  rw [Hpk_eq, Matrix.mul_apply]
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Pk_star]
  simp only [Pk, add_mul, mul_add, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hs : j = sig k r i
  · subst hs
    rcases lt_or_ge i.val r with h | h
    · have hsv := sig_lo k r i h
      have hne : ¬ sig k r i = i := fun e => by have := congrArg Fin.val e; omega
      have hne' : ¬ i = sig k r i := fun e => hne e.symm
      have f1 : ¬ (2 * r + k - i.val < r) := by omega
      have f2 : r + k < 2 * r + k - i.val := by omega
      have f3 : ¬ (i.val = r + k) := by omega
      have f4 : i.val < r + k := by omega
      have f5 : ¬ (2 * r + k - i.val < r + k) := by omega
      simp [c1, c2, epsK, sgn, sig_sig, hsv, hne, hne', h, f1, f2, f3, f4, f5]
      all_goals norm_num
    rcases le_or_gt i.val (r + k) with h' | h'
    · have hm := sig_mid k r i h h'
      simp only [sig_sig, hm]
      have f1 : ¬ (i.val < r) := by omega
      have f2 : ¬ (r + k < i.val) := by omega
      by_cases h3 : i.val = r + k
      · simp [c1, c2, epsK, sgn, f1, f2, h3]
      · have f4 : i.val < r + k := by omega
        simp [c1, c2, epsK, sgn, f1, f2, h3, f4]
    · have hsv := sig_hi k r i h'
      have hne : ¬ sig k r i = i := fun e => by have := congrArg Fin.val e; omega
      have hne' : ¬ i = sig k r i := fun e => hne e.symm
      have f1 : 2 * r + k - i.val < r := by omega
      have f2 : ¬ (i.val < r) := by omega
      have f3 : ¬ (i.val = r + k) := by omega
      have f4 : ¬ (i.val < r + k) := by omega
      have f5 : 2 * r + k - i.val < r + k := by omega
      simp [c1, c2, epsK, sgn, sig_sig, hsv, hne, hne', h', f1, f2, f3, f4, f5]
      all_goals norm_num
  · have hs' : ¬ i = sig k r j := fun e => hs ((eq_sig_iff k r i j).1 e)
    by_cases hij : j = i
    · subst hij
      rcases lt_or_ge j.val r with h | h
      · have hsv := sig_lo k r j h
        have f1 : ¬ (2 * r + k - j.val < r) := by omega
        have f2 : r + k < 2 * r + k - j.val := by omega
        have f4 : j.val < r + k := by omega
        have f5 : ¬ (2 * r + k - j.val < r + k) := by omega
        have hne : ¬ sig k r j = j := fun e => hs e.symm
        simp [c1, c2, epsK, sgn, hs, hne, hsv, h, f1, f2, f4, f5]
        all_goals norm_num
      rcases le_or_gt j.val (r + k) with h' | h'
      · exact absurd (sig_mid k r j h h').symm hs
      · have hsv := sig_hi k r j h'
        have f1 : 2 * r + k - j.val < r := by omega
        have f2 : ¬ (j.val < r) := by omega
        have f4 : ¬ (j.val < r + k) := by omega
        have f5 : 2 * r + k - j.val < r + k := by omega
        have hne : ¬ sig k r j = j := fun e => hs e.symm
        simp [c1, c2, epsK, sgn, hs, hne, hsv, h', f1, f2, f4, f5]
        all_goals norm_num
    · have hij' : ¬ i = j := fun e => hij e.symm
      have hss : ¬ sig k r i = sig k r j := fun e => hij' ((sig_inj k r i j).1 e)
      have hs'' : ¬ sig k r j = i := fun e => hs' e.symm
      have hs3 : ¬ sig k r i = j := fun e => hs e.symm
      have hss' : ¬ sig k r j = sig k r i := fun e => hss e.symm
      simp [hs, hs', hs'', hs3, hij, hij', hss, hss']
end Formalism.QuantumDeterminants.GBasic
