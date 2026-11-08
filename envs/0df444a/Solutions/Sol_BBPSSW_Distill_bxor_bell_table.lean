-- Prove2me | solution 1 for BBPSSW.Distill.bxor_bell_table
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:25:05.896098+00:00
-- url     : https://prove2.me/submissions/cbc26377-9615-4fd0-839a-e85412d0899a

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_BBPSSW_Distill_bellVec
import Definitions.Def_BBPSSW_Distill_bxor
import Definitions.Def_BBPSSW_Distill_bxorTable

open QAlgorithms.Papers.Independent.Information100.P21 (QQ)
open Matrix

namespace BBPSSW.Distill.Aux_BB

open BBPSSW.Distill

def flipb (b : Fin 2) : Fin 2 := if b = 0 then 1 else 0

def sig (P : QQ × QQ) : QQ × QQ :=
  ((P.1.1, P.1.2), (if P.1.1 = 0 then flipb P.2.1 else P.2.1,
    if P.1.2 = 0 then flipb P.2.2 else P.2.2))

theorem uxor_apply (a b c d : Fin 2) :
    uxor (a, b) (c, d) = if c = a ∧ d = (if a = 0 then flipb b else b) then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [uxor, Matrix.single_apply, flipb]

theorem bxor_mulVec (x : QQ × QQ → ℂ) (P : QQ × QQ) : (bxor *ᵥ x) P = x (sig P) := by
  simp only [Matrix.mulVec, dotProduct, bxor, Matrix.of_apply]
  rw [Finset.sum_eq_single (sig P)]
  · rw [uxor_apply, uxor_apply]
    simp [sig]
  · intro Q _ hQ
    rw [uxor_apply, uxor_apply]
    by_cases h1 : (Q.1.1 = P.1.1 ∧ Q.2.1 = (if P.1.1 = 0 then flipb P.2.1 else P.2.1))
    · by_cases h2 : (Q.1.2 = P.1.2 ∧ Q.2.2 = (if P.1.2 = 0 then flipb P.2.2 else P.2.2))
      · exfalso
        apply hQ
        obtain ⟨⟨q11, q12⟩, ⟨q21, q22⟩⟩ := Q
        simp only [sig, Prod.mk.injEq] at h1 h2 ⊢
        exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩
      · rw [if_neg h2, mul_zero, zero_mul]
    · rw [if_neg h1, zero_mul, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end BBPSSW.Distill.Aux_BB

open BBPSSW.Distill BBPSSW.Distill.Aux_BB in
theorem solution (s t : BellLabel) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      QAlgorithms.act bxor (QAlgorithms.tensorVec (bellVec s) (bellVec t)) =
        c • QAlgorithms.tensorVec (bellVec (bxorTable s t).1) (bellVec (bxorTable s t).2) := by
  have key : ∀ c : ℂ, (∀ P : QQ × QQ, (bellVec s) (sig P).1 * (bellVec t) (sig P).2 =
      c * ((bellVec (bxorTable s t).1) P.1 * (bellVec (bxorTable s t).2) P.2)) →
      QAlgorithms.act bxor (QAlgorithms.tensorVec (bellVec s) (bellVec t)) =
        c • QAlgorithms.tensorVec (bellVec (bxorTable s t).1) (bellVec (bxorTable s t).2) := by
    intro c hc
    unfold QAlgorithms.act QAlgorithms.tensorVec
    ext P
    simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_toLp]
    rw [bxor_mulVec]
    exact hc P
  refine ⟨if t = BellLabel.phiPlus ∨ t = BellLabel.psiPlus then 1 else -1, ?_, key _ ?_⟩
  · split_ifs <;> simp
  · rintro ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩
    cases s <;> cases t <;> fin_cases a1 <;> fin_cases b1 <;> fin_cases a2 <;> fin_cases b2 <;>
      simp [sig, flipb, bellVec, bxorTable] <;> ring
