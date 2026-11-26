-- Prove2me | solution 1 for FirstPassageLinearTransport.square_exp_payment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:26:02.974833+00:00
-- url     : https://prove2.me/submissions/349411a2-49b6-4a33-85fd-45ab2b299a6b

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {q x : ℝ} (hq : 0 < q) (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-(q * x)) ≤ 4 / q ^ 2 := by
  let z := q * x / 2
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzexp : z ≤ Real.exp z := by
    have h := Real.add_one_le_exp z
    linarith
  have hsq : z ^ 2 ≤ (Real.exp z) ^ 2 :=
    (sq_le_sq₀ hz (Real.exp_pos z).le).2 hzexp
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
  have hcore : x ^ 2 ≤ (4 / q ^ 2) * Real.exp (q * x) := by
    have hexp : (Real.exp z) ^ 2 = Real.exp (q * x) := by
      rw [pow_two, ← Real.exp_add]
      dsimp [z]
      congr 1
      ring
    rw [hexp] at hsq
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hq2).2
    dsimp [z] at hsq
    nlinarith
  have hexpPos : 0 < Real.exp (q * x) := Real.exp_pos _
  calc
    x ^ 2 * Real.exp (-(q * x)) = x ^ 2 / Real.exp (q * x) := by
      rw [Real.exp_neg]
      ring
    _ ≤ 4 / q ^ 2 := (div_le_iff₀ hexpPos).2 (by
      nlinarith [hcore])
end FirstPassageLinearTransport
