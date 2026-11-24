-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.constsOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:33.5108+00:00
-- url     : https://prove2.me/submissions/8453746a-fece-4c23-9e44-42fbc7e08ada

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffConsts
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_constsOf_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution (A : ℕ) (c c₀ C : ℝ) (hc : 0 < c) (hc₀ : 0 < c₀) (hC : 0 ≤ C) : ∃ K : ℝ, 4 ≤ K ∧
    ∀ (m : ℕ) (x : ℝ), 1 ≤ m → 0 < x → K * Real.log (3 * m) ^ 2 ≤ Real.log x →
      4 ≤ Real.log x ∧ (m : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x)) ∧
      3 * (Real.sqrt x * Real.log x) ≤
        c₀ * x / (m : ℝ) ^ (A + 1) - C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  have hn : 1 ≤ A + 1 := Nat.le_add_left 1 A
  set a : ℝ := ((A + 1 : ℕ) : ℝ) with ha
  have ha1 : 1 ≤ a := by rw [ha]; exact_mod_cast hn
  set R : ℝ := 4 * a + 4 * (24 / c₀) + (a + 2 * C / c₀) / c with hR
  have h1 : 0 ≤ 4 * (24 / c₀) := by positivity
  have h2 : 0 ≤ (a + 2 * C / c₀) / c := by positivity
  have hA1 : 4 * a + 4 * (24 / c₀) ≤ R := by linarith
  have hA2 : a + 2 * C / c₀ ≤ c * R := by
    have h3 : c * ((a + 2 * C / c₀) / c) = a + 2 * C / c₀ := by field_simp
    have h4 : 0 ≤ c * (4 * a + 4 * (24 / c₀)) := by positivity
    have h5 : c * R = c * (4 * a + 4 * (24 / c₀)) + c * ((a + 2 * C / c₀) / c) := by rw [hR]; ring
    linarith
  refine ⟨R ^ 2, by nlinarith, ?_⟩
  intro m x hm hx hK
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have h3m : (0 : ℝ) < 3 * m := by linarith
  have hl : 1 ≤ Real.log (3 * m) := by
    rw [Real.le_log_iff_exp_le h3m]
    have := Real.exp_one_lt_d9
    linarith
  have hMl : (m : ℝ) ≤ Real.exp (Real.log (3 * m)) := by
    rw [Real.exp_log h3m]; linarith
  have key := constsOf_core (A + 1) c c₀ C R (Real.log (3 * m)) (Real.log x) m hn hc hc₀ hC hA1 hA2
    hl hK hm0 hMl
  have hsq : Real.exp (Real.log x / 2) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 1; ring
  rw [hsq, Real.exp_log hx] at key
  exact key
end Formalism.HermitianLattices.Ext.SupplyAP
