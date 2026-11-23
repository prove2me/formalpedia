-- Prove2me | solution 1 for Formalism.CountingSumsFrames.tail_q_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:57.751661+00:00
-- url     : https://prove2.me/submissions/6beaf608-d595-4dd4-ba71-03ec3b6aa8a8

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_BinomialSeriesBound
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_pos_real
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_succ_eq_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Filter Topology
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (k' be : ℕ) (b' : ℝ) (hk : 1 ≤ k') (_hb : 0 < b') :
    ∀ J : ℕ, (be : ℝ) + J + k' ≤ 2 * b' →
      (dimPol k' be : ℝ) * ((be : ℝ) + J + k') / dimPol k' (be + J)
        ≤ ((be : ℝ) + k') * Real.exp (-((k' : ℝ) - 1) * J / (2 * b')) := by
  have hk1 : (1 : ℝ) ≤ k' := by exact_mod_cast hk
  have pb := dimPol_pos_real k' be
  intro J
  induction J with
  | zero =>
    intro _
    have e : (dimPol k' be : ℝ) * ((be : ℝ) + k') / dimPol k' be = (be : ℝ) + k' := by
      field_simp
    simpa using e.le
  | succ J ih =>
    intro hJ
    push_cast at hJ ⊢
    have ihJ := ih (by linarith)
    have p0 := dimPol_pos_real k' (be + J)
    have hrec : (dimPol k' (be + (J + 1)) : ℝ)
        = dimPol k' (be + J) * ((be : ℝ) + J + 1 + k') / ((be : ℝ) + J + 1) := by
      rw [show be + (J + 1) = be + J + 1 by omega, dimPol_succ_eq_real]; push_cast; ring
    rw [hrec]
    set q := (dimPol k' be : ℝ) * ((be : ℝ) + J + k') / dimPol k' (be + J) with hq
    have hq0 : 0 ≤ q := by positivity
    have hpos : (0 : ℝ) < (be : ℝ) + J + k' := by positivity
    have hid : (dimPol k' be : ℝ) * ((be : ℝ) + (J + 1) + k')
        / (dimPol k' (be + J) * ((be : ℝ) + J + 1 + k') / ((be : ℝ) + J + 1))
        = q * (((be : ℝ) + J + 1) / ((be : ℝ) + J + k')) := by
      rw [hq]; field_simp; ring
    rw [hid]
    set t := ((be : ℝ) + J + 1) / ((be : ℝ) + J + k') with ht
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ Real.exp (-((k' : ℝ) - 1) / (2 * b')) := by
      have h1 : t = 1 - ((k' : ℝ) - 1) / ((be : ℝ) + J + k') := by rw [ht]; field_simp; ring
      have h2 : ((k' : ℝ) - 1) / (2 * b') ≤ ((k' : ℝ) - 1) / ((be : ℝ) + J + k') :=
        div_le_div_of_nonneg_left (by linarith) hpos (by linarith)
      have h3 := Real.add_one_le_exp (-(((k' : ℝ) - 1) / (2 * b')))
      have h4 : -((k' : ℝ) - 1) / (2 * b') = -(((k' : ℝ) - 1) / (2 * b')) := by ring
      rw [h1, h4]; linarith
    calc q * t ≤ (((be : ℝ) + k') * Real.exp (-((k' : ℝ) - 1) * J / (2 * b')))
          * Real.exp (-((k' : ℝ) - 1) / (2 * b')) :=
          mul_le_mul ihJ ht1 ht0 (by positivity)
      _ = ((be : ℝ) + k') * Real.exp (-((k' : ℝ) - 1) * (J + 1) / (2 * b')) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
end Formalism.CountingSumsFrames
