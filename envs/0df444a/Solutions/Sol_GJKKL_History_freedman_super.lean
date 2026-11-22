-- Prove2me | solution 1 for GJKKL.History.freedman_super
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:24.744817+00:00
-- url     : https://prove2.me/submissions/da6ae49b-1bd3-4a4c-9e49-bf0378252826

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_History_Freedman
public import Theorems.Thm_GJKKL_History_exp_step_le_super
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_stopped_of_alive
public import Theorems.Thm_GJKKL_History_stopped_cons_of_not_alive
public import Theorems.Thm_GJKKL_History_accInc_add_of_alive
public import Theorems.Thm_GJKKL_History_accInc_cons_of_not_alive
public import Theorems.Thm_GJKKL_History_expect_le_of_super
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_mul_prob_le_expect
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil


attribute [local simp] GJKKL.History.aliveBefore_nil
attribute [local simp] GJKKL.History.aliveBefore_cons

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α) (X : List α → ℝ) (G : List α → Prop)
namespace GJKKL.History
theorem _root_.solution (T : ℕ) (C s lam : ℝ) (hC : 0 < C) (hs : 0 < s) (hlam : 0 < lam)
    (htrend : ∀ h : List α, h.length < T → AliveBefore G h → G h →
      ∑ a, κ.K h a * (X (a :: h) - X h) ≤ 0)
    (hinc : ∀ h : List α, h.length < T → AliveBefore G h → G h →
      ∀ a, κ.K h a ≠ 0 → |X (a :: h) - X h| ≤ C)
    (hacc : ∀ h : List α, h.length < T → AliveBefore G h → G h → accSum κ X h ≤ s) :
    prob κ T (fun h => lam ≤ X h - X [] ∧ AliveBefore G h) ≤
      Real.exp (-(lam ^ 2 / (2 * C * (lam + s)))) := by
  classical
  set θ := lam / (C * (lam + s)) with hθdef
  have hθ0 : 0 < θ := by positivity
  have hθC : θ * C = lam / (lam + s) := by rw [hθdef]; field_simp
  have hθC1 : θ * C < 1 := by rw [hθC, div_lt_one (by positivity)]; linarith
  set ψ := θ ^ 2 * C / (2 * (1 - θ * C)) with hψdef
  have hψ0 : 0 ≤ ψ := div_nonneg (by positivity) (by linarith)
  set Z : List α → ℝ := fun h =>
    Real.exp (θ * (stopped X G h - X []) - ψ * accInc κ X G h) with hZ
  -- supermartingale step
  have hsuper : ∀ h : List α, h.length < T → ∑ a, κ.K h a * Z (a :: h) ≤ Z h := by
    intro h hT
    by_cases hal : AliveBefore G h ∧ G h
    · have hcons : ∀ a, AliveBefore G (a :: h) := fun a => hal
      have hZa : ∀ a, Z (a :: h) = Z h *
          Real.exp (θ * (X (a :: h) - X h) - ψ * condAbsInc κ X h) := by
        intro a
        simp only [hZ]
        rw [← Real.exp_add, stopped_of_alive X G (hcons a), stopped_of_alive X G hal.1]
        have hA : accInc κ X G (a :: h) = accInc κ X G h + condAbsInc κ X h := by
          simp only [accInc, if_pos (hcons a)]
        rw [hA]
        congr 1; ring
      simp_rw [hZa]
      have hstep := exp_step_le_super (κ.K h) (κ.nonneg h) (κ.mass_le h)
        (fun a => X (a :: h) - X h) (htrend h hT hal.1 hal.2) C θ hθ0.le hθC1
        (fun a ha => hinc h hT hal.1 hal.2 a ha)
      calc ∑ a, κ.K h a * (Z h * Real.exp (θ * (X (a :: h) - X h) - ψ * condAbsInc κ X h))
          = Z h * Real.exp (-(ψ * condAbsInc κ X h)) *
              ∑ a, κ.K h a * Real.exp (θ * (X (a :: h) - X h)) := by
            rw [mul_sum]; refine sum_congr rfl fun a _ => ?_
            rw [sub_eq_add_neg, Real.exp_add]; ring
        _ ≤ Z h * Real.exp (-(ψ * condAbsInc κ X h)) *
              Real.exp (ψ * condAbsInc κ X h) := by
            apply mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = Z h := by rw [mul_assoc, ← Real.exp_add]; simp
    · have hZa : ∀ a, Z (a :: h) = Z h := by
        intro a
        have hn : ¬ AliveBefore G (a :: h) := hal
        simp only [hZ, stopped_cons_of_not_alive X G hn, accInc_cons_of_not_alive κ X G hn]
      simp_rw [hZa]
      rw [← sum_mul]
      exact mul_le_of_le_one_left (Real.exp_pos _).le (κ.mass_le h)
  have hEZ : expect κ T Z ≤ 1 := by
    have := expect_le_of_super κ Z T hsuper
    simpa [hZ, stopped, accInc] using this
  -- Markov
  have hev : ∀ h : List α, h.length = T → (lam ≤ X h - X [] ∧ AliveBefore G h) →
      Real.exp (θ * lam - ψ * s) ≤ Z h := by
    rintro h hh ⟨hl, hal⟩
    have hAn : accInc κ X G h ≤ s := by
      cases h with
      | nil => simp only [accInc]; exact hs.le
      | cons a h0 =>
        have hal0 : AliveBefore G h0 ∧ G h0 := hal
        have hA : accInc κ X G (a :: h0) = accSum κ X h0 := by
          simp only [accInc, if_pos hal]
          exact accInc_add_of_alive κ X G hal0.1 hal0.2
        rw [hA]
        exact hacc h0 (by simp at hh; omega) hal0.1 hal0.2
    simp only [hZ]
    apply Real.exp_le_exp.mpr
    rw [stopped_of_alive X G hal]
    nlinarith [mul_le_mul_of_nonneg_left hl hθ0.le, mul_le_mul_of_nonneg_left hAn hψ0]
  have hprob : Real.exp (θ * lam - ψ * s) *
      prob κ T (fun h => lam ≤ X h - X [] ∧ AliveBefore G h) ≤ 1 :=
    (mul_prob_le_expect κ (fun h _ => (Real.exp_pos _).le) hev).trans hEZ
  have hval : θ * lam - ψ * s = lam ^ 2 / (2 * C * (lam + s)) := by
    rw [hψdef, hθC, hθdef]
    have h1 : 1 - lam / (lam + s) = s / (lam + s) := by field_simp; ring
    rw [h1]
    field_simp
    ring
  rw [hval] at hprob
  rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _), mul_comm]
  exact hprob
end GJKKL.History
