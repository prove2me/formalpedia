-- Prove2me | solution 1 for BBPSSW.Distill.recurrenceMap_iterate
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:50:11.836598+00:00
-- url     : https://prove2.me/submissions/301a52a1-f710-4b0b-bbbc-0ef975384766

import Mathlib
import Definitions.Def_BBPSSW_Distill_recurrenceMap

open Filter Topology

open BBPSSW.Distill in
theorem solution :
    Continuous recurrenceMap ∧
      (∀ F : ℝ, 1 / 2 < F → F < 1 → F < recurrenceMap F) ∧
      ∀ F₀ : ℝ, 1 / 2 < F₀ → F₀ ≤ 1 →
        Tendsto (fun k : ℕ => recurrenceMap^[k] F₀) atTop (𝓝 1) := by
  have hD : ∀ F : ℝ, 0 < F ^ 2 + (2 / 3) * F * (1 - F) + (5 / 9) * (1 - F) ^ 2 := by
    intro F
    nlinarith [sq_nonneg (F - 1 / 4)]
  have hcont : Continuous recurrenceMap := by
    unfold recurrenceMap
    exact Continuous.div (by fun_prop) (by fun_prop) (fun F => (hD F).ne')
  have hkey : ∀ F : ℝ, (F ^ 2 + (1 / 9) * (1 - F) ^ 2) -
      F * (F ^ 2 + (2 / 3) * F * (1 - F) + (5 / 9) * (1 - F) ^ 2) =
      (1 / 9) * ((1 - F) * (2 * F - 1) * (4 * F - 1)) := by
    intro F
    ring
  have hlt : ∀ F : ℝ, 1 / 2 < F → F < 1 → F < recurrenceMap F := by
    intro F h1 h2
    unfold recurrenceMap
    rw [lt_div_iff₀ (hD F)]
    have hp : 0 < (1 - F) * (2 * F - 1) * (4 * F - 1) :=
      mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    have := hkey F
    linarith
  have hge : ∀ F : ℝ, 1 / 2 < F ∧ F ≤ 1 → F ≤ recurrenceMap F := by
    rintro F ⟨h1, h2⟩
    unfold recurrenceMap
    rw [le_div_iff₀ (hD F)]
    have hp : 0 ≤ (1 - F) * (2 * F - 1) * (4 * F - 1) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have := hkey F
    linarith
  have hle1 : ∀ F : ℝ, 1 / 2 < F ∧ F ≤ 1 → recurrenceMap F ≤ 1 := by
    rintro F ⟨h1, h2⟩
    unfold recurrenceMap
    rw [div_le_one (hD F)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by linarith : (0:ℝ) ≤ F + 2)]
  have hmaps : ∀ F : ℝ, 1 / 2 < F ∧ F ≤ 1 → 1 / 2 < recurrenceMap F ∧ recurrenceMap F ≤ 1 :=
    fun F hF => ⟨lt_of_lt_of_le hF.1 (hge F hF), hle1 F hF⟩
  refine ⟨hcont, hlt, ?_⟩
  intro F₀ h1 h2
  have hsucc : ∀ k : ℕ, recurrenceMap^[k + 1] F₀ = recurrenceMap (recurrenceMap^[k] F₀) :=
    fun k => Function.iterate_succ_apply' _ _ _
  have hinv : ∀ k : ℕ, 1 / 2 < recurrenceMap^[k] F₀ ∧ recurrenceMap^[k] F₀ ≤ 1 := by
    intro k
    induction k with
    | zero => exact ⟨h1, h2⟩
    | succ k ih =>
      rw [hsucc]
      exact hmaps _ ih
  have hmono : Monotone (fun k : ℕ => recurrenceMap^[k] F₀) :=
    monotone_nat_of_le_succ (fun k => by
      show recurrenceMap^[k] F₀ ≤ recurrenceMap^[k + 1] F₀
      rw [hsucc]
      exact hge _ (hinv k))
  have hbdd : BddAbove (Set.range (fun k : ℕ => recurrenceMap^[k] F₀)) :=
    ⟨1, by rintro _ ⟨k, rfl⟩; exact (hinv k).2⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  have hL1 : (⨆ k : ℕ, recurrenceMap^[k] F₀) ≤ 1 := ciSup_le (fun k => (hinv k).2)
  have hL0 : F₀ ≤ ⨆ k : ℕ, recurrenceMap^[k] F₀ := le_ciSup hbdd 0
  have hfix : recurrenceMap (⨆ k : ℕ, recurrenceMap^[k] F₀) = ⨆ k : ℕ, recurrenceMap^[k] F₀ := by
    have t1 : Tendsto (fun k : ℕ => recurrenceMap^[k + 1] F₀) atTop
        (𝓝 (⨆ k : ℕ, recurrenceMap^[k] F₀)) := hlim.comp (tendsto_add_atTop_nat 1)
    have t2 : Tendsto (fun k : ℕ => recurrenceMap (recurrenceMap^[k] F₀)) atTop
        (𝓝 (recurrenceMap (⨆ k : ℕ, recurrenceMap^[k] F₀))) := (hcont.tendsto _).comp hlim
    have e : (fun k : ℕ => recurrenceMap^[k + 1] F₀) =
        fun k : ℕ => recurrenceMap (recurrenceMap^[k] F₀) := funext hsucc
    rw [e] at t1
    exact tendsto_nhds_unique t2 t1
  have hL : (⨆ k : ℕ, recurrenceMap^[k] F₀) = 1 := by
    by_contra hne
    have hlt' : (⨆ k : ℕ, recurrenceMap^[k] F₀) < 1 := lt_of_le_of_ne hL1 hne
    have := hlt _ (by linarith) hlt'
    linarith
  rw [← hL]
  exact hlim
