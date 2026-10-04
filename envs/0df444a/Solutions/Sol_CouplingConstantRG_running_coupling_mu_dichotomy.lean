-- Prove2me | solution 1 for CouplingConstantRG.running_coupling_mu_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T16:54:29.876838+00:00
-- url     : https://prove2.me/submissions/1564adf5-03e7-48c6-9091-aacfbe7ba38d

import Mathlib
import Definitions.Def_CouplingConstantRGDefs
import Theorems.Thm_CouplingConstantRG_landau_pole_mu
import Theorems.Thm_CouplingConstantRG_isMuRunning_inv_relation

set_option autoImplicit false
set_option linter.unusedVariables false

open CouplingConstantRG Real Set Filter

theorem solution (b μ₀ α₀ : ℝ) (hμ₀ : 0 < μ₀) (hα₀ : 0 < α₀) :
    (b < 0 → ∀ α : ℝ → ℝ, α μ₀ = α₀ → IsMuRunning b α (Set.Ici μ₀) →
        (∀ μ, μ₀ ≤ μ → α μ = α₀ / (1 - b * α₀ * Real.log (μ / μ₀))) ∧
          Filter.Tendsto α Filter.atTop (nhds 0)) ∧
      (0 < b → ¬ ∃ α : ℝ → ℝ, α μ₀ = α₀ ∧
        IsMuRunning b α (Set.Icc μ₀ (μ₀ * Real.exp (1 / (b * α₀))))) := by
  constructor
  · intro hb α h₀ hα
    have hformula : ∀ μ, μ₀ ≤ μ → α μ = α₀ / (1 - b * α₀ * log (μ / μ₀)) := by
      intro μ hμ
      have hrun : IsMuRunning b α (Icc μ₀ μ) := by
        intro t ht
        exact hα t ht.1
      have hprod : α μ * (1 - b * α₀ * log (μ / μ₀)) = α₀ :=
        isMuRunning_inv_relation b μ₀ μ α₀ α hμ₀ hμ hα₀ h₀ hrun μ ⟨hμ, le_rfl⟩
      have hlog0 : 0 ≤ log (μ / μ₀) := log_nonneg ((one_le_div hμ₀).2 hμ)
      have hden_ge : (1 : ℝ) ≤ 1 - b * α₀ * log (μ / μ₀) := by
        have hnn : 0 ≤ -(b * α₀ * log (μ / μ₀)) := by
          have hb0 : 0 ≤ -b := neg_nonneg.mpr hb.le
          have : 0 ≤ (-b) * α₀ * log (μ / μ₀) :=
            mul_nonneg (mul_nonneg hb0 hα₀.le) hlog0
          simpa [neg_mul, mul_assoc] using this
        linarith
      have hden_ne : 1 - b * α₀ * log (μ / μ₀) ≠ 0 := by linarith
      exact (eq_div_iff hden_ne).2 (by simpa [mul_comm] using hprod)
    refine ⟨hformula, ?_⟩
    have hlim : Tendsto (fun μ : ℝ => α₀ / (1 - b * α₀ * log (μ / μ₀))) atTop (nhds 0) := by
      have hdiv : Tendsto (fun μ : ℝ => μ / μ₀) atTop atTop :=
        tendsto_id.atTop_div_const hμ₀
      have hlog : Tendsto (fun μ : ℝ => log (μ / μ₀)) atTop atTop :=
        tendsto_log_atTop.comp hdiv
      have hcoeff : 0 < -b * α₀ := mul_pos (neg_pos.mpr hb) hα₀
      have hmul : Tendsto (fun μ : ℝ => (-b * α₀) * log (μ / μ₀)) atTop atTop :=
        hlog.const_mul_atTop hcoeff
      have hden : Tendsto (fun μ : ℝ => 1 - b * α₀ * log (μ / μ₀)) atTop atTop := by
        rw [tendsto_atTop]
        intro C
        filter_upwards [(tendsto_atTop.1 hmul) (C - 1)] with μ hμ
        have hle : C - 1 ≤ (-b * α₀) * log (μ / μ₀) := hμ
        have heq : 1 - b * α₀ * log (μ / μ₀) = 1 + (-b * α₀) * log (μ / μ₀) := by ring
        linarith
      exact tendsto_const_nhds.div_atTop hden
    have hev : (fun μ => α μ) =ᶠ[atTop] fun μ => α₀ / (1 - b * α₀ * log (μ / μ₀)) := by
      filter_upwards [eventually_ge_atTop μ₀] with μ hμ
      exact hformula μ hμ
    exact hlim.congr' hev.symm
  · intro hb
    exact landau_pole_mu b μ₀ α₀ hb hμ₀ hα₀
