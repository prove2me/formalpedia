-- Prove2me | solution 1 for DFT.levy_constrained_search
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:36:28.554096+00:00
-- url     : https://prove2.me/submissions/2ad1789a-d6f5-4249-9fc0-a877b93edb20

import Definitions.Def_DFT_HohenbergKohn

open MeasureTheory
open DFT

theorem solution (M : HKModel) {v : M.Pot} {Ψ₀ : M.Wf}
    (h : M.IsGroundState v Ψ₀) :
    M.energy v Ψ₀ = sInf ((fun n => M.levyFunctional n + M.ext v n) '' Set.range M.dens) := by
  have hbdd : ∀ n : M.Dens, BddBelow (M.F '' {Ψ : M.Wf | M.dens Ψ = n}) := by
    intro n
    refine ⟨M.energy v Ψ₀ - M.ext v n, ?_⟩
    rintro _ ⟨Φ, hΦ, rfl⟩
    have := h Φ
    unfold HKModel.energy at this ⊢
    rw [hΦ] at this
    simp only [Set.mem_setOf_eq] at hΦ
    linarith
  have hge : ∀ Φ : M.Wf, M.energy v Ψ₀ ≤ M.levyFunctional (M.dens Φ) + M.ext v (M.dens Φ) := by
    intro Φ
    have : M.energy v Ψ₀ - M.ext v (M.dens Φ) ≤ M.levyFunctional (M.dens Φ) := by
      unfold HKModel.levyFunctional
      refine le_csInf ⟨M.F Φ, Φ, rfl, rfl⟩ ?_
      rintro _ ⟨Φ', hΦ', rfl⟩
      have := h Φ'
      simp only [Set.mem_setOf_eq] at hΦ'
      unfold HKModel.energy at this ⊢
      rw [hΦ'] at this
      linarith
    linarith
  have hle : M.levyFunctional (M.dens Ψ₀) ≤ M.F Ψ₀ :=
    csInf_le (hbdd _) ⟨Ψ₀, rfl, rfl⟩
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨M.dens Ψ₀, ⟨Ψ₀, rfl⟩, ?_⟩, ?_⟩
  · have := hge Ψ₀
    unfold HKModel.energy at this ⊢
    linarith
  · rintro _ ⟨_, ⟨Φ, rfl⟩, rfl⟩
    exact hge Φ
