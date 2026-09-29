-- Prove2me | solution 1 for DFT.hk_variational_principle
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:35:01.953164+00:00
-- url     : https://prove2.me/submissions/d1afa464-f9d7-4527-ab68-281f2c631319

import Definitions.Def_DFT_HohenbergKohn

open MeasureTheory
open DFT

namespace Ag3Aux_HKVar

theorem uniq (M : HKModel) {v₁ v₂ : M.Pot} {Ψ₁ Ψ₂ : M.Wf}
    (h₁ : M.IsNondegenerateGroundState v₁ Ψ₁) (h₂ : M.IsNondegenerateGroundState v₂ Ψ₂)
    (hd : M.dens Ψ₁ = M.dens Ψ₂) : Ψ₁ = Ψ₂ := by
  by_contra hne
  have a := h₁ Ψ₂ (Ne.symm hne)
  have b := h₂ Ψ₁ hne
  unfold HKModel.energy at a b
  rw [hd] at a b
  linarith

theorem hkF (M : HKModel) {v : M.Pot} {Ψ : M.Wf}
    (h : M.IsNondegenerateGroundState v Ψ) : M.hkFunctional (M.dens Ψ) = M.F Ψ := by
  have hv : M.VRepresentable (M.dens Ψ) := ⟨Ψ, ⟨v, h⟩, rfl⟩
  unfold HKModel.hkFunctional
  rw [dif_pos hv]
  obtain ⟨⟨v', h'⟩, hd⟩ := hv.choose_spec
  rw [uniq M h' h hd]

end Ag3Aux_HKVar

open Ag3Aux_HKVar

theorem solution (M : HKModel) {v : M.Pot} {Ψ₀ : M.Wf}
    (h₀ : M.IsNondegenerateGroundState v Ψ₀) {n : M.Dens} (hn : M.VRepresentable n) :
    M.energy v Ψ₀ ≤ M.hkFunctional n + M.ext v n ∧
      (M.hkFunctional n + M.ext v n = M.energy v Ψ₀ ↔ n = M.dens Ψ₀) := by
  obtain ⟨Ψ, ⟨v', h'⟩, rfl⟩ := hn
  rw [hkF M h']
  change M.energy v Ψ₀ ≤ M.energy v Ψ ∧ (M.energy v Ψ = M.energy v Ψ₀ ↔ M.dens Ψ = M.dens Ψ₀)
  by_cases he : Ψ = Ψ₀
  · subst he; simp
  · have := h₀ Ψ he
    refine ⟨this.le, ⟨fun h => absurd h (ne_of_gt this), fun hd => absurd (uniq M h' h₀ hd) he⟩⟩
