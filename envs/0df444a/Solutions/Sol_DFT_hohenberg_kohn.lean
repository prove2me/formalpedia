-- Prove2me | solution 1 for DFT.hohenberg_kohn
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:35:50.991494+00:00
-- url     : https://prove2.me/submissions/2a061e6d-e85b-4f50-bd92-7c0a59126a08

import Definitions.Def_DFT_HohenbergKohn

open MeasureTheory
open DFT

namespace Ag3Aux_HK

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

theorem varp (M : HKModel) {v : M.Pot} {Ψ₀ : M.Wf}
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

end Ag3Aux_HK

open Ag3Aux_HK

theorem solution (M : HKModel) :
    (∀ O : M.Wf → ℝ, ∃ O' : M.Dens → ℝ, ∀ (v : M.Pot) (Ψ : M.Wf),
        M.IsNondegenerateGroundState v Ψ → O Ψ = O' (M.dens Ψ)) ∧
      (∀ (v : M.Pot) (Ψ₀ : M.Wf), M.IsNondegenerateGroundState v Ψ₀ →
        ∀ n : M.Dens, M.VRepresentable n →
          M.hkFunctional (M.dens Ψ₀) + M.ext v (M.dens Ψ₀) ≤ M.hkFunctional n + M.ext v n ∧
            (M.hkFunctional n + M.ext v n
                = M.hkFunctional (M.dens Ψ₀) + M.ext v (M.dens Ψ₀) ↔ n = M.dens Ψ₀)) := by
  classical
  refine ⟨fun O => ?_, fun v Ψ₀ h₀ n hn => ?_⟩
  · refine ⟨fun n => if h : M.VRepresentable n then O h.choose else 0, fun v Ψ h => ?_⟩
    have hv : M.VRepresentable (M.dens Ψ) := ⟨Ψ, ⟨v, h⟩, rfl⟩
    simp only [dif_pos hv]
    obtain ⟨⟨v', h'⟩, hd⟩ := hv.choose_spec
    rw [uniq M h' h hd]
  · have e : M.hkFunctional (M.dens Ψ₀) + M.ext v (M.dens Ψ₀) = M.energy v Ψ₀ := by
      rw [hkF M h₀]; rfl
    rw [e]
    exact varp M h₀ hn
