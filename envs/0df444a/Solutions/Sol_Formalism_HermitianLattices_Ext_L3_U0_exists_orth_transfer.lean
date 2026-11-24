-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.exists_orth_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:46.997372+00:00
-- url     : https://prove2.me/submissions/1799d57b-b51f-4d0b-a09c-7c78ae0d41cc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA Module
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution (hd : ∀ x, h x x = 0 → x = 0) {W₁ W₂ : Submodule K V}
    {ψ : V ≃ₗ[K] V} (hψ : ∀ a b, h (ψ a) (ψ b) = h a b) (hW : ∀ v ∈ W₁, ψ v ∈ W₂) {z₁ z₂ ξ : V}
    (hz₁ : z₁ ∈ W₁) (hz₁0 : z₁ ≠ 0) (hz₂ : z₂ ∈ W₂) (hz₂0 : z₂ ≠ 0) (hξ : ξ ∈ W₁) (hξ0 : ξ ≠ 0)
    (hzξ : h z₁ ξ = 0) : ∃ η ∈ W₂, η ≠ 0 ∧ h z₂ η = 0 := by
  have ha : ψ z₁ ∈ W₂ := hW z₁ hz₁
  have hb : ψ ξ ∈ W₂ := hW ξ hξ
  have haa : h (ψ z₁) (ψ z₁) ≠ 0 := by
    rw [hψ]
    exact fun h0 => hz₁0 (hd z₁ h0)
  have hb0 : ψ ξ ≠ 0 := fun h0 => hξ0 (ψ.injective (h0.trans (map_zero ψ).symm))
  have hab : h (ψ z₁) (ψ ξ) = 0 := by
    rw [hψ]
    exact hzξ
  by_cases h0 : h z₂ (ψ z₁) = 0
  · exact ⟨ψ z₁, ha, fun ha0 => haa (by simp [ha0]), h0⟩
  · refine ⟨(h z₂ (ψ ξ)) • ψ z₁ - (h z₂ (ψ z₁)) • ψ ξ,
      W₂.sub_mem (W₂.smul_mem _ ha) (W₂.smul_mem _ hb), ?_, ?_⟩
    · intro heq
      have hc := congrArg (h (ψ z₁)) heq
      simp only [map_sub, map_smul, smul_eq_mul, hab, mul_zero, sub_zero, map_zero] at hc
      rcases mul_eq_zero.mp hc with hb' | hb'
      · rw [hb', zero_smul, zero_sub, neg_eq_zero, smul_eq_zero] at heq
        exact heq.elim h0 hb0
      · exact haa hb'
    · simp only [map_sub, map_smul, smul_eq_mul]
      ring
end Formalism.HermitianLattices.Ext.L3.U0
