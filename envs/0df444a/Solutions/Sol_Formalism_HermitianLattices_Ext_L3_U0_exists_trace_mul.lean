-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.exists_trace_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:42:18.579442+00:00
-- url     : https://prove2.me/submissions/c7cd25ba-3e01-4eba-ae14-928cbd639d13

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_mul_left
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_mul_right
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_unit_of_not_dv

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
open WA
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K} {π : K}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution (hS : IsHermSemilocal S) (hπ : IsUnif S π) {σ : K} (hσ : σ ∈ S)
    (hn : ¬ Dv S π σ) {τ : K} (hτ : τ ∈ S) (hτf : star τ = τ) :
    ∃ s ∈ S, σ * s + star (σ * s) = τ := by
  obtain ⟨θ, hθ, hμ⟩ := hS.unram
  have key : ∀ t ∈ S, IsUnitIn S (σ * t + star (σ * t)) → ∃ s ∈ S, σ * s + star (σ * s) = τ := by
    intro t ht hu
    have hf : star (σ * t + star (σ * t)) = σ * t + star (σ * t) := by
      rw [star_add, star_star, add_comm]
    refine ⟨t * (τ * (σ * t + star (σ * t))⁻¹), S.mul_mem ht (S.mul_mem hτ hu.2.2), ?_⟩
    have e : star (σ * (t * (τ * (σ * t + star (σ * t))⁻¹))) =
        star (σ * t) * (τ * (σ * t + star (σ * t))⁻¹) := by
      rw [← mul_assoc, star_mul', star_mul' τ, star_inv₀, hf, hτf]
    rw [e]
    have := hu.1
    field_simp
  by_cases h1 : Dv S π (σ * 1 + star (σ * 1))
  · by_cases h2 : Dv S π (σ * θ + star (σ * θ))
    · exfalso
      apply hn
      have e : σ = ((σ * θ + star (σ * θ)) - star θ * (σ * 1 + star (σ * 1))) * (θ - star θ)⁻¹ := by
        have := hμ.1
        rw [eq_mul_inv_iff_mul_eq₀ this]
        simp only [star_mul', mul_one]
        ring
      rw [e]
      exact (h2.sub (h1.mul_left (hS.star_mem _ hθ))).mul_right hμ.2.2
    · refine key θ hθ (unit_of_not_dv hπ ?_ ?_ h2)
      · exact S.add_mem (S.mul_mem hσ hθ) (hS.star_mem _ (S.mul_mem hσ hθ))
      · rw [star_add, star_star, add_comm]
  · refine key 1 S.one_mem (unit_of_not_dv hπ ?_ ?_ h1)
    · exact S.add_mem (S.mul_mem hσ S.one_mem) (hS.star_mem _ (S.mul_mem hσ S.one_mem))
    · rw [star_add, star_star, add_comm]
end Formalism.HermitianLattices.Ext.L3.U0
