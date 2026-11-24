-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:59:36.660949+00:00
-- url     : https://prove2.me/submissions/025f50c5-20bf-4130-a98f-51013a980e2d

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_conv_char
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sum_of_mul_sum_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {G V W : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (h : ∀ U : Submodule ℂ W, (∀ g, ∀ x ∈ U, σ g x ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∃ μ : ℂ, μ * (Module.finrank ℂ W : ℂ) = ∑ g, ρ.character g⁻¹ * σ.character g ∧
      centralIdem ρ * centralIdem σ =
        ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * μ) • centralIdem σ := by
  have ha : ∀ g k : G, ρ.character (k * g * k⁻¹)⁻¹ = ρ.character g⁻¹ := by
    intro g k
    simpa [mul_assoc] using ρ.char_conj g⁻¹ k
  obtain ⟨μ, hconv⟩ := conv_char σ h (fun g => ρ.character g⁻¹) ha
  have hone : σ.character 1 = (Module.finrank ℂ W : ℂ) := by
    first
      | exact σ.char_one
      | (unfold Representation.character; simp)
  refine ⟨μ, ?_, ?_⟩
  · have h1 := hconv 1
    simp only [mul_one, hone] at h1
    exact h1.symm
  · unfold centralIdem
    rw [sum_of_mul_sum_of, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_smul]
    congr 1
    have hcm : ∀ g : G, σ.character (k⁻¹ * g) = σ.character (g * k⁻¹) := fun g => by
      simpa [mul_assoc] using (σ.char_conj (k⁻¹ * g) g).symm
    have e1 : ∀ g : G, ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ρ.character g⁻¹) *
        ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ) * σ.character (g⁻¹ * k)⁻¹) =
        ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ))) *
        (ρ.character g⁻¹ * σ.character (g * k⁻¹)) := by
      intro g
      rw [mul_inv_rev, inv_inv, hcm]
      ring
    calc _ = ∑ g, ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) *
            ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ))) *
            (ρ.character g⁻¹ * σ.character (g * k⁻¹)) := Finset.sum_congr rfl (fun g _ => e1 g)
      _ = _ := by
        rw [← Finset.mul_sum, hconv k⁻¹]
        ring
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
