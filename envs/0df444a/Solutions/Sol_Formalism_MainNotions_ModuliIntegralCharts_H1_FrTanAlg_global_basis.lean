-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg.global_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:20:38.330661+00:00
-- url     : https://prove2.me/submissions/e8c1a33f-3874-4c17-a8f9-84d2e57622e1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanAlg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanAlg_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
open Polynomial NumberField
variable {E : Type} [Field E] [NumberField E] {S M : Type} [Field S] [CharZero S] [AddCommGroup M] [Module S M]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
theorem _root_.solution (χ : ι → (E →+* S)) (hχ : Function.Injective χ)
    (hcard : Fintype.card ι = Module.finrank ℚ E) (ρ : 𝓞 E →+* Module.End S M) {mult : ι → ℕ}
    (U : (Σ σ, Fin (mult σ)) → M) (hU : ∀ σ i (a : 𝓞 E), ρ a (U ⟨σ, i⟩) = χ σ (a : E) • U ⟨σ, i⟩)
    (hb : ∀ σ (W : M), (∀ a : 𝓞 E, ρ a W = χ σ (a : E) • W) →
      ∃! c : Fin (mult σ) → S, ∑ i, c i • U ⟨σ, i⟩ = W)
    (W : M) : ∃! a : (Σ σ, Fin (mult σ)) → S, ∑ ℓ, a ℓ • U ℓ = W := by
  classical
  obtain ⟨hex, huniq⟩ := decomp χ hχ hcard ρ
  have heig : ∀ σ (c : Fin (mult σ) → S) (a : 𝓞 E),
      ρ a (∑ i, c i • U ⟨σ, i⟩) = χ σ (a : E) • ∑ i, c i • U ⟨σ, i⟩ := by
    intro σ c a
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hU, smul_comm]
  obtain ⟨mσ, hmσ, hsum⟩ := hex W
  have hex' := fun σ => (hb σ (mσ σ) (hmσ σ)).exists
  choose c hc using hex'
  refine ⟨fun ℓ => c ℓ.1 ℓ.2, ?_, ?_⟩
  · show ∑ ℓ, c ℓ.1 ℓ.2 • U ℓ = W
    rw [Fintype.sum_sigma, ← hsum]
    exact Finset.sum_congr rfl fun σ _ => hc σ
  · intro a ha
    have hn : ∀ σ, ∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ = mσ σ := by
      have h0 := huniq (fun σ => ∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ - mσ σ)
        (fun σ b => by
          rw [map_sub, smul_sub, heig σ (fun i => a ⟨σ, i⟩) b, hmσ σ b])
        (by
          rw [Finset.sum_sub_distrib, hsum, ← ha, Fintype.sum_sigma, sub_self])
      intro σ
      exact sub_eq_zero.mp (h0 σ)
    funext ℓ
    obtain ⟨σ, i⟩ := ℓ
    have := (hb σ (mσ σ) (hmσ σ)).unique (hn σ) (hc σ)
    exact congrFun this i
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
