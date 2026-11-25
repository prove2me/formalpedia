-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.global_basis_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:17:09.902869+00:00
-- url     : https://prove2.me/submissions/834161f9-5f78-43b0-a218-8429043cf6ee

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanDirAlg

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
open NumberField Matrix
variable {E : Type} [Field E] [NumberField E] {κ : Type} [Fintype κ]
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {ι : Type} [Fintype ι] [DecidableEq ι]
  [DecidableEq κ]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
theorem _root_.solution (ρ : 𝓞 E →+* Module.End R M) (χ : ι → 𝓞 E → R)
    (hdec : (∀ m : M, ∃ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) ∧ ∑ σ, mσ σ = m) ∧
      (∀ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) → ∑ σ, mσ σ = 0 → ∀ σ, mσ σ = 0))
    {mult : ι → ℕ} (U : (Σ σ, Fin (mult σ)) → M) (hU : ∀ σ i (a : 𝓞 E), ρ a (U ⟨σ, i⟩) = χ σ a • U ⟨σ, i⟩)
    (hb : ∀ σ (W : M), (∀ a : 𝓞 E, ρ a W = χ σ a • W) → ∃! c : Fin (mult σ) → R, ∑ i, c i • U ⟨σ, i⟩ = W)
    (W : M) : ∃! a : (Σ σ, Fin (mult σ)) → R, ∑ ℓ, a ℓ • U ℓ = W := by
  classical
  have heig : ∀ σ (c : Fin (mult σ) → R) (a : 𝓞 E),
      ρ a (∑ i, c i • U ⟨σ, i⟩) = χ σ a • ∑ i, c i • U ⟨σ, i⟩ := by
    intro σ c a
    simp only [map_sum, map_smul, hU, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  obtain ⟨mσ, hmσ, hsum⟩ := hdec.1 W
  choose c hc hcu using fun σ => hb σ (mσ σ) (hmσ σ)
  refine ⟨fun ℓ => c ℓ.1 ℓ.2, ?_, ?_⟩
  · have hs : ∑ ℓ : (Σ σ, Fin (mult σ)), c ℓ.1 ℓ.2 • U ℓ = ∑ σ, ∑ i, c σ i • U ⟨σ, i⟩ :=
      Fintype.sum_sigma _
    show ∑ ℓ : (Σ σ, Fin (mult σ)), c ℓ.1 ℓ.2 • U ℓ = W
    rw [hs]
    simp_rw [hc]
    exact hsum
  · intro a ha
    have hs : ∑ ℓ, a ℓ • U ℓ = ∑ σ, ∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ := Fintype.sum_sigma _
    have key : ∀ σ, ∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ = mσ σ := by
      have hz := hdec.2 (fun σ => ∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ - mσ σ)
        (fun σ a' => by
          show ρ a' (∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ - mσ σ) = χ σ a' • (∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ - mσ σ)
          rw [map_sub, heig, hmσ, smul_sub])
        (by
          show ∑ σ, (∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ - mσ σ) = 0
          rw [Finset.sum_sub_distrib, ← hs, ha, hsum, sub_self])
      exact fun σ => sub_eq_zero.1 (hz σ)
    funext ℓ
    obtain ⟨σ, i⟩ := ℓ
    exact congrFun (hcu σ (fun i => a ⟨σ, i⟩) (key σ)) i
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
