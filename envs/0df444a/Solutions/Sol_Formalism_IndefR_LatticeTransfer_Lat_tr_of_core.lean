-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.Lat.tr_of_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:52.016871+00:00
-- url     : https://prove2.me/submissions/af3ca1c5-6adc-4a8b-9529-460c416b1f46

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_pe_facts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer Formalism.IndefR.LatticeTransfer.Lat
open Formalism.IndefR.TransferLatticeStatement Formalism.HN Formalism.IndefR.LatticeTransfer
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.IndefR.LatticeTransfer.Lat
theorem _root_.solution (hP : IdemP) {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    {τ : Representation K G T} {H₀ : Subgroup G} {χ₀ : H₀ →* (𝓞 K)ˣ} {H : Subgroup G}
    {χ : H →* (𝓞 K)ˣ} {n : ℕ} {γ δ : Fin n → G} {c : Matrix (Fin n) (Fin n) K}
    {Γ : Matrix (Fin n) (Fin n) (𝓞 K)} (h : CoreData τ H₀ χ₀ H χ γ δ c Γ)
    (ρ : Representation K G V) (he : eS τ ρ ∘ₗ eS τ ρ = eS τ ρ) :
    Tr (epP H₀ χ₀ ρ ∘ₗ eS τ ρ) (epP H χ ρ ∘ₗ eS τ ρ) (fun j => epP H χ ρ ∘ₗ ρ (γ j))
      (fun i => epP H₀ χ₀ ρ ∘ₗ ρ (δ i)) c := by
  obtain ⟨hE, hEp⟩ := hP K G V ρ
  obtain ⟨hc, hcp, -⟩ := hE T τ
  have f0 := pe_facts (hEp H₀ χ₀).1 he (hcp H₀ χ₀)
  have f1 := pe_facts (hEp H χ).1 he (hcp H χ)
  have key : ∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) (g : G) (a : V), eS τ ρ a = a →
      (epP H χ ρ ∘ₗ eS τ ρ) ((epP H χ ρ ∘ₗ ρ g) a) = (epP H χ ρ ∘ₗ ρ g) a := by
    intro H χ g a ha
    have h1 : ∀ a, epP H χ ρ (epP H χ ρ a) = epP H χ ρ a :=
      fun a => LinearMap.congr_fun (hEp H χ).1 a
    have h2 : ∀ a, eS τ ρ (epP H χ ρ a) = epP H χ ρ (eS τ ρ a) :=
      fun a => LinearMap.congr_fun (hcp H χ) a
    have h3 : eS τ ρ (ρ g a) = ρ g (eS τ ρ a) := LinearMap.congr_fun (hc g) a
    simp only [LinearMap.comp_apply, h2, h1, h3, ha]
  obtain ⟨hd, -, -, hV⟩ := h
  refine ⟨f0.1, f1.1, fun j a ha => key H χ _ a ((f0.2 a).1 ha).2,
    fun i a ha => key H₀ χ₀ _ a ((f1.2 a).1 ha).2, hd, fun i j a ha => (hV V ρ).1 i j a ha,
    fun a ha => (hV V ρ).2 a ha⟩
end Formalism.IndefR.LatticeTransfer.Lat
