-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.Lat.sandwich
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:59.273577+00:00
-- url     : https://prove2.me/submissions/fd45d885-0433-4e56-9e5c-3ea81b0f3b2a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_mem_cut
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_map_osmul
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
variable {S : Type} [Fintype S] {T : S → Type} [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
  [∀ s, FiniteDimensional K (T s)] {τ : ∀ s, Representation K G (T s)}
namespace Formalism.IndefR.LatticeTransfer.Lat
theorem _root_.solution (hE : IdemE) (hP : IdemP) (hτ : IsGood τ) (ρ : Representation K G V)
    {A : Submodule (𝓞 K) V} (hA : ∀ g : G, ∀ a ∈ A, ρ g a ∈ A) (H : Subgroup G)
    (χ : H →* (𝓞 K)ˣ) :
    (∀ s, cut A (epP H χ ρ ∘ₗ eS (τ s) ρ) ≤ cut A (epP H χ ρ ∘ₗ eGood τ ρ)) ∧
    (∀ a ∈ cut A (epP H χ ρ ∘ₗ eGood τ ρ),
      (Fintype.card G : 𝓞 K) • a ∈ ⨆ s, cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) ∧
    ∀ s, ∀ a ∈ cut A (epP H χ ρ ∘ₗ eS (τ s) ρ), eS (τ s) ρ a = a := by
  obtain ⟨he, ho⟩ := hE K G S T τ hτ V ρ
  obtain ⟨hE', hEp⟩ := hP K G V ρ
  have f := fun s => pe_facts (hEp H χ).1 (he s) ((hE' (T s) (τ s)).2.1 H χ)
  have hge : ∀ s a, eGood τ ρ (eS (τ s) ρ a) = eS (τ s) ρ a := by
    intro s a
    classical
    unfold eGood
    rw [LinearMap.sum_apply, Finset.sum_eq_single s]
    · exact LinearMap.congr_fun (he s) a
    · intro t _ hts
      exact LinearMap.congr_fun (ho t s hts) a
    · simp
  refine ⟨fun s a ha => ⟨ha.1, ?_⟩, fun a ha => ?_, fun s a ha => ?_⟩
  · obtain ⟨z, hz⟩ := ha.2
    refine ⟨eS (τ s) ρ z, ?_⟩
    rw [← hz]
    simp only [LinearMap.comp_apply, hge]
  · obtain ⟨haA, z, hz⟩ := ha
    have hz' : a = ∑ s, epP H χ ρ (eS (τ s) ρ z) := by
      rw [← hz]
      simp only [LinearMap.comp_apply, eGood, LinearMap.sum_apply, map_sum]
    have hs : ∀ s, eS (τ s) ρ a = epP H χ ρ (eS (τ s) ρ z) := by
      intro s
      have h2 : ∀ a, eS (τ s) ρ (epP H χ ρ a) = epP H χ ρ (eS (τ s) ρ a) :=
        fun a => LinearMap.congr_fun ((hE' (T s) (τ s)).2.1 H χ) a
      have h3 : eS (τ s) ρ (eGood τ ρ z) = eS (τ s) ρ z := by
        classical
        unfold eGood
        rw [LinearMap.sum_apply, map_sum, Finset.sum_eq_single s]
        · exact LinearMap.congr_fun (he s) z
        · intro t _ hts
          exact LinearMap.congr_fun (ho s t hts.symm) z
        · simp
      rw [← hz, LinearMap.comp_apply, h2, h3]
    have : (Fintype.card G : 𝓞 K) • a = ∑ s, (Fintype.card G : 𝓞 K) • eS (τ s) ρ a := by
      rw [← Finset.smul_sum]
      simp only [hs]
      rw [← hz']
    rw [this]
    refine Submodule.sum_mem _ fun s _ => Submodule.mem_iSup_of_mem s ?_
    rw [mem_cut (f s).1]
    refine ⟨(hE' (T s) (τ s)).2.2 A hA a haA, ?_⟩
    rw [map_osmul, hs]
    exact congrArg _ ((f s).1 z)
  · exact (((f s).2 a).1 ((mem_cut (f s).1).1 ha).2).2
end Formalism.IndefR.LatticeTransfer.Lat
