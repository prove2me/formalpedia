-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.Lat.smul_mem_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:59.312269+00:00
-- url     : https://prove2.me/submissions/8130846c-bf6e-4d2a-b22c-2148149946e8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_mem_cut
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_map_osmul

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
theorem _root_.solution (hP : IdemP) (ρ : Representation K G V) {A : Submodule (𝓞 K) V}
    (hA : ∀ g : G, ∀ a ∈ A, ρ g a ∈ A) (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) (g : G)
    {p : V →ₗ[K] V} (hp : ∀ a, p (p a) = p a) {a : V} (ha : a ∈ A)
    (hx : p ((epP H χ ρ ∘ₗ ρ g) a) = (epP H χ ρ ∘ₗ ρ g) a) :
    (Fintype.card G : 𝓞 K) • (epP H χ ρ ∘ₗ ρ g) a ∈ cut A p := by
  rw [mem_cut hp]
  refine ⟨((hP K G V ρ).2 H χ).2 A hA _ (hA g a ha), ?_⟩
  rw [map_osmul, hx]
end Formalism.IndefR.LatticeTransfer.Lat
