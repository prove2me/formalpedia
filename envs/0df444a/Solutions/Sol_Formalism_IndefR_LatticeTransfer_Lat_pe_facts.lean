-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.Lat.pe_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:16.036348+00:00
-- url     : https://prove2.me/submissions/8e19b204-7713-47f4-abd7-b10b534a2668

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem

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
theorem _root_.solution {ε e : V →ₗ[K] V} (hε : ε ∘ₗ ε = ε) (he : e ∘ₗ e = e) (hc : e ∘ₗ ε = ε ∘ₗ e) :
    (∀ a, (ε ∘ₗ e) ((ε ∘ₗ e) a) = (ε ∘ₗ e) a) ∧
    ∀ a, (ε ∘ₗ e) a = a ↔ ε a = a ∧ e a = a := by
  have h1 : ∀ a, ε (ε a) = ε a := fun a => LinearMap.congr_fun hε a
  have h2 : ∀ a, e (e a) = e a := fun a => LinearMap.congr_fun he a
  have h3 : ∀ a, e (ε a) = ε (e a) := fun a => LinearMap.congr_fun hc a
  refine ⟨fun a => ?_, fun a => ⟨fun h => ?_, fun h => ?_⟩⟩
  · simp only [LinearMap.comp_apply, h3, h1, h2]
  · simp only [LinearMap.comp_apply] at h
    constructor
    · rw [← h, h1]
    · rw [← h, h3, h2]
  · simp only [LinearMap.comp_apply, h.1, h.2]
end Formalism.IndefR.LatticeTransfer.Lat
