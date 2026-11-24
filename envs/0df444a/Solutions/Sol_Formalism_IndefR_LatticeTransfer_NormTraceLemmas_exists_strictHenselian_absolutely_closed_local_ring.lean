-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.NormTraceLemmas.exists_strictHenselian_absolutely_closed_local_ring
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:52.25184+00:00
-- url     : https://prove2.me/submissions/a7d1af93-0a39-45f3-9bfb-6b90a0ef888f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Lemmata_RankOneOrbitForms_RankOneForm
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_ExistsStrictHenselianAbsolutelyClosedLocalRing
import Theorems.Thm_Bl_RankOneOrbitForms_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.NormTraceLemmas
variable {K : Type} [Field K] {G : Type} [Group G]
  {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
namespace Formalism.IndefR.LatticeTransfer.NormTraceLemmas
theorem _root_.solution (τ : Representation K G T)
    (hirr : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ε₀ ε : T →ₗ[K] T) (h1 : finrank K (LinearMap.range ε₀) = 1) :
    ∃ (γ δ : Fin (finrank K (LinearMap.range ε)) → G)
      (c : Matrix (Fin (finrank K (LinearMap.range ε))) (Fin (finrank K (LinearMap.range ε))) K),
      c.det ≠ 0 ∧
      (∀ i j, c i j = LinearMap.trace K T (ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j))) ∧
      (∀ i j, ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j) ∘ₗ ε₀ = c i j • ε₀) ∧
      ∑ j, ∑ i, c⁻¹ j i • (ε ∘ₗ τ (γ j) ∘ₗ ε₀ ∘ₗ τ (δ i) ∘ₗ ε) = ε := by
  first | exact Bl.RankOneOrbitForms.goal1 .. | (apply Bl.RankOneOrbitForms.goal1 <;> assumption) | (intros; apply Bl.RankOneOrbitForms.goal1 <;> assumption)
end Formalism.IndefR.LatticeTransfer.NormTraceLemmas
