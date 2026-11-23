-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.Xi_of_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:50.586413+00:00
-- url     : https://prove2.me/submissions/50a397e2-afb8-4a39-b6fc-a9833dfc9612

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Mv
variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
namespace Formalism.L2.PairingIndexBounds.Mv
theorem _root_.solution {c : B → A → k} {WA : A → T →ₗ[k] T} {WB : B → T →ₗ[k] T} {A₀ : AddSubgroup A} {θ : T}
    {Xi : Sch c A₀ →ₗ[k] T} (hXi : IsXi c WA WB A₀ θ Xi) {ι : Type*} (s : Finset ι) (r : ι → k) (a : ι → A)
    (b : ι → B) (Φ : A → k) (hΦ : Φ = ∑ i ∈ s, r i • gen c A₀ (a i) (b i)) :
    ∃ h : Φ ∈ Sch c A₀, Xi ⟨Φ, h⟩ = ∑ i ∈ s, r i • WA (a i) (WB (b i) θ) := by
  subst hΦ
  refine ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (gen_mem c A₀ _ _), ?_⟩
  have e : (⟨∑ i ∈ s, r i • gen c A₀ (a i) (b i),
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (gen_mem c A₀ _ _)⟩ : Sch c A₀)
      = ∑ i ∈ s, r i • ⟨gen c A₀ (a i) (b i), gen_mem c A₀ (a i) (b i)⟩ := by
    apply Subtype.ext
    simp
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hXi]
end Formalism.L2.PairingIndexBounds.Mv
