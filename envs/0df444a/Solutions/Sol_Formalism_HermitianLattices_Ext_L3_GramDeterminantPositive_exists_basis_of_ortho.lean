-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.GramDeterminantPositive.exists_basis_of_ortho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:22.44883+00:00
-- url     : https://prove2.me/submissions/1e173e36-b250-4d3e-ae05-0abf9bda7a7d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.GramDeterminantPositive
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLattices.Ext.L3.GramDeterminantPositive
theorem _root_.solution [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {k : ℕ}
    (v : Fin k → V) (hk : finrank K V = k) (ho : ∀ i j, i ≠ j → h (v i) (v j) = 0)
    (hne : ∀ i, h (v i) (v i) ≠ 0) : ∃ e : Basis (Fin k) K V, ∀ i, e i = v i := by
  have hli : LinearIndependent K v :=
    LinearMap.linearIndependent_of_isOrthoᵢ (B := h) (fun i j hij => ho i j hij) (fun i => hne i)
  have htop : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hk])
  exact ⟨Basis.mk hli htop.ge, fun i => Basis.mk_apply hli htop.ge i⟩
end Formalism.HermitianLattices.Ext.L3.GramDeterminantPositive
