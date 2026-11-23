-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.GramDeterminantPositive.exists_ortho_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:38:16.958797+00:00
-- url     : https://prove2.me/submissions/581fd8b9-205a-4aa0-90e4-27fd71247881

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
    (v : Fin k → V) (hk : k < finrank K V) : ∃ x : V, x ≠ 0 ∧ ∀ i, h (v i) x = 0 := by
  let f : V →ₗ[K] (Fin k → K) := LinearMap.pi fun i => h (v i)
  have hlt : finrank K (Fin k → K) < finrank K V := by
    rw [Module.finrank_fin_fun]; exact hk
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
  exact ⟨x, hx0, fun i => congrFun (LinearMap.mem_ker.1 hx) i⟩
end Formalism.HermitianLattices.Ext.L3.GramDeterminantPositive
