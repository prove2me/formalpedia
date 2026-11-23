-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.update_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:55.097311+00:00
-- url     : https://prove2.me/submissions/66160d90-1f47-4a5a-b84e-651b81ac77eb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BallB
theorem _root_.solution {L : Submodule (𝓞 K) V} {n : ℕ} {x : Fin n → V} {i : Fin n}
    (hx : ∀ k, k ≠ i → x k ∈ L) {y : V} (hy : y ∈ L) : ∀ k, Function.update x i y k ∈ L := by
  intro k
  by_cases hk : k = i
  · subst hk; rwa [Function.update_self]
  · rw [Function.update_of_ne hk]; exact hx k hk
end Formalism.HermitianLattices.Ext.L3.BallB
