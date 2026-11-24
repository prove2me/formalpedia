-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.mem_sSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:40:57.879068+00:00
-- url     : https://prove2.me/submissions/5ec507ef-511d-4a01-8891-cc330d6f6d80

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ}
    {X : V ≃ₗ[K] V} : X ∈ sSub h A 𝔭 k ↔
      X ∈ glSub A ∧ ∀ x ∈ A, ∀ y ∈ A, h (X x) (X y) - h x y ∈ pK K 𝔭 k := Iff.rfl
end Formalism.HermitianLattices.Ext.L3.D2
