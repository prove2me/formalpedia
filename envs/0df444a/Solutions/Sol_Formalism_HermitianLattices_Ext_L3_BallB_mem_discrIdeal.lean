-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.mem_discrIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:15.175338+00:00
-- url     : https://prove2.me/submissions/c2503f0b-58f5-4d6c-8c3b-a77e60a27fdb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_gram_det_eq

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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (b : Basis (Fin (finrank K V)) K V) {x : Fin (finrank K V) → V} (hx : ∀ i, x i ∈ L) {z : 𝓞 K}
    (hz : algebraMap (𝓞 K) K z = star (b.det x) * gdet h b * b.det x) : z ∈ discrIdeal h L :=
  Ideal.subset_span ⟨x, hx, by rw [hz, gram_det_eq h b]; rfl⟩
end Formalism.HermitianLattices.Ext.L3.BallB
