-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.exists_mixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:35.14999+00:00
-- url     : https://prove2.me/submissions/71395e2e-cbcc-4a4f-9879-71215ce9c3b2

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
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (b : Basis (Fin (finrank K V)) K V)
    {u w : Fin (finrank K V) → V} (hu : ∀ i, u i ∈ L) (hw : ∀ i, w i ∈ L) :
    ∃ z : 𝓞 K, algebraMap (𝓞 K) K z = star (b.det u) * gdet h b * b.det w := by
  choose g hg using fun i j => Submodule.mem_one.mp (hLi (u i) (hu i) (w j) (hw j))
  refine ⟨(Matrix.of g).det, ?_⟩
  rw [RingHom.map_det, gdet, ← gram_det_eq h b]
  congr 1
  ext i j
  exact hg i j
end Formalism.HermitianLattices.Ext.L3.BallB
