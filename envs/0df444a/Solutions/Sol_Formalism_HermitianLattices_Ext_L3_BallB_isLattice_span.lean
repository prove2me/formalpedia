-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.isLattice_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:45.624024+00:00
-- url     : https://prove2.me/submissions/6e1f855c-2a72-4352-88aa-701e185da0b6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormSpanSingletonEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLand
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthBasisMem

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
theorem _root_.solution [FiniteDimensional K V] (b : Basis (Fin (finrank K V)) K V) :
    Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range b)) where
  fg := ⟨(Set.finite_range b).toFinset, by rw [Set.Finite.coe_toFinset]⟩
  span_eq_top := by
    rw [eq_top_iff, ← b.span_eq]
    exact Submodule.span_mono Submodule.subset_span
end Formalism.HermitianLattices.Ext.L3.BallB
