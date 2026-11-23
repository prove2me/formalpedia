-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.gmap_eq_of_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:20.991325+00:00
-- url     : https://prove2.me/submissions/f91d25dc-81e6-4dd0-9c7f-9860e276d00a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsASDOfTuple
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero

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
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.U0
open WA
omit [NumberField K] [StarRing K] [FiniteDimensional K V]
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution {g : V ≃ₗ[K] V} {A B : Submodule (𝓞 K) V} (hg : ∀ v, v ∈ A ↔ g v ∈ B) :
    Formalism.HermitianLatticesTheory.gmap g A = B := by
  ext w
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (hg v).mp hv
  · intro hw
    exact ⟨g.symm w, (hg _).mpr (by rw [g.apply_symm_apply]; exact hw), g.apply_symm_apply w⟩
end Formalism.HermitianLattices.Ext.L3.U0
