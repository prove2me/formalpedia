-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.RankOne.exists_ne_zero_of_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:40.383941+00:00
-- url     : https://prove2.me/submissions/a1b27f8c-7417-4112-b427-1026f0dc5699

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNeZeroOfIsLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne
open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.RankOne
theorem _root_.solution {A : Submodule (𝓞 K) K} (hA : Submodule.IsLattice K A) :
    ∃ a ∈ A, a ≠ 0 := by
  by_contra hne
  push_neg at hne
  have h2 : Submodule.span K (A : Set K) = ⊥ := by
    rw [Submodule.span_eq_bot]; exact hne
  have h3 : (1 : K) ∈ Submodule.span K (A : Set K) := by
    rw [hA.span_eq_top]; exact Submodule.mem_top
  rw [h2, Submodule.mem_bot] at h3
  exact one_ne_zero h3
end Formalism.HermitianLattices.Ext.L3.RankOne
