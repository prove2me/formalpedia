-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.RankOne.isLattice_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:12.022812+00:00
-- url     : https://prove2.me/submissions/44277fc5-c75b-4cf3-8b3a-2a78da2f005e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNeZeroOfIsLattice
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_exists_ne_zero_of_isLattice
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_span_eq_top_of_ne_zero

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
theorem _root_.solution {A B : Submodule (𝓞 K) K} (hA : Submodule.IsLattice K A)
    (hB : Submodule.IsLattice K B) : Submodule.IsLattice K (A * B) := by
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_of_isLattice hA
  obtain ⟨b, hb, hb0⟩ := exists_ne_zero_of_isLattice hB
  exact ⟨hA.fg.mul hB.fg, span_eq_top_of_ne_zero (Submodule.mul_mem_mul ha hb) (mul_ne_zero ha0 hb0)⟩
end Formalism.HermitianLattices.Ext.L3.RankOne
