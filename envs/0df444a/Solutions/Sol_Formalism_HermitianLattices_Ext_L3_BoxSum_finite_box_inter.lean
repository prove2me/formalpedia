-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.finite_box_inter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:36.568357+00:00
-- url     : https://prove2.me/submissions/692911f0-92cd-4744-bc57-550a0cfdddde

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemIdealLatticeIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumCoset
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_finite_boxSet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) (A : Set (𝓞 F)) :
    {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ A}.Finite := (finite_boxSet hK hF T).subset fun _ hn => hn.1
end Formalism.HermitianLattices.Ext.L3.BoxSum
