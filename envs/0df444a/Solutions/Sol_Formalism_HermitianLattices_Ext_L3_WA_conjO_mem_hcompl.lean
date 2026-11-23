-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.conjO_mem_hcompl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:05.778822+00:00
-- url     : https://prove2.me/submissions/7e557c1b-341f-4f72-9a12-9f10bc5f8422

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapNeZeroOfMemHcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_hcompl_eq_closure
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.WA
theorem _root_.solution {p : Ideal (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    conjO K s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  rw [hcompl_eq_closure] at hs ⊢
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    apply Submonoid.subset_closure
    exact ⟨hx.2, by rw [conjO_conjO]; exact hx.1⟩
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ ihx ihy => rw [map_mul]; exact mul_mem ihx ihy
end Formalism.HermitianLattices.Ext.L3.WA
