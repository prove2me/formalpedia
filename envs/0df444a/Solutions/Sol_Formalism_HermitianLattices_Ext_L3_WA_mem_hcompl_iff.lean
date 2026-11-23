-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.mem_hcompl_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:05.896627+00:00
-- url     : https://prove2.me/submissions/1de47564-b918-4b5f-91ad-8948f9501544

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapNeZeroOfMemHcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_conjIdeal_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_hcompl_eq_closure

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
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : p.IsPrime) (s : 𝓞 K) :
    s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p ↔ s ∉ p ∧ s ∉ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by
  rw [hcompl_eq_closure, mem_conjIdeal_iff]
  constructor
  · intro hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one =>
      have h1 : (1 : 𝓞 K) ∉ p := (Ideal.ne_top_iff_one p).mp hp.ne_top
      exact ⟨h1, by rwa [map_one]⟩
    | mul x y _ _ ihx ihy =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact (hp.mem_or_mem h).elim ihx.1 ihy.1
      · rw [map_mul] at h
        exact (hp.mem_or_mem h).elim ihx.2 ihy.2
  · intro hs
    exact Submonoid.subset_closure hs
end Formalism.HermitianLattices.Ext.L3.WA
