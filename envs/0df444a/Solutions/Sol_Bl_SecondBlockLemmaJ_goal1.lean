-- Prove2me | solution 1 for Bl.SecondBlockLemmaJ.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:28.737386+00:00
-- url     : https://prove2.me/submissions/d6eb90fd-b3dc-4801-aab7-66a064d905e3

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasI_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Bl Bl.SecondBlockLemmaJ
namespace Bl.SecondBlockLemmaJ
theorem _root_.solution {K L ι n : Type} [Field K] [Field L] [Fintype ι] [Fintype n] [DecidableEq ι]
    [DecidableEq n] (τ : K →+* L) (c : ι → n → K) (hc : LinearIndependent K c) :
    LinearIndependent L (fun a => fun i => τ (c a i)) := by
  let : Algebra K L := τ.toAlgebra
  have : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 τ.injective
  exact (linearIndependent_algebraMap_comp_iff (R := K) (S := L) (v := c)).2 hc
end Bl.SecondBlockLemmaJ
