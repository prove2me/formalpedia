-- Prove2me | solution 1 for Falmagne.Examples.mixture_BM_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:32:00.659881+00:00
-- url     : https://prove2.me/submissions/2c54fa68-6dda-4033-bda5-566a6aea2094

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_mixtureLaw_isRankingLaw
public import Theorems.Thm_Falmagne_Examples_mixtureLaw_represents
public import Theorems.Thm_Falmagne_blockMarschak_necessary


set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
namespace Falmagne.Examples
theorem _root_.solution :
    ∀ x A, x ∈ A → 0 ≤ blockMarschak mixtureChoice x A := by
  exact blockMarschak_necessary mixtureLaw_isRankingLaw mixtureLaw_represents
end Falmagne.Examples
