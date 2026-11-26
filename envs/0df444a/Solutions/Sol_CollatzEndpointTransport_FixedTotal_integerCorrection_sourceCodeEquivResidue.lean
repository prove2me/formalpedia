-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.integerCorrection_sourceCodeEquivResidue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:25:27.688814+00:00
-- url     : https://prove2.me/submissions/877fe409-6bf7-4d1c-92e1-d0d486ae22d6

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_parityVec_sourceCodeEquivResidue
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrection_parityVec


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M : ℕ) (x : SourceCode M) :
    Terras.integerCorrection M (sourceCodeEquivResidue M x : ℕ) =
      sourceCodeCorrection x := by
  rw [← wordCorrection_parityVec]
  rw [parityVec_sourceCodeEquivResidue]
  rw [ofFn_sourceCodeWord]
  exact wordCorrection_sourceCodeList x
end CollatzEndpointTransport.FixedTotal
