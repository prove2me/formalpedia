-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.parityVec_sourceCodeEquivResidue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:51:17.444057+00:00
-- url     : https://prove2.me/submissions/15ba7929-cef3-425b-9610-62ac57baa83c

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M : ℕ) (x : SourceCode M) :
    Terras.parityVec M (sourceCodeEquivResidue M x : ℕ) =
      sourceCodeWord x := by
  change Terras.terrasMap M
      ((Terras.terrasEquiv M).symm (sourceCodeWord x)) =
        sourceCodeWord x
  exact (Terras.terrasEquiv M).apply_symm_apply _
end CollatzEndpointTransport.FixedTotal
