-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.parityVec_sourceShellStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:27:00.660444+00:00
-- url     : https://prove2.me/submissions/b751f640-6156-493c-ae85-162080e19b10

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceShellStart_modEq_residue
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_parityVec_sourceCodeEquivResidue
import Theorems.Thm_CollatzEndpointTransport_Terras_parityVec_congr


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M : ℕ} (x : SourceCode M) :
    Terras.parityVec M (sourceShellStart x) = sourceCodeWord x := by
  calc
    Terras.parityVec M (sourceShellStart x) =
        Terras.parityVec M (sourceCodeEquivResidue M x : ℕ) :=
      Terras.parityVec_congr (sourceShellStart_modEq_residue x)
    _ = sourceCodeWord x := parityVec_sourceCodeEquivResidue M x
end CollatzEndpointTransport.FixedTotal
