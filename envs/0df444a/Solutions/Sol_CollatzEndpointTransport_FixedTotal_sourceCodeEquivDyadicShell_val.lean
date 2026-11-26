-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceCodeEquivDyadicShell_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:57:52.464789+00:00
-- url     : https://prove2.me/submissions/9aabd718-d73f-4b74-a305-8c61348b2747

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalShellCoding

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M : ℕ} (x : SourceCode M) :
    ((sourceCodeEquivDyadicShell M x :
        {n // n ∈ QuantitativeDensity.dyadicShell M}) : ℕ) =
      sourceShellStart x := rfl
end CollatzEndpointTransport.FixedTotal
