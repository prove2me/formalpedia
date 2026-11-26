-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.log_two_eq_of_mem_dyadicShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:10:47.076052+00:00
-- url     : https://prove2.me/submissions/e7ae0d9f-ffe6-4844-af4d-1e351bfb5a4b

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_ShellToGlobalDensity
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {n M : ℕ} (hn : n ∈ QuantitativeDensity.dyadicShell M) :
    Nat.log 2 n = M := by
  rw [QuantitativeDensity.dyadicShell, Finset.mem_Ico] at hn
  exact Nat.log_eq_of_pow_le_of_lt_pow hn.1 hn.2
end CollatzEndpointTransport.Terras
