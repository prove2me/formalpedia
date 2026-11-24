-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.ThickOrbit.bound_aux
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:33.291123+00:00
-- url     : https://prove2.me/submissions/9442d038-b5cb-417e-a851-c866a51fd401

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.ThickOrbit
namespace Formalism.FrobeniusOrbits.ThickOrbit
theorem _root_.solution {n L : ℕ} (j : ℤ) (s : ℕ) (hj : j ≤ L) (hs : 4 * L * s < n) :
    4 * (j * (s : ℤ)) < n := by
  have hs' : (4 * L * s : ℤ) < n := by exact_mod_cast hs
  have h0 : (0 : ℤ) ≤ s := by positivity
  nlinarith
end Formalism.FrobeniusOrbits.ThickOrbit
