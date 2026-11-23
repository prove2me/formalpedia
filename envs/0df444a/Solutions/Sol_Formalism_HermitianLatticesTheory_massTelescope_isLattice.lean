-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.massTelescope_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:46.507689+00:00
-- url     : https://prove2.me/submissions/1ab27405-1d97-4ce5-a10c-3112aaddfa63

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassTelescope

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
open Formalism Formalism.HermitianLatticesTheory
variable (K : Type) [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (n : ℕ) : Submodule.IsLattice K (massTelescope_lat K n) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [massTelescope_lat, Submodule.span_span_of_tower]
    exact (Pi.basisFun K (Fin n)).span_eq
end Formalism.HermitianLatticesTheory
