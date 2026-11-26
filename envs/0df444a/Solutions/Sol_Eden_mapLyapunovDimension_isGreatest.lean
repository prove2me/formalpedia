-- Prove2me | solution 1 for Eden.mapLyapunovDimension_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:03:41.369099+00:00
-- url     : https://prove2.me/submissions/fc8b0e6d-be8e-445d-ae3d-2aab32a8e3cc

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
import Theorems.Thm_Eden_admissibleDimensions_nonempty
import Theorems.Thm_Eden_isCompact_admissibleDimensions

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {A : PhaseSpace →ₗ[ℝ] PhaseSpace}
    (hA : Function.Injective A) : IsGreatest (admissibleDimensions A) (mapLyapunovDimension A) :=
  (isCompact_admissibleDimensions hA).isGreatest_sSup (admissibleDimensions_nonempty A)
end Eden
