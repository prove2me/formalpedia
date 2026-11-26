-- Prove2me | solution 1 for Eden.isCompact_admissibleDimensions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:02:44.017509+00:00
-- url     : https://prove2.me/submissions/fc351502-2490-4581-9617-82aca5f2b807

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
import Theorems.Thm_Eden_continuous_singularValueFunction

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {A : PhaseSpace →ₗ[ℝ] PhaseSpace}
    (hA : Function.Injective A) : IsCompact (admissibleDimensions A) :=
  isCompact_Icc.inter_right (isClosed_le continuous_const (continuous_singularValueFunction hA))
end Eden
