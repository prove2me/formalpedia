-- Prove2me | solution 1 for Eden.lyapunovExponent_eq_descending
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:14:37.667518+00:00
-- url     : https://prove2.me/submissions/90ea63a7-5f5d-4ae4-9024-28a1ef138615

import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_Sorting
import Definitions.Def_Eden_LyapunovExponents
import Theorems.Thm_Eden_tendsto_normalizedLogSingularValues

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) (i : Fin 5) :
    lyapunovExponent c p i = descending (factorExponents c p) i :=
  (tendsto_pi_nhds.mp (tendsto_normalizedLogSingularValues c p) i).limUnder_eq
end Eden
