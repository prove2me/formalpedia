-- Prove2me | solution 1 for FirstPassageLinearTransport.assembledHeightCertified_naturalDensityOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:12.517491+00:00
-- url     : https://prove2.me/submissions/d45e54a6-0c72-4800-8d9e-367f6be32a79

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Theorems.Thm_FirstPassageLinearTransport_heightCertifiedShellRatioTendstoZero
import Theorems.Thm_FirstPassageLinearTransport_naturalDensityOne_assembleDyadic


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta chi Dc omega zeta alpha : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega : 0 < omega)
    (hdensity : densityGamma omega chi < 1)
    (hzeta : 0 < zeta) (halpha : 0 < alpha) :
    NaturalDensityOne (assembledHeightCertified p omega zeta alpha) := by
  exact naturalDensityOne_assembleDyadic _
    (heightCertifiedShellRatioTendstoZero p hchi0 hchir hchi1
      hDc0 hDc1 hDcRate hchiDc homega hdensity hzeta halpha)
end FirstPassageLinearTransport
