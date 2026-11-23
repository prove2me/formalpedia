-- Prove2me | solution 1 for Formalism.H.covolDual_vol_fd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:33.808416+00:00
-- url     : https://prove2.me/submissions/30557704-5e58-494a-8ba7-b616db53229d

import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_CovolumeDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped RealInnerProductSpace
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
namespace Formalism.H
theorem _root_.solution {ι : Type*} [Fintype ι] (o : OrthonormalBasis ι ℝ V) :
    volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
  rw [MeasureTheory.measureReal_def,
    MeasureTheory.measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    OrthonormalBasis.coe_toBasis, o.volume_parallelepiped, ENNReal.toReal_one]
end Formalism.H
