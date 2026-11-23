-- Prove2me | solution 1 for Formalism.NG.BlockDetAlt.isUnit_det_of_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:43.101797+00:00
-- url     : https://prove2.me/submissions/f8a5f355-c3b1-46e1-a5f9-a95eb0b05f1f

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.BlockDetAlt
variable {O : Type*} [CommRing O] {X' : Type*}
variable {d : Type} [Fintype d] [DecidableEq d]
variable {d : Type} [Fintype d] [DecidableEq d]
namespace Formalism.NG.BlockDetAlt
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (PowerSeries (X' → FractionRing O)))
    (hA : (PowerSeries.constantCoeff).mapMatrix A = 1) : IsUnit A.det := by
  rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, hA, Matrix.det_one]
  exact isUnit_one
end Formalism.NG.BlockDetAlt
