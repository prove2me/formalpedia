-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.red_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:26:55.533704+00:00
-- url     : https://prove2.me/submissions/a2ba1a11-62f2-4f6e-a640-6e8e97ed468d

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_coe_phi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.S3x2.coe_phi

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable (o : Type) [CommRing o] [IsLocalRing o]
local notation "𝔽" => IsLocalRing.ResidueField o
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution (ι : Type) [Fintype ι] [DecidableEq ι] : Function.Surjective (red o ι) := by
  intro g
  let y : Matrix ι ι o := Matrix.of fun i j =>
    Function.surjInv IsLocalRing.residue_surjective ((g : Matrix ι ι 𝔽) i j)
  have hy : y.map (IsLocalRing.residue o) = (g : Matrix ι ι 𝔽) := by
    ext i j
    simp [y, Function.surjInv_eq]
  have hdet : IsUnit y.det := by
    have h1 : IsLocalRing.residue o y.det = (g : Matrix ι ι 𝔽).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hy]
    have h2 : IsUnit (IsLocalRing.residue o y.det) := by
      rw [h1]; exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    exact isUnit_of_map_unit (IsLocalRing.residue o) _ h2
  exact ⟨toGL y hdet, Units.ext hy⟩
end Formalism.FourierDecayAlt.P.S3x2
