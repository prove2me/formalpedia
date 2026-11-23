-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.disj_phi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:11.47749+00:00
-- url     : https://prove2.me/submissions/896aeab1-0269-47f4-bb73-0fb1ad7ed08c

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_hEmb_apply
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
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution (V : Subgroup (GL (Fin k) A)) : Disjoint (UcG A (cI r k)) (V.map (phi A r k)) := by
  rw [Subgroup.disjoint_def]
  rintro _ hx ⟨h, -, rfl⟩
  have h1 : h = 1 := by
    apply Units.ext
    ext a b
    have := hx (Sum.inr (Sum.inl (Sum.inl a))) (Sum.inr (Sum.inl (Sum.inl b))) le_rfl
    rw [coe_phi, hEmb_apply] at this
    simpa [Matrix.one_apply] using this
  rw [h1, map_one]
end Formalism.FourierDecayAlt.P.S3x2
