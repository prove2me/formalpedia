-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_mp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:51.106628+00:00
-- url     : https://prove2.me/submissions/5e8a16fd-0e3f-463a-9dd5-5f9f08b63e87

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_measurePreserving_pi_comp_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (d r : ℕ)
    (Φ : EuclideanSpace ℂ (Fin (d + 1)) ≃ₗᵢ[ℂ] WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d))) :
    MeasurePreserving (fun a : Fin r → EuclideanSpace ℂ (Fin (d + 1)) =>
      ((fun b => (Φ (a b)).ofLp.1), (fun b => (Φ (a b)).ofLp.2))) volume volume := by
  have h0 : MeasurePreserving
      (Φ : EuclideanSpace ℂ (Fin (d + 1)) → WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d))) :=
    LinearIsometryEquiv.measurePreserving
      ({ (Φ.toLinearEquiv.restrictScalars ℝ) with norm_map' := Φ.norm_map } :
        EuclideanSpace ℂ (Fin (d + 1)) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d)))
  exact measurePreserving_pi_comp_prod r _ _ h0 (WithLp.volume_preserving_ofLp ℂ (EuclideanSpace ℂ (Fin d)))
end Formalism.HermitianLatticeCounting.P
