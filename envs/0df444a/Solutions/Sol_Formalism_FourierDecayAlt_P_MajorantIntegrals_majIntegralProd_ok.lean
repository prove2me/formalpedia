-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MajorantIntegrals.majIntegralProd_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:24.943103+00:00
-- url     : https://prove2.me/submissions/9a868a0d-547f-473c-88f4-b1f0fe5f7f87

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Theorems.Thm_Formalism_FourierDecayAlt_P_MajorantIntegrals_majIntegral_ok

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MajorantIntegrals
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.MajorantIntegrals
theorem _root_.solution : MajIntegralProd := by
  intro f K x hK hx
  have h1 := fun v => (majIntegral_ok K (x v) hK (hx v))
  refine ⟨Integrable.fintype_prod (f := fun v (l : ℂ) => mfac K (x v) ‖l‖)
    (μ := fun _ => volume) (fun v => (h1 v).1), ?_⟩
  have h2 := integral_fintype_prod_volume_eq_prod (ι := Fin f) (E := fun _ => ℂ)
    (fun v (l : ℂ) => mfac K (x v) ‖l‖)
  exact h2.trans (Finset.prod_congr rfl (fun v _ => (h1 v).2))
end Formalism.FourierDecayAlt.P.MajorantIntegrals
