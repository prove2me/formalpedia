-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.split_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:50.517883+00:00
-- url     : https://prove2.me/submissions/ab66b5ee-fe92-4109-a8fa-4dba155bc448

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Polynomial Finset Formalism.GM.M
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (p : ℕ) [Fact p.Prime] {n : ℕ} (Aq : Matrix (Fin n) (Fin n) ℚ_[p][X]) :
    (Aq.map (Polynomial.map (algebraMap ℚ_[p] (PadicAlgCl p)))).det =
      (Aq.det).map (algebraMap ℚ_[p] (PadicAlgCl p)) := by
  have h := RingHom.map_det (Polynomial.mapRingHom (algebraMap ℚ_[p] (PadicAlgCl p))) Aq
  simpa using h.symm
end Formalism.GM.MeanGammaLemmas
