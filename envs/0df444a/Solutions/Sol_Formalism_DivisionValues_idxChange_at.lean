-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:14:49.795082+00:00
-- url     : https://prove2.me/submissions/2ba9fca5-720e-489a-b6b2-b47fecb3c6ee

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_lidx_congr
import Theorems.Thm_Formalism_DivisionValues_indexChange_of_det_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
open NumberField
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues
theorem _root_.solution {d : ℕ} (v : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) (Fin d → K))
    (e : Fin d → Fin d → K) (he : LinearIndependent K e) (γ : Matrix (Fin d) (Fin d) K)
    (hγ : γ.det ≠ 0)
    (hloc : localization₂ v.asIdeal (Submodule.span (𝓞 K) (Set.range (idxChangeAct e γ))) =
      localization₂ v.asIdeal L) :
    idx v (Submodule.span (𝓞 K) (Set.range e)) L = vw v γ.det := by
  unfold idx vw
  rw [← idxChange_lidx_congr v.asIdeal rfl hloc]
  exact indexChange_of_det_ne_zero v γ hγ e he
end Formalism.DivisionValues
