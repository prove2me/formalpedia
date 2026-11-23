-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx6.Nst_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:20.442623+00:00
-- url     : https://prove2.me/submissions/b93cfb67-0378-48c9-987a-5aee64d76e83

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionGivesUniformBoundsForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_psd_pull
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_sum_mul_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx6
namespace Formalism.FourierDecayAlt.P.Jx6
theorem _root_.solution {E W : Type} [Field E] (D : TB.Data E W) (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ}
    (hε : 0 < ε) (i s : ℕ) (w : W) (Y : Finset (TB.Pt E)) {κ : TB.Pt E → TB.Pt E → ℂ}
    (hκ : TB.PSDOn Y κ) (t : E) : 0 ≤ (D.Nst ε i s w Y κ t t).re := by
  classical
  unfold TB.Data.Nst
  rw [Complex.div_ofReal_re]
  refine div_nonneg (sum_mul_nonneg hκ ?_) (hW w).le
  have hm : ∀ x ∈ Y, TB.join x s t ∈ Y.image (fun h => TB.join h s t) :=
    fun x hx => Finset.mem_image_of_mem _ hx
  exact psd_pull (F := Y.image (fun h => TB.join h s t))
    (fun x : Y => ⟨TB.join x.1 s t, hm x.1 x.2⟩) (fun _ _ => rfl) (hG ε hε i w _)
end Formalism.FourierDecayAlt.P.Jx6
