-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TA1.sum_PT_ls
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:38.999993+00:00
-- url     : https://prove2.me/submissions/e7bcf194-858c-4b28-ad1a-d45f085182c1

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagonalTopBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TA1_filter_PT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA1
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {E : Type} [DecidableEq E]
namespace Formalism.FourierDecayAlt.P.TA1
theorem _root_.solution {M : Type} [AddCommMonoid M] (Sg : ℕ → ℕ → Finset E) (i s : ℕ) (hs : 1 ≤ s)
    (hsi : s ≤ i) (F : Pt E → M) :
    ∑ p ∈ PT Sg i, (if ls p = s then F p else 0) =
      ∑ t ∈ Sg i s, ∑ h ∈ PT Sg (i - s), F (Formalism.FourierDecayAlt.TA.ext h s t) := by
  rw [← sum_filter, filter_PT Sg i s hs hsi, sum_image, sum_product_right]
  rintro ⟨h, t⟩ _ ⟨h', t'⟩ _ hxy
  simp only [Formalism.FourierDecayAlt.TA.ext] at hxy
  have := List.append_inj' hxy rfl
  simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at this
  exact Prod.ext this.1 this.2
end Formalism.FourierDecayAlt.P.TA1
