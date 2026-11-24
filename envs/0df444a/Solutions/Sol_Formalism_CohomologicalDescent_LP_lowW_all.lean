-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LP.lowW_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:07:13.492568+00:00
-- url     : https://prove2.me/submissions/05f09168-271d-43fb-9101-baaeea6982bb

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLP
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_GeneratedHighestWeightHolds
import Theorems.Thm_Formalism_CohomologicalDescent_LP_lowSpan_low

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LP
open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample
variable {K N : Type*} [CommRing K] [AddCommGroup N] [Module K N] {q : ℕ}
namespace Formalism.CohomologicalDescent.LP
theorem _root_.solution (T : Fin q → Fin q → Module.End K N) (hT : GlRel T) (κ : Fin q → K) (x : N) (hx : LowW T κ x) :
    ∀ a b, T a b x ∈ lowSpan T κ := by
  induction hx with
  | base v hv =>
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · rw [hv.1 a b h]; exact Submodule.zero_mem _
    · subst h
      rw [hv.2 a]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (LowW.base v hv))
    · exact Submodule.subset_span (LowW.step a b v h (LowW.base v hv))
  | step c d x hdc _ ih =>
    intro a b
    have h := LinearMap.congr_fun (hT a b c d) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    have e : T a b (T c d x) = T c d (T a b x) +
        (((if b = c then T a d else 0 : Module.End K N) x) - ((if d = a then T c b else 0 : Module.End K N) x)) := by
      rw [← h]; abel
    rw [e]
    refine Submodule.add_mem _ (lowSpan_low T κ c d hdc _ (ih a b)) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs
      · exact ih a d
      · simp
    · split_ifs
      · exact ih c b
      · simp
end Formalism.CohomologicalDescent.LP
