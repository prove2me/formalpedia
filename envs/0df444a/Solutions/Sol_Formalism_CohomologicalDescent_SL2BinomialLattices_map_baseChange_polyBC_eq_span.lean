-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.map_baseChange_polyBC_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:37.445839+00:00
-- url     : https://prove2.me/submissions/8b6fba3f-dc02-4748-a92d-e008de4120fe

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_polyBC_tmul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial CategoryTheory TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.SL2BinomialLattices
open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA
universe u v u' v'
namespace Formalism.CohomologicalDescent.SL2BinomialLattices
theorem _root_.solution (R O : Type) [CommRing R] [CommRing O] [Algebra R O] (r n : ℕ)
    (q : Submodule R (MvPolynomial (Fin r × Fin n) R)) :
    (q.baseChange O).map (polyBC R O r n).toLinearMap =
      Submodule.span O (map (algebraMap R O) '' (q : Set (MvPolynomial (Fin r × Fin n) R))) := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨f, hf, ?_⟩
    have h := polyBC_tmul R O r n 1 f
    rw [one_smul] at h
    exact h.symm
  · rintro ⟨f, hf, rfl⟩
    refine ⟨_, ⟨f, hf, rfl⟩, ?_⟩
    have h := polyBC_tmul R O r n 1 f
    rw [one_smul] at h
    exact h
end Formalism.CohomologicalDescent.SL2BinomialLattices
