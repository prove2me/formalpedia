-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FlagGramRestriction.flag_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:51:08.496483+00:00
-- url     : https://prove2.me/submissions/2c707b09-e978-455e-99c1-b54d0a3e20b9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagGramRestriction
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FlagGramRestriction
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hu : u ∈ C2.UTset (r + 1))
    (b : Fin (r + 1)) : (∑ c, u c b • fvec k r z c) - fvec k r z b ∈ C2.flagSpan k r z b := by
  have e : (∑ c, u c b • fvec k r z c) - fvec k r z b =
      ∑ c, (u c b - if c = b then 1 else 0) • fvec k r z c := by
    simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [e]
  apply Submodule.sum_mem
  intro c _
  by_cases hcb : c < b
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨c, hcb⟩, rfl⟩
  · have h0 : u c b - (if c = b then 1 else 0) = 0 := by
      rcases lt_or_eq_of_le (not_lt.mp hcb) with h | h
      · rw [hu.1 c b h, if_neg (ne_of_gt h), sub_self]
      · subst h; rw [hu.2, if_pos rfl, sub_self]
    rw [h0, zero_smul]; exact Submodule.zero_mem _
end Formalism.FourierDecayAlt.P.FlagGramRestriction
