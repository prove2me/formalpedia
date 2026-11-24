-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x4.cut_preserves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:15:41.516951+00:00
-- url     : https://prove2.me/submissions/0011671c-b26a-4f00-82a9-bd9f6ca7a5a5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x4
variable {m : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x4
theorem _root_.solution (w : Equiv.Perm (Fin m)) (c : Fin m) (hc : IsCut w c) (x : Fin m) :
    x ≤ c ↔ w x ≤ c := by
  set S := Finset.univ.filter (fun x : Fin m => x ≤ c) with hS
  set T := Finset.univ.filter (fun x : Fin m => w x ≤ c) with hT
  have hTS : T = S.map w.symm.toEmbedding := by
    ext x; simp only [hS, hT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.coe_toEmbedding]
    constructor
    · intro h; exact ⟨w x, h, by simp⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  have hcard : T.card = S.card := by rw [hTS, Finset.card_map]
  have hsub : S ⊆ T := by
    intro x hx
    by_contra hxT
    have hTnot : ¬ T ⊆ S := by
      intro hTS'
      have := Finset.eq_of_subset_of_card_le hTS' (le_of_eq hcard.symm)
      rw [this] at hxT; exact hxT hx
    obtain ⟨y, hyT, hyS⟩ := Finset.not_subset.mp hTnot
    simp only [hS, hT, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hx hxT hyT hyS
    have := hc x y hx hyS
    exact absurd (lt_of_le_of_lt hyT hxT) (not_lt.mpr (le_of_lt this))
  have hEq : S = T := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard)
  have := congrArg (fun F => x ∈ F) hEq
  simpa [hS, hT] using this
end Formalism.FourierDecayAlt.P.C2x4
