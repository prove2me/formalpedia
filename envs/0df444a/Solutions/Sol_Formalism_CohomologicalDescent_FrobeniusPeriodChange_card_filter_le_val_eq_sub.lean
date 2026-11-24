-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.card_filter_le_val_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:55:18.760386+00:00
-- url     : https://prove2.me/submissions/e30aab09-f5a9-47a1-aad2-911f48c9fd15

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution (N m : ℕ) (hm : m ≤ N) :
    (Finset.univ.filter fun a : Fin N => m ≤ (a : ℕ)).card = N - m := by
  have hm2 : (Finset.univ.filter fun a : Fin N => m ≤ (a : ℕ)).map Fin.valEmbedding =
      Finset.Ico m N := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨a, h1, rfl⟩
      exact ⟨h1, a.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hm2, Nat.card_Ico]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
