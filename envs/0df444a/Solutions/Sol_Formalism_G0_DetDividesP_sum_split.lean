-- Prove2me | solution 1 for Formalism.G0.DetDividesP.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:25.399805+00:00
-- url     : https://prove2.me/submissions/b6a67c2e-dc85-44b8-921f-302b41ddba67

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι) (d : ι → ℕ)
    (hAS : ∀ l, A l ∈ S ∧ vec (A l) = true) :
    (∑ i ∈ S.filter (fun i => i ∉ Set.range A), d i) =
      (∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) +
        ∑ i ∈ S.filter (fun i => vec i = false), d i := by
  rw [← Finset.sum_filter_add_sum_filter_not (S.filter (fun i => i ∉ Set.range A)) (fun i => vec i = true)]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i; simp [Finset.mem_filter]; tauto
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp only [Finset.mem_filter, Bool.not_eq_true]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rintro ⟨l, rfl⟩
      have := (hAS l).2; simp_all
end Formalism.G0.DetDividesP
