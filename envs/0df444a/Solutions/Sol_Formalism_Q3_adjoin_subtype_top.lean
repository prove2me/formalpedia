-- Prove2me | solution 1 for Formalism.Q3.adjoin_subtype_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:11:19.336436+00:00
-- url     : https://prove2.me/submissions/82247c1a-134c-424d-881b-8c1c9040916e

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial
noncomputable section
namespace Formalism.Q3
section MQ
variable {k : ℕ} {E : Type} [Field E] [NumberField E] {a : Fin k → ℤ} {α : Fin k → E}
end MQ
section Exists
variable {k : ℕ} (a : Fin k → ℤ)
end Exists
private lemma adjoin_range_subtype_eq_whole_field {L : Type} [Field L] [Algebra ℚ L] (K : IntermediateField ℚ L)
    {k : ℕ} (β : Fin k → L) (hK : K = IntermediateField.adjoin ℚ (Set.range β)) (α' : Fin k → K)
    (hα : ∀ i, (α' i : L) = β i) :
    @IntermediateField.adjoin ℚ _ K _ K.algebra' (Set.range α') = ⊤ := by
  letI : Algebra ℚ K := K.algebra'
  have himg : K.val '' Set.range α' = Set.range β := by
    rw [← Set.range_comp]
    congr 1
    funext i
    exact hα i
  have hmap := IntermediateField.adjoin_map ℚ (Set.range α') K.val
  rw [himg, ← hK] at hmap
  rw [eq_top_iff]
  intro x _
  have hx : (x : L) ∈ (IntermediateField.adjoin ℚ (Set.range α')).map K.val := by
    rw [hmap]; exact x.2
  obtain ⟨y, hy, hyx⟩ := (IntermediateField.mem_map _).1 hx
  have hyx' : y = x := Subtype.ext hyx
  exact hyx' ▸ hy
end Formalism.Q3
end
end

set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution {L : Type} [Field L] [Algebra ℚ L] (K : IntermediateField ℚ L)
    {k : ℕ} (β : Fin k → L) (hK : K = IntermediateField.adjoin ℚ (Set.range β)) (α' : Fin k → K)
    (hα : ∀ i, (α' i : L) = β i) [inst : Algebra ℚ K] :
    IntermediateField.adjoin ℚ (Set.range α') = ⊤ := by
  obtain rfl : inst = K.algebra' := Subsingleton.elim _ _
  exact adjoin_range_subtype_eq_whole_field K β hK α' hα
end Formalism.Q3
