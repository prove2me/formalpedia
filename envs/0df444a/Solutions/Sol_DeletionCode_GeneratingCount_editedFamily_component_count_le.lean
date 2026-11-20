-- Prove2me | solution 1 for DeletionCode.GeneratingCount.editedFamily_component_count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:07:42.230988+00:00
-- url     : https://prove2.me/submissions/4dd57f35-00a3-4503-951d-d7d3703841d8

import Definitions.Def_DeletionCode_RecordSerialization
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_DeletionCode_GeneratingCount

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingCount
open Windows HeaderRecovery GeneratingModel GeneratingRecovery RecordSerialization DescriptionCount
namespace DeletionCode.GeneratingCount
theorem _root_.solution {ν k : ℕ} (E : EditedFamily (Fin ν) k) :
    Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) ≤ ν := by
  classical
  rw [← Fintype.card_congr (componentGraphEquiv E)]
  let : Fintype (GeneratingModel.Components E) := componentsFintype E
  let f : Fin ν → GeneratingModel.Components E :=
    Quotient.mk (GeneratingModel.componentSetoid E.family (windowLength k))
  have hsurj : Function.Surjective f := by
    intro C
    induction C using Quotient.inductionOn with
    | _ b => exact ⟨b, rfl⟩
  have hcard := Fintype.card_le_of_surjective f hsurj
  simpa only [Fintype.card_fin] using hcard
end DeletionCode.GeneratingCount
