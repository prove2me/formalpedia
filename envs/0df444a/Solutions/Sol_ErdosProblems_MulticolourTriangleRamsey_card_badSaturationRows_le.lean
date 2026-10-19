-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.card_badSaturationRows_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/6ecf15f9-6e94-4f09-8bb4-71e5f6f074b5

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_mem_missingSymbolRows
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_card_missingSymbolRows

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H m : ℕ)
    (T : Finset (Fin m → Fin H)) :
    (badSaturationRows H m T).card ≤
      H * ((H - 1) ^ T.card * H ^ (H ^ m - T.card)) := by
  classical
  have hsubset : badSaturationRows H m T ⊆
      (Finset.univ : Finset (Fin H)).biUnion
        (fun symbol => missingSymbolRows H m T symbol) := by
    intro row hrow
    have hbad : ¬ RowCovers T row := by
      simpa [badSaturationRows] using hrow
    unfold RowCovers at hbad
    push Not at hbad
    obtain ⟨symbol, hsymbol⟩ := hbad
    exact Finset.mem_biUnion.mpr
      ⟨symbol, Finset.mem_univ symbol,
        (mem_missingSymbolRows H m T symbol row).mpr hsymbol⟩
  calc
    (badSaturationRows H m T).card ≤
        ((Finset.univ : Finset (Fin H)).biUnion
          (fun symbol => missingSymbolRows H m T symbol)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ symbol : Fin H, (missingSymbolRows H m T symbol).card :=
      Finset.card_biUnion_le
    _ = H * ((H - 1) ^ T.card * H ^ (H ^ m - T.card)) := by
      simp [card_missingSymbolRows]
end ErdosProblems.MulticolourTriangleRamsey
