-- Prove2me | solution 1 for C6BipartiteDomination.finite_graph_density_le_eight_fifteenths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:17:23.7118+00:00
-- url     : https://prove2.me/submissions/d7e02f27-b796-4891-9345-85cbdb4654a4

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
import Theorems.Thm_C6BipartiteDomination_main_upper_bound_gamma

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace C6BipartiteDomination
theorem _root_.solution {H : FiniteSimpleGraphData}
    (hH : C6Admissible H) : finiteGraphDensity H ≤ (8 : ℝ) / 15 := by
  letI : Fintype H.Vertex := H.finiteVertex
  letI : DecidableEq H.Vertex := H.decidableVertex
  obtain ⟨hNoIso, hcardPos, hmax⟩ := hH
  have hmain := main_upper_bound_gamma H.graph hNoIso hmax
  have hpos : 0 < (Fintype.card H.Vertex : ℝ) := by exact_mod_cast hcardPos
  have hmainR :
      (15 : ℝ) * (gammaBip H.graph : ℝ) ≤
        (8 : ℝ) * (Fintype.card H.Vertex : ℝ) := by
    exact_mod_cast hmain
  unfold finiteGraphDensity
  rw [div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 15)]
  nlinarith
end C6BipartiteDomination
