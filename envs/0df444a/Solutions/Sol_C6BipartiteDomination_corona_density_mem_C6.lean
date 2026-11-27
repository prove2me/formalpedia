-- Prove2me | solution 1 for C6BipartiteDomination.corona_density_mem_C6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:14:56.61421+00:00
-- url     : https://prove2.me/submissions/34fce14a-4878-44f7-a819-ca6da993b576

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
import Theorems.Thm_C6BipartiteDomination_corona_has_no_isolates
import Theorems.Thm_C6BipartiteDomination_corona_degree_at_most_six
import Theorems.Thm_C6BipartiteDomination_corona_vertex_card
import Theorems.Thm_C6BipartiteDomination_corona_gamma_eq_eight

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace C6BipartiteDomination
theorem _root_.solution :
    (8 : ℝ) / 15 ∈ C6DensitySet := by
  let H : FiniteSimpleGraphData :=
    ⟨CoronaVertex, inferInstance, inferInstance, coronaGraph⟩
  refine ⟨H, ?_, ?_⟩
  · refine ⟨corona_has_no_isolates, ?_, corona_degree_at_most_six⟩
    change 0 < Fintype.card CoronaVertex
    rw [corona_vertex_card]
    norm_num
  · simp [H, finiteGraphDensity, corona_gamma_eq_eight]
end C6BipartiteDomination
