-- Prove2me | solution 1 for BSLambda.LLL.card_le_seven_of_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:08.563681+00:00
-- url     : https://prove2.me/submissions/7d0116bd-ce02-44ab-b680-8573db49c229

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_not_close_nine
public import Theorems.Thm_BSLambda_LLL_card_filter_le_of_no_support

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution (hT : IsTournament Arc) {ω : GateCfg ι r}
    (hgood : ∀ i : BadIdx Arc, ω ∉ badEvent Arc i) (h : ι)
    (x : Input (Coord ι r)) (hx : (cert Arc (toGamma ω) h).Sat x) :
    (Finset.univ.filter fun j =>
        j ≠ h ∧ (cert Arc (toGamma ω) j).dist x ≤ 2).card ≤ 7 :=
  card_filter_le_of_no_support fun _ hS hh hclose ↦ not_close_nine hT hgood hS hh hx hclose
end BSLambda.LLL
