-- Prove2me | solution 1 for BSLambda.LLL.card_le_three_of_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:42.724857+00:00
-- url     : https://prove2.me/submissions/c49dfdab-196e-4803-a3cf-0387ed90ddd4

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_not_close_five
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
        j ≠ h ∧ (cert Arc (toGamma ω) j).dist x = 1).card ≤ 3 :=
  card_filter_le_of_no_support fun _ hS hh hclose ↦
    not_close_five hT hgood hS hh hx fun i hi hih ↦ (hclose i hi hih).le
end BSLambda.LLL
