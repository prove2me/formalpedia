-- Prove2me | solution 1 for BSLambda.LLL.dist_cert_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:27:38.429473+00:00
-- url     : https://prove2.me/submissions/8255a3e4-fabc-4f18-9b72-f19002f6674a

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_violSet_cert_eq
public import Theorems.Thm_BSLambda_LLL_disjoint_zeros_image_gate_image
public import Theorems.Thm_BSLambda_Construction_gateCoord_injective
public import Theorems.Thm_BSLambda_PartialAssign_dist_eq_card_violSet


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
namespace BSLambda.LLL
theorem _root_.solution (Arc : ι → ι → Bool) (hT : IsTournament Arc)
    (γ : ι → ι → Fin r) (i : ι) (x : Input (Construction.Coord ι r)) :
    (Construction.cert Arc γ i).dist x =
      (zeroSet x i).card + (missSet Arc γ (zeroSet x) Finset.univ i).card := by
  rw [PartialAssign.dist_eq_card_violSet, violSet_cert_eq Arc hT γ i x,
    Finset.card_union_of_disjoint (disjoint_zeros_image_gate_image Arc hT γ i x),
    Finset.card_image_of_injective _ (Prod.mk_right_injective i),
    Finset.card_image_of_injective _ (Construction.gateCoord_injective γ i)]
end BSLambda.LLL
