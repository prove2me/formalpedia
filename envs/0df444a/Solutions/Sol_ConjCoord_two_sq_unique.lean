-- Prove2me | solution 1 for ConjCoord.two_sq_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:57:02.835137+00:00
-- url     : https://prove2.me/submissions/6eccef34-2d92-449f-96ea-7edccadf3fa1

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_two_sq_unique


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution {p : ℤ} (hp : Prime p) (hodd : p % 2 = 1) {α β γ δ : ℤ} (hα : 0 < α)
    (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ) (h1 : α ^ 2 + β ^ 2 = p) (h2 : γ ^ 2 + δ ^ 2 = p)
    (hβe : Even β) (hδe : Even δ) : α = γ ∧ β = δ :=
  Proof.two_sq_unique hp hodd hα hβ hγ hδ h1 h2 hβe hδe
end ConjCoord
