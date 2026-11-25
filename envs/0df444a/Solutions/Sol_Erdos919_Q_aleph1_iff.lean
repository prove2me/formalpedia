-- Prove2me | solution 1 for Erdos919.Q_aleph1_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:41:31.513303+00:00
-- url     : https://prove2.me/submissions/4e27235e-7813-4794-984b-06440e1fd6af

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_chromaticCardinal_eq_aleph1_iff
public import Theorems.Thm_Erdos919_Q_iff

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution :
    Q.{u} ℵ₁ ↔ ∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ ChiAleph1 G := by
  rw [Q_iff]
  refine exists_congr fun G => ?_
  rw [chromaticCardinal_eq_aleph1_iff G]
end Erdos919
