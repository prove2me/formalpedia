-- Prove2me | solution 1 for Erdos919.Q_aleph2_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:41:32.072877+00:00
-- url     : https://prove2.me/submissions/f473e45f-8717-4391-af0d-bd8e2ccd7237

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_mk_lex
public import Theorems.Thm_Erdos919_chromaticCardinal_eq_aleph2_iff
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
    Q.{u} (ℵ_ 2) ↔ ∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ ChiAleph2 G := by
  rw [Q_iff]
  refine exists_congr fun G => ?_
  rw [chromaticCardinal_eq_aleph2_iff G mk_lex]
end Erdos919
