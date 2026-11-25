-- Prove2me | solution 1 for ErdosGirthChromatic.exists_girth_not_colorable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:40:55.554402+00:00
-- url     : https://prove2.me/submissions/8eb20d7a-46a3-488f-8d64-90fba1b50208

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirth
public import Definitions.Def_Mycielski_Family
public import Definitions.Def_FractionalLib_LarsenProppUllman
public import Definitions.Def_ErdosGirthChromatic_Solution
public import Theorems.Thm_ErdosGirth_exists_girth_not_colorable


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirthChromatic
namespace ErdosGirthChromatic
theorem _root_.solution (g k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n), (g : ℕ∞) < G.egirth ∧ ¬ G.Colorable k :=
  ErdosGirth.exists_girth_not_colorable g k
end ErdosGirthChromatic
