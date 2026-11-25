-- Prove2me | solution 1 for ErdosGirthChromatic.exists_girth_chromaticNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:41:47.012433+00:00
-- url     : https://prove2.me/submissions/fc62e751-acd0-47cf-a83c-a288c4f8c9bf

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirth
public import Definitions.Def_Mycielski_Family
public import Definitions.Def_FractionalLib_LarsenProppUllman
public import Definitions.Def_ErdosGirthChromatic_Solution
public import Theorems.Thm_ErdosGirth_exists_girth_chromaticNumber


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirthChromatic
namespace ErdosGirthChromatic
theorem _root_.solution (g k : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), (g : ℕ∞) < G.egirth ∧ (k : ℕ∞) < G.chromaticNumber :=
  ErdosGirth.exists_girth_chromaticNumber g k
end ErdosGirthChromatic
