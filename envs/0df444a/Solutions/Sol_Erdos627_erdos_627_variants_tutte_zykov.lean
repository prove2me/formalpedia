-- Prove2me | solution 1 for Erdos627.erdos_627.variants.tutte_zykov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:24:20.705319+00:00
-- url     : https://prove2.me/submissions/1f1e2523-a4e7-4bd1-a242-2e39f65d40a5

module
public import Definitions.Def_Erdos627
public import Definitions.Def_Erdos627Palomar_Solution
public import Theorems.Thm_SimpleGraph_exists_cliqueNum_eq_two_chromaticNumber_eq


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Erdos627
namespace Erdos627
namespace erdos_627.variants
theorem _root_.solution :
    ∀ k : ℕ, 2 ≤ k → ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.cliqueNum = 2 ∧ G.chromaticNumber = (k : ℕ∞) := by
  exact exists_cliqueNum_eq_two_chromaticNumber_eq
end erdos_627.variants
end Erdos627
