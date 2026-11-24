-- Prove2me | solution 1 for BalanceSpecification.fiveSymbol_mixing_biBalanced_not_synchronized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:58:29.476447+00:00
-- url     : https://prove2.me/submissions/a289688c-1c20-4c2e-bd06-5b61602aaf79

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Definitions.Def_BalanceSpecificaton_TopologicalMixing
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Definitions.Def_BalanceSpecificaton_Examples
public import Theorems.Thm_BalanceSpecification_FiveSymbol_biBalanced
public import Theorems.Thm_BalanceSpecification_FiveSymbol_irreducible
public import Theorems.Thm_BalanceSpecification_FiveSymbol_not_synchronized
public import Theorems.Thm_BalanceSpecification_FiveSymbol_topologicallyMixing
public import Theorems.Thm_BalanceSpecification_OneSidedExample_irreducible


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution :
    Irreducible FiveSymbol.shift ∧ TopologicallyMixing FiveSymbol.shift ∧
      BiBalanced (language FiveSymbol.shift) ∧ ¬Synchronized FiveSymbol.shift :=
  ⟨FiveSymbol.irreducible, FiveSymbol.topologicallyMixing,
    FiveSymbol.biBalanced, FiveSymbol.not_synchronized⟩
end BalanceSpecification
