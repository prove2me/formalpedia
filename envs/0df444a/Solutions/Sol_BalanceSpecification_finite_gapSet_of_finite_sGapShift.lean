-- Prove2me | solution 1 for BalanceSpecification.finite_gapSet_of_finite_sGapShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:26.147643+00:00
-- url     : https://prove2.me/submissions/e7ed7e11-9231-4e39-a9c0-089eca3d648e

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
public import Theorems.Thm_BalanceSpecification_sGapPeriodic_injective
public import Theorems.Thm_BalanceSpecification_sGapPeriodic_mem

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace Bool] {S : Set ℕ}
    (hX : (sGapShift S).carrier.Finite) : S.Finite := by
  have himage : (sGapPeriodic '' S).Finite := hX.subset (by
    rintro _ ⟨s, hs, rfl⟩
    exact sGapPeriodic_mem hs)
  exact himage.of_finite_image sGapPeriodic_injective.injOn
end BalanceSpecification
