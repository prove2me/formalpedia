-- Prove2me | solution 1 for Formalism.HC.Landau.eq_one_of_chi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:55.673712+00:00
-- url     : https://prove2.me/submissions/bece3be4-8b0c-4851-9288-9e82da5235bd

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism Formalism.HC Formalism.HC.Landau
open Formalism ArithmeticFunction
namespace Formalism.HC.Landau
theorem _root_.solution {ψ : PChar} (h : ψ.χ = 1) : ψ = PChar.one := by
  obtain ⟨N, χ, hp⟩ := ψ
  have h' : χ = 1 := h
  subst h'
  have e : N = 1 := hp.symm.trans DirichletCharacter.conductor_one
  subst e
  rfl
end Formalism.HC.Landau
