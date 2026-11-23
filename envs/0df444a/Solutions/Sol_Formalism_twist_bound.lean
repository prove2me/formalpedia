-- Prove2me | solution 1 for Formalism.twist_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:55.537548+00:00
-- url     : https://prove2.me/submissions/f7514504-6482-4ea8-bbcf-30aa82415fa9

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi

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
open Formalism
open ArithmeticFunction
namespace Formalism
theorem _root_.solution {N : ℕ} (χ : DirichletCharacter ℂ N) :
    ∀ n : ℕ, |Λ n * (χ n).re| ≤ 1 * Λ n := fun n => by
  rw [one_mul, abs_mul, abs_of_nonneg vonMangoldt_nonneg]
  have h1 : |(χ n).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ _)
  exact mul_le_of_le_one_right vonMangoldt_nonneg h1
end Formalism
