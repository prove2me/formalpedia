-- Prove2me | solution 1 for Garrido.exists_injective_freeGroup_specialOrthogonalGroup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T14:12:44.724047+00:00
-- url     : https://prove2.me/submissions/f1f4f886-513a-414e-b409-ddf44a358dbc

import Mathlib
import Theorems.Thm_Garrido_injective_lift_rho_sigma
import Definitions.Def_Garrido_BanachTarski
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Chou_Classes

universe u

namespace Garrido.BT

open scoped ENNReal Pointwise
open Set

/-! ### Reduced words -/

section Words

variable {α : Type*} [DecidableEq α]
set_option linter.unusedSectionVars false

end Words

/-! ### Equidecomposition lemmas (copied from proofs/EQ_Sec1.lean) -/

/-! ### The paradox from an equivariant map to `F₂` -/

/-! ### Amenable groups have no free subgroup of rank two -/

end Garrido.BT


namespace Garrido.BT

open Matrix
theorem injective_lift_rho_sigma' :
    Function.Injective (FreeGroup.lift ![rho, sigma]) :=
  Garrido.injective_lift_rho_sigma
theorem exists_injective_freeGroup_specialOrthogonalGroup' :
    ∃ f : FreeGroup (Fin 2) →* Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      Function.Injective f :=
  ⟨_, injective_lift_rho_sigma'⟩

end Garrido.BT


namespace Garrido.BT

open Matrix

/-! ### Transfer of equidecompositions from an invariant subtype -/

section Transfer

open Set

variable {G H Y : Type*} [Group G] [MulAction G Y] [Group H]

end Transfer

/-! ### The sphere is uncountable -/

/-! ### Theorem 1.7 (Hausdorff) -/

end Garrido.BT


namespace Garrido.BT

open scoped Pointwise
open Real Matrix

/-! ## Part 2: absorbing a set with disjoint orbit translates -/

/-! ## Part 1: rotations -/

end Garrido.BT


namespace Garrido.BT

open scoped Pointwise
open Set

end Garrido.BT

namespace Garrido.BT

open Matrix

end Garrido.BT

namespace Garrido.BT

open Matrix Set
open scoped ENNReal Pointwise

end Garrido.BT


/-! Garrido, Corollary 1.10 (Banach–Tarski for balls and for ℝ³) and the p. 1 consequence. -/

namespace Garrido.BT
open scoped ENNReal Pointwise
open Set Matrix

/-! ## The radial projection -/

/-! ## Absorbing the centre -/

/-! ## The targets -/

end Garrido.BT


/-! ## Composition: every milestone, with no hypotheses -/

namespace Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem injective_lift_rho_sigma : Function.Injective (FreeGroup.lift ![rho, sigma]) :=
  Garrido.injective_lift_rho_sigma

theorem exists_injective_freeGroup_specialOrthogonalGroup :
    ∃ f : FreeGroup (Fin 2) →* Matrix.specialOrthogonalGroup (Fin 3) ℝ, Function.Injective f :=
  Garrido.BT.exists_injective_freeGroup_specialOrthogonalGroup'

end Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem solution :
    ∃ f : FreeGroup (Fin 2) →* Matrix.specialOrthogonalGroup (Fin 3) ℝ, Function.Injective f :=
  Garrido.BT.Final.exists_injective_freeGroup_specialOrthogonalGroup
