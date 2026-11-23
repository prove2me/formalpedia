-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Test.herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:20.876137+00:00
-- url     : https://prove2.me/submissions/97964f64-71e0-4a29-957f-fc9d069c6fff

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PUnitBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {c : K →+* K} {h : V → V → K} {O : Subring K} {L : AddSubgroup V} {p : ℕ}
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Test
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Test
theorem _root_.solution : Herm4 (RingHom.id ℚ) (fun x y : ℚ => x * y) where
  add_left x x' y := add_mul x x' y
  smul_left k x y := by simp [mul_assoc]
  symm x y := mul_comm y x
  pos x hx := ⟨mul_self_ne_zero.2 hx, x, 0, 0, 0, rfl, rfl, rfl, rfl, by ring⟩
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Test
