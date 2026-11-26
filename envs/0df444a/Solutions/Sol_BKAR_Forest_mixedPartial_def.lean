-- Prove2me | solution 1 for BKAR.Forest.mixedPartial_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:20:11.449534+00:00
-- url     : https://prove2.me/submissions/417b823e-b4f3-4be7-986b-bda783d4a90f

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (F : Forest V)
namespace BKAR.Forest
theorem _root_.solution (ρ : (Edge V → ℝ) → ℝ) :
    F.mixedPartial ρ = mixedPartialList F.edges.toList ρ :=
  rfl
end BKAR.Forest
