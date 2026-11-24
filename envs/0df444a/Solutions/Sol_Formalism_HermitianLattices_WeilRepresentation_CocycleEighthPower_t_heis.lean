-- Prove2me | solution 1 for Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower.t_heis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:48.443689+00:00
-- url     : https://prove2.me/submissions/e3c66d24-9145-4771-b8ff-642fd0d8b42d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SignsFromTrianglesSquares
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareEqDiagOfQuadraticEven

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.WeilRepresentation Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
open Formalism.HermitianLattices.WeilRepresentation Formalism.HermitianLattices.IntegralLatticeDensity
namespace Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
theorem _root_.solution : HeisenbergCocycle := by
  intro V _ H hadd hherm F x y z
  have hadd2 : ∀ x y y', H x (y + y') = H x y + H x y' := by
    intro x y y'; rw [hherm (y+y') x, hadd, map_add, ← hherm, ← hherm]
  have hc : H y x = H x y - 2 * Complex.I * ((H x y).im : ℂ) := by
    rw [hherm x y]; apply Complex.ext <;> simp <;> ring
  unfold Heisenberg₂
  rw [add_assoc, mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [hadd, hadd2]
  rw [hc]
  ring
end Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
