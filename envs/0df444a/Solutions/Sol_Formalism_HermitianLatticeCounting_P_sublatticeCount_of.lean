-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.sublatticeCount_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:36.976398+00:00
-- url     : https://prove2.me/submissions/e4266579-026e-4480-a533-d362350276b7

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hS : Formalism.SLP.SubmoduleIndexCountO) (hC : Formalism.HermitianLatticeCounting.S6.CfBound) :
    Formalism.HermitianLatticeCounting.S6.SublatticeCount := by
  intro E _ _ M _ _ _ _ f x hE hx
  obtain ⟨h1, h2⟩ := hS E M x hx
  refine ⟨h1, ?_⟩
  have hf : 1 ≤ f := by
    have : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  rw [hE] at h2
  have h3 : (({N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = x}.ncard : ℕ) : ℝ) ≤
      ((2 * f : ℕ) : ℝ) ^ (Nat.primeFactorsList x).length *
        (x : ℝ) ^ Module.finrank (NumberField.RingOfIntegers E) M := by exact_mod_cast h2
  exact le_trans h3 (hC f x _ hf hx)
end Formalism.HermitianLatticeCounting.P
