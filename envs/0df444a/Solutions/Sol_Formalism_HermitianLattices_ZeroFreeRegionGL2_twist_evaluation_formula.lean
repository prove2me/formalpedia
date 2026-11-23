-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.twist_evaluation_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:56.155177+00:00
-- url     : https://prove2.me/submissions/5111b9e3-b14c-4a00-9f08-65b5a66f3f71

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : TwEval := by
  intro t θ q _ n
  by_cases hu : IsUnit (n : ZMod (t * q))
  · unfold tw
    rw [MulChar.mul_apply]
    obtain ⟨u, hu'⟩ := hu
    rw [← hu', DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu']
    have h1 : (ZMod.cast ((n : ZMod (t * q))) : ZMod t) = (n : ZMod t) := by
      have : (ZMod.castHom (Dvd.intro q rfl : t ∣ t * q) (ZMod t)) (n : ZMod (t*q)) = (n : ZMod t) := map_natCast _ n
      simpa using this
    have h2 : (ZMod.cast ((n : ZMod (t * q))) : ZMod q) = (n : ZMod q) := by
      have : (ZMod.castHom (Dvd.intro_left t rfl : q ∣ t * q) (ZMod q)) (n : ZMod (t*q)) = (n : ZMod q) := map_natCast _ n
      simpa using this
    rw [h1, h2]
    congr 1
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    simp [qc, legendreSym]
  · rw [MulChar.map_nonunit _ hu]
    have hc : ¬ n.Coprime (t * q) := fun h => hu ((ZMod.isUnit_iff_coprime n _).2 h)
    by_cases h1 : n.Coprime t
    · have h2 : ¬ n.Coprime q := fun h => hc (Nat.Coprime.mul_right h1 h)
      have : jacobiSym (n : ℤ) q = 0 := by
        have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
        rw [jacobiSym.eq_zero_iff_not_coprime]
        simpa [Int.gcd_natCast_natCast] using h2
      simp [this]
    · have : θ (n : ZMod t) = 0 := MulChar.map_nonunit _ (fun h => h1 ((ZMod.isUnit_iff_coprime n _).1 h))
      simp [this]
end Formalism.HermitianLattices.ZeroFreeRegionGL2
