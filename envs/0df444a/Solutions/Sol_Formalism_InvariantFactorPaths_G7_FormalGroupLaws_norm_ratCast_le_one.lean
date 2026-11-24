-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLaws.norm_ratCast_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:18.000468+00:00
-- url     : https://prove2.me/submissions/bf2bea11-8423-4854-a708-5ad00c2ca822

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws
namespace Formalism.InvariantFactorPaths.G7.FormalGroupLaws
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ}
    (hp : p.Prime) (hnp : ‖(p : K)‖ < 1) (r : ℚ) (hr : ¬ p ∣ r.den) : ‖(r : K)‖ ≤ 1 := by
  have hden : 1 ≤ ‖(r.den : K)‖ := by
    have hcop : Nat.Coprime r.den p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hr).symm
    have hab : (r.den : ℤ) * Nat.gcdA r.den p + (p : ℤ) * Nat.gcdB r.den p = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hcop, Nat.cast_one]
    have h1 : (1 : K) = (r.den : K) * ((Nat.gcdA r.den p : ℤ) : K) + (p : K) * ((Nat.gcdB r.den p : ℤ) : K) := by
      have h1' := congrArg (Int.cast : ℤ → K) hab
      push_cast at h1'
      exact h1'.symm
    by_contra hlt
    push_neg at hlt
    have hm := IsUltrametricDist.norm_add_le_max ((r.den : K) * ((Nat.gcdA r.den p : ℤ) : K))
      ((p : K) * ((Nat.gcdB r.den p : ℤ) : K))
    rw [← h1, norm_one, norm_mul, norm_mul] at hm
    have ha := IsUltrametricDist.norm_intCast_le_one K (Nat.gcdA r.den p)
    have hb := IsUltrametricDist.norm_intCast_le_one K (Nat.gcdB r.den p)
    have e1 : ‖(r.den : K)‖ * ‖((Nat.gcdA r.den p : ℤ) : K)‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) ha) hlt
    have e2 : ‖(p : K)‖ * ‖((Nat.gcdB r.den p : ℤ) : K)‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hb) hnp
    exact absurd hm (not_le.mpr (max_lt e1 e2))
  have hnum : ‖(r.num : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K r.num
  rw [Rat.cast_def, norm_div]
  exact div_le_one_of_le₀ (hnum.trans hden) (norm_nonneg _)
end Formalism.InvariantFactorPaths.G7.FormalGroupLaws
