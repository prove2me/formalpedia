-- Prove2me | solution 1 for Formalism.ELL.Lemma2Aux.norm_nat_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:57.49881+00:00
-- url     : https://prove2.me/submissions/1db38927-6c15-4564-81fb-7091fef2afc5

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionWeights
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CoefficientWeightsLemmaTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open Formalism Formalism.ELL Formalism.ELL.Lemma2Aux
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.Lemma2Aux
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hpl : ‖(p : K)‖ < 1) (m : ℕ) (hm : ¬ p ∣ m) :
    ‖(m : K)‖ = 1 := by
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have h := Nat.gcd_eq_gcd_ab p m
  rw [hcop] at h
  have hK : (1 : K) = (p : K) * (Nat.gcdA p m : K) + (m : K) * (Nat.gcdB p m : K) := by
    have := congrArg (Int.cast : ℤ → K) h
    push_cast at this
    exact this
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K m) ?_
  by_contra hlt
  push_neg at hlt
  have hmax := IsUltrametricDist.norm_add_le_max ((p : K) * (Nat.gcdA p m : K)) ((m : K) * (Nat.gcdB p m : K))
  rw [← hK, norm_one, norm_mul, norm_mul] at hmax
  have ha := IsUltrametricDist.norm_intCast_le_one K (Nat.gcdA p m)
  have hb := IsUltrametricDist.norm_intCast_le_one K (Nat.gcdB p m)
  have h1 : ‖(p : K)‖ * ‖((Nat.gcdA p m : ℤ) : K)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) ha) hpl
  have h2 : ‖(m : K)‖ * ‖((Nat.gcdB p m : ℤ) : K)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hb) hlt
  exact absurd hmax (not_le.2 (max_lt h1 h2))
end Formalism.ELL.Lemma2Aux
