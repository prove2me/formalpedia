-- Prove2me | solution 1 for Formalism.L2.Th1.H.cmPair_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:36:52.375805+00:00
-- url     : https://prove2.me/submissions/4fbb3758-1fc4-47ec-b44b-03018f38de84

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CommensurableK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RatFourSquares
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexNeZeroOfNsmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (k : ℂ) (hk : InK d k) :
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ (Formalism.L2.Th1.F.cmPair a b d ha hd).lattice,
      (N : ℂ) * k * z ∈ (Formalism.L2.Th1.F.cmPair a b d ha hd).lattice := by
  obtain ⟨p, q, rfl⟩ := hk
  have hs : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) * ((Real.sqrt (d : ℝ) : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  have hδ2 : (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))
      = -(d : ℂ) := by
    linear_combination (Complex.I * Complex.I) * hs + (d : ℂ) * Complex.I_mul_I
  have hpP : (p : ℂ) * (p.den : ℂ) = (p.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num p
  have hqQ : (q : ℂ) * (q.den : ℂ) = (q.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num q
  refine ⟨2 * a * p.den * q.den, by positivity, ?_⟩
  intro z hz
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hz
  rw [PeriodPair.mem_lattice]
  refine ⟨m * (2 * a * q.den * p.num - 2 * a * p.den * q.num * b) + n * (-(p.den * q.num * (b ^ 2 + d))),
    m * (2 * a * (2 * a * p.den * q.num)) + n * (2 * a * q.den * p.num + 2 * a * p.den * q.num * b), ?_⟩
  simp only [Formalism.L2.Th1.F.cmPair, Formalism.L2.Th1.F.cmTheta]
  push_cast
  linear_combination
    (-((m : ℂ) * a + n * ((b + Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) / 2)) * (2 * a * q.den)) * hpP
    - ((m : ℂ) * a + n * ((b + Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) / 2))
        * (2 * a * p.den * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))) * hqQ
    - ((a : ℂ) * p.den * q.num * n) * hδ2
end Formalism.L2.Th1.H
