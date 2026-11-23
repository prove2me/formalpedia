-- Prove2me | solution 1 for Formalism.ELL.EulerSeries.coeff_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:58:52.843522+00:00
-- url     : https://prove2.me/submissions/91e103b9-a9cb-42a8-a179-0c50c62cbdce

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ConstantCoeffLogOnePlus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.EulerSeries
open Formalism.G Formalism.ELL
variable {K : Type*} [NormedField K] [CharZero K] {σ : Type} [DecidableEq σ]
namespace Formalism.ELL.EulerSeries
theorem _root_.solution {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    ∀ (n : ℕ) (d : σ →₀ ℕ), d.degree < n → MvPowerSeries.coeff d (f ^ n) = 0
  | 0, d, hd => absurd hd (Nat.not_lt_zero _)
  | n + 1, d, hd => by
    rw [pow_succ', MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdeg := congrArg Finsupp.degree hp
    rw [map_add] at hdeg
    by_cases h1 : p.1 = 0
    · rw [h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul]
    · have : 0 < p.1.degree :=
        Nat.pos_of_ne_zero (fun h => h1 ((Finsupp.degree_eq_zero_iff _).mp h))
      rw [solution hf n p.2 (by omega), mul_zero]
end Formalism.ELL.EulerSeries
