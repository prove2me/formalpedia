-- Prove2me | solution 1 for Formalism.MainNotions.J.coeff_pow_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:14.500028+00:00
-- url     : https://prove2.me/submissions/6e5fa563-04f9-4969-8018-4d882055d840

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open MvPowerSeries
variable {ι κ : Type} {R S : Type} [CommRing R] [CommRing S]
namespace Formalism.MainNotions.J
theorem _root_.solution {f : MvPowerSeries ι R} (hf : constantCoeff f = 0) :
    ∀ (d : ℕ) (n : ι →₀ ℕ), n.degree < d → coeff n (f ^ d) = 0 := by
  classical
  intro d
  induction d with
  | zero => intro n hn; exact absurd hn (Nat.not_lt_zero _)
  | succ d ih =>
    intro n hn
    rw [pow_succ, MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    replace hp : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    by_cases h2 : p.2 = 0
    · rw [h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, mul_zero]
    · have hdeg : p.1.degree + p.2.degree = n.degree := by
        rw [← hp]
        first
        | exact (Finsupp.degree_add p.1 p.2).symm
        | exact (map_add Finsupp.degree p.1 p.2).symm
        | simp [Finsupp.degree_add]
      have hpos : p.2.degree ≠ 0 := by
        intro h
        apply h2
        first
        | exact (Finsupp.degree_eq_zero_iff _).mp h
        | exact Finsupp.degree_eq_zero_iff.mp h
      rw [ih p.1 (by omega), zero_mul]
end Formalism.MainNotions.J
