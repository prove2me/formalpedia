-- Prove2me | solution 1 for Formalism.ELL.Lemma2Aux.coeff_X0_add_X1_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:44.661803+00:00
-- url     : https://prove2.me/submissions/7f6169a7-9498-47e7-9eaa-d1975bdf6fb6

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
theorem _root_.solution {R : Type*} [CommRing R] (d i j : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j)
      ((MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ d) =
      if i + j = d then (d.choose i : R) else 0 := by
  rw [add_pow, map_sum]
  have hterm : ∀ m ∈ Finset.range (d + 1),
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j)
        ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) ^ m * MvPowerSeries.X 1 ^ (d - m) *
          (d.choose m : MvPowerSeries (Fin 2) R)) =
      if m = i ∧ d - m = j then (d.choose m : R) else 0 := by
    intro m _
    rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial,
      ← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := R)), mul_comm, MvPowerSeries.coeff_C_mul,
      MvPowerSeries.coeff_monomial]
    have : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j =
        Finsupp.single 0 m + Finsupp.single 1 (d - m)) ↔ (m = i ∧ d - m = j) := by
      constructor
      · intro h
        have h0 := congrArg (· 0) h
        have h1 := congrArg (· 1) h
        simp at h0 h1
        omega
      · rintro ⟨rfl, rfl⟩; rfl
    by_cases hc : m = i ∧ d - m = j
    · rw [if_pos (this.2 hc), if_pos hc]; simp
    · rw [if_neg (fun h => hc (this.1 h)), if_neg hc, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  by_cases hij : i + j = d
  · rw [if_pos hij, Finset.sum_eq_single i]
    · rw [if_pos ⟨rfl, by omega⟩]
    · intro b _ hb; rw [if_neg (fun h => hb h.1)]
    · intro h; simp at h; omega
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun m hm => ?_
    simp at hm
    rw [if_neg (by omega)]
end Formalism.ELL.Lemma2Aux
