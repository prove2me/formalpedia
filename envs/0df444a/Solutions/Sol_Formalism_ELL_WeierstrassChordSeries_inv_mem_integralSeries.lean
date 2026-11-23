-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.inv_mem_integralSeries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:30.308213+00:00
-- url     : https://prove2.me/submissions/bdc3ba5b-89ac-4a85-b8df-7694a34f0f3a

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_mem_T

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable (W : WeierstrassCurve K) (w : PowerSeries K)
variable {W w}
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution {φ : MvPowerSeries (Fin 2) K} (h : φ ∈ T W) (h0 : cc φ ≠ 0)
    (hi : (cc φ)⁻¹ ∈ Sadj W) : φ⁻¹ ∈ T W := by
  classical
  rw [mem_T] at h ⊢
  have step : ∀ n : Fin 2 →₀ ℕ, (∀ m, m < n → MvPowerSeries.coeff m φ⁻¹ ∈ Sadj W) →
      MvPowerSeries.coeff n φ⁻¹ ∈ Sadj W := by
    intro n ih
    rw [MvPowerSeries.coeff_inv]
    split_ifs with hn
    · exact hi
    · refine mul_mem (neg_mem hi) (sum_mem fun x _ => ?_)
      split_ifs with hx
      · exact mul_mem (h _) (ih _ hx)
      · exact zero_mem _
  intro n
  first
    | exact (wellFounded_lt (α := Fin 2 →₀ ℕ)).induction n step
    | exact WellFoundedLT.induction n step
    | exact (wellFounded_lt (α := Fin 2 →₀ ℕ)).induction (C := fun n => MvPowerSeries.coeff n φ⁻¹ ∈ Sadj W) n step
end Formalism.ELL.WeierstrassChordSeries
