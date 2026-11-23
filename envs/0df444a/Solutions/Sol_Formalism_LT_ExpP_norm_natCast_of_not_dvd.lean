-- Prove2me | solution 1 for Formalism.LT.ExpP.norm_natCast_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:57.512818+00:00
-- url     : https://prove2.me/submissions/525b8f63-2b61-48f2-8f1c-4505b643f58a

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.ExpP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.ExpP
theorem _root_.solution {p m : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (hm : ¬ p ∣ m) :
    ‖(m : K)‖ = 1 := by
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K m) ?_
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * p + b * m = 1 := by
    have h := Nat.gcd_eq_gcd_ab p m
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    exact ⟨Nat.gcdA p m, Nat.gcdB p m, by push_cast at h; linarith⟩
  have h1 : (1 : K) = (a : K) * (p : K) + (b : K) * (m : K) := by
    have := congrArg (Int.cast : ℤ → K) hab
    push_cast at this
    exact this.symm
  have hle : (1 : ℝ) ≤ max ‖(a : K) * p‖ ‖(b : K) * m‖ := by
    calc (1 : ℝ) = ‖(1 : K)‖ := norm_one.symm
      _ = ‖(a : K) * p + (b : K) * m‖ := by rw [← h1]
      _ ≤ max ‖(a : K) * p‖ ‖(b : K) * m‖ := IsUltrametricDist.norm_add_le_max _ _
  have ha := IsUltrametricDist.norm_intCast_le_one K a
  have hb := IsUltrametricDist.norm_intCast_le_one K b
  rcases le_max_iff.1 hle with h | h
  · rw [norm_mul] at h
    nlinarith [norm_nonneg (p : K), norm_nonneg (a : K)]
  · rw [norm_mul] at h
    nlinarith [norm_nonneg (m : K), norm_nonneg (b : K)]
end Formalism.LT.ExpP
