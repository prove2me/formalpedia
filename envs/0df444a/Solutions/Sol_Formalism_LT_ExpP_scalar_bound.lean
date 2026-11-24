-- Prove2me | solution 1 for Formalism.LT.ExpP.scalar_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:33:37.350598+00:00
-- url     : https://prove2.me/submissions/de4c744c-4ec6-4ae4-b92f-38d3755b1d30

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
import Theorems.Thm_Formalism_LT_ExpP_norm_natCast_eq

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (c : K) (d m : ℕ) (hmd : m < d)
    (hc : ‖(d : K) * c‖ ≤ 1) :
    ‖c * ((p : K) ^ (d - m) * (d.choose m : K))‖ ≤ ‖(p : K)‖ := by
  haveI := Fact.mk hp
  have hP0 : 0 ≤ ‖(p : K)‖ := norm_nonneg _
  have hP1 : ‖(p : K)‖ ≤ 1 := hp1.le
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, n + 1 - m = j + 1 := ⟨n - m, by omega⟩
  have hsym : (n + 1).choose (j + 1) = (n + 1).choose m := by
    rw [← hj]
    exact Nat.choose_symm (by omega)
  have hN : (n + 1).choose m * (j + 1) = (n + 1) * n.choose j := by
    rw [← hsym, Nat.add_one_mul_choose_eq]
  have hnorm : ‖((n + 1).choose m : K)‖ * ‖((j + 1 : ℕ) : K)‖ ≤ ‖((n + 1 : ℕ) : K)‖ := by
    have h := congrArg (fun x : ℕ => ‖(x : K)‖) hN
    simp only [Nat.cast_mul, norm_mul] at h
    rw [h]
    exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K _)
  have hkn : ‖((j + 1 : ℕ) : K)‖ = ‖(p : K)‖ ^ padicValNat p (j + 1) :=
    norm_natCast_eq hp hp1 (Nat.succ_ne_zero j)
  have hv : padicValNat p (j + 1) < j + 1 := by
    have h1 : p ^ padicValNat p (j + 1) ≤ j + 1 := Nat.le_of_dvd (Nat.succ_pos j) pow_padicValNat_dvd
    have h2 : j + 1 < p ^ (j + 1) := Nat.lt_pow_self hp.one_lt
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 (lt_of_le_of_lt h1 h2)
  have hcd : ‖c‖ * ‖((n + 1 : ℕ) : K)‖ ≤ 1 := by
    rw [mul_comm, ← norm_mul]
    exact_mod_cast hc
  rw [hj, norm_mul, norm_mul, norm_pow]
  have key : ‖c‖ * ‖((n + 1).choose m : K)‖ * ‖(p : K)‖ ^ padicValNat p (j + 1) ≤ 1 := by
    calc ‖c‖ * ‖((n + 1).choose m : K)‖ * ‖(p : K)‖ ^ padicValNat p (j + 1)
        = ‖c‖ * (‖((n + 1).choose m : K)‖ * ‖((j + 1 : ℕ) : K)‖) := by rw [hkn]; ring
      _ ≤ ‖c‖ * ‖((n + 1 : ℕ) : K)‖ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ ≤ 1 := hcd
  have hk' : ‖(p : K)‖ ^ (j + 1) =
      ‖(p : K)‖ ^ padicValNat p (j + 1) * ‖(p : K)‖ ^ (j + 1 - padicValNat p (j + 1)) := by
    rw [← pow_add]
    congr 1
    omega
  calc ‖c‖ * (‖(p : K)‖ ^ (j + 1) * ‖((n + 1).choose m : K)‖)
      = (‖c‖ * ‖((n + 1).choose m : K)‖ * ‖(p : K)‖ ^ padicValNat p (j + 1)) *
          ‖(p : K)‖ ^ (j + 1 - padicValNat p (j + 1)) := by rw [hk']; ring
    _ ≤ 1 * ‖(p : K)‖ ^ (j + 1 - padicValNat p (j + 1)) :=
        mul_le_mul_of_nonneg_right key (pow_nonneg hP0 _)
    _ ≤ ‖(p : K)‖ := by
        rw [one_mul]
        exact pow_le_of_le_one hP0 hP1 (by omega)
end Formalism.LT.ExpP
