-- Prove2me | solution 1 for Formalism.L2.Th1.G.integral_dist_jets_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:38:57.619952+00:00
-- url     : https://prove2.me/submissions/844de2d8-5041-4274-b68c-b4246cac9006

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_LT_TorsProof_one_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.L2.Th1.G
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral)
namespace HurwitzJetIntegrality
end HurwitzJetIntegrality
open HurwitzJetIntegrality
namespace HurwitzJetIntegrality
end HurwitzJetIntegrality
private theorem intPS_mul_paired_square_jets {K : Type} [Field K] {R : Subring K} {f g : PowerSeries K}
    (hf : Formalism.L2.Th1.C.IntPS R f) (hg : Formalism.L2.Th1.C.IntPS R g) : Formalism.L2.Th1.C.IntPS R (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact R.sum_mem fun p _ => R.mul_mem (hf p.1) (hg p.2)
private theorem intPS_derivative' {K : Type} [Field K] {R : Subring K} {f : PowerSeries K}
    (hf : Formalism.L2.Th1.C.IntPS R f) : Formalism.L2.Th1.C.IntPS R (PowerSeries.derivative K f) := by
  intro n
  have h : PowerSeries.coeff n (PowerSeries.derivative K f) = PowerSeries.coeff (n + 1) f * (n + 1) := by
    first
      | exact PowerSeries.coeff_derivativeFun f n
      | (rw [PowerSeries.derivative_coe, PowerSeries.coeff_derivativeFun])
      | simp [PowerSeries.derivative]
  rw [h]
  have hn : ((n : K) + 1) ∈ R := R.add_mem (by simpa using R.natCast_mem n) R.one_mem
  exact R.mul_mem (hf (n + 1)) hn
private theorem intPS_inv_of_isOneUnit {K : Type} [Field K] {R : Subring K} {u : PowerSeries K}
    (hu : Formalism.L2.Th1.C.IsOneUnit R u) : Formalism.L2.Th1.C.IntPS R u⁻¹ := by
  obtain ⟨h0, hI⟩ := hu
  have hmul : u * u⁻¹ = 1 := PowerSeries.mul_inv_cancel u (by rw [h0]; exact one_ne_zero)
  have h0' : PowerSeries.coeff 0 u = 1 := by rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc := congrArg (PowerSeries.coeff n) hmul
    have hs := Finset.add_sum_erase (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ))
      (fun p : ℕ × ℕ => PowerSeries.coeff p.1 u * PowerSeries.coeff p.2 u⁻¹)
      (show ((0 : ℕ), n) ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)) from
        Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add n))
    beta_reduce at hs
    rw [PowerSeries.coeff_mul, ← hs, h0', one_mul] at hc
    rw [eq_sub_of_add_eq hc]
    refine R.sub_mem ?_ (R.sum_mem fun p hp => R.mul_mem (hI p.1) (ih p.2 ?_))
    · rw [PowerSeries.coeff_one]
      split_ifs
      exacts [R.one_mem, R.zero_mem]
    · have h1 := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_of_mem_erase hp)
      have h2 := Finset.ne_of_mem_erase hp
      rcases p with ⟨a, b⟩
      simp only at h1 ⊢
      by_contra hb
      have ha : a = 0 := by omega
      have hb' : b = n := by omega
      exact h2 (by rw [ha, hb'])
end Formalism.L2.Th1.G
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral)
open HurwitzJetIntegrality
namespace Formalism.L2.Th1.G
theorem _root_.solution : IntDJets := by
  intro K _ R l f hl hf i
  have hu := intPS_inv_of_isOneUnit hl
  have hit : ∀ j, Formalism.L2.Th1.C.IntPS R ((Formalism.L2.Th1.C.Dinv l)^[j] f) := by
    intro j
    induction j with
    | zero => exact hf
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact intPS_mul_paired_square_jets hu (intPS_derivative' ih)
  have h := hit i 0
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  exact h
end Formalism.L2.Th1.G
