-- Prove2me | solution 1 for Formalism.L2.Th1.D.trace_dual_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:03:07.313799+00:00
-- url     : https://prove2.me/submissions/7f586c51-f8a7-4086-902d-5a12ea58880f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TraceDualExists
import Theorems.Thm_Formalism_L2_Th1_D_TraceDualSums_sum_zmod
import Theorems.Thm_Formalism_L2_Th1_D_TraceDualSums_sum_range_even
import Theorems.Thm_Formalism_L2_Th1_D_TraceDualSums_norm_det_le
import Theorems.Thm_Formalism_L2_Th1_D_TraceDualSums_inv_shift
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_eq_one_of_not_dvd
import Theorems.Thm_Formalism_FG_ShiftFEAux_pow_inj
import Theorems.Thm_Formalism_L2_Th1_D_B4_iterate_of_pow
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_norm_eq_one_of_pow
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_root_eq_of_norm_lt
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_pow_inj
import Theorems.Thm_Formalism_L2_Th1_D_teichSigma
import Theorems.Thm_GlobalTheory_NatCastUnitNorm_norm_natCast_eq_one_of_not_dvd


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open TraceDualSums Fin.NatCast
namespace Formalism.L2.Th1.D
theorem _root_.solution : TrDualExists := by
  intro K _ _ _ l d _ σ hU hd ζ hζ
  obtain ⟨m, rfl⟩ := hd
  have hd0 : m + m ≠ 0 := NeZero.ne (m + m)
  have hm0 : m ≠ 0 := by omega
  have hdm : (m + m) / 2 = m := by omega
  rw [hdm]
  have : NeZero m := ⟨hm0⟩
  have hp : l.Prime := hU.1
  have hl3 : 2 < l := hU.2.1
  have hlt : ‖(l : K)‖ < 1 := by
    rw [hU.2.2.1]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hpos : 1 ≤ l ^ (m + m) := Nat.one_le_pow _ _ hp.pos
  have hnd : ¬ l ∣ l ^ (m + m) - 1 := by
    intro h
    have h1 : l ∣ l ^ (m + m) := dvd_pow_self l hd0
    have h2 : l ∣ 1 := by
      have := (Nat.dvd_sub h1 h)
      rwa [Nat.sub_sub_self hpos] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hN : ‖((l ^ (m + m) - 1 : ℕ) : K)‖ = 1 :=
    Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp hlt hnd
  have hN0 : l ^ (m + m) - 1 ≠ 0 := by
    intro h
    rw [h] at hnd
    exact hnd (dvd_zero l)
  have nζ : ‖ζ‖ = 1 := FormalExponential.norm_eq_one_of_pow hN0 hζ.pow_eq_one
  have hσζ : σ ζ = ζ ^ l := teichSigma K l (m + m) σ hU (by omega) ζ hζ.pow_eq_one
  have hit : ∀ j, σ^[j] ζ = ζ ^ (l ^ j) := B4.iterate_of_pow hσζ
  have hper : σ^[m + m] ζ = ζ := by
    rw [hit, show l ^ (m + m) = (l ^ (m + m) - 1) + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]
  let τ : K →+* K := σ.comp σ
  have hτ : ∀ (k : ℕ) (a : K), τ^[k] a = σ^[2 * k] a := by
    intro k a
    rw [Function.iterate_mul]
    rfl
  have hper' : Function.IsPeriodicPt τ m ζ := by
    show τ^[m] ζ = ζ
    rw [hτ, two_mul]
    exact hper
  let x : Fin m → K := fun k => σ^[2 * k.val] ζ
  have hxn : ∀ j : ℕ, x (j : Fin m) = τ^[j] ζ := by
    intro j
    show σ^[2 * ((j : Fin m) : ℕ)] ζ = _
    rw [Fin.val_natCast, ← hτ, hper'.iterate_mod_apply]
  have hxs : ∀ k, τ (x k) = x (k + 1) := by
    intro k
    have h : k + 1 = ((k.val + 1 : ℕ) : Fin m) := by
      rw [Nat.cast_succ, Fin.cast_val_eq_self]
    rw [h, hxn, Function.iterate_succ_apply', ← hxn, Fin.cast_val_eq_self]
  let V : Matrix (Fin m) (Fin m) K := Matrix.vandermonde x
  have hVa : ∀ k r, V k r = x k ^ (r : ℕ) := fun k r => Matrix.vandermonde_apply x k r
  have hVs : ∀ k r, τ (V k r) = V (k + 1) r := by
    intro k r
    rw [hVa, hVa, map_pow, hxs]
  have hxpow : ∀ k, x k = ζ ^ (l ^ (2 * k.val)) := fun k => hit _
  have hxN : ∀ k, x k ^ (l ^ (m + m) - 1) = 1 := by
    intro k
    rw [hxpow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have nx : ∀ k, ‖x k‖ = 1 := fun k => FormalExponential.norm_eq_one_of_pow hN0 (hxN k)
  have hsmall : ∀ k : Fin m, l ^ (2 * k.val) < l ^ (m + m) - 1 := by
    intro k
    have hk := k.2
    have h1 : l ^ (2 * k.val) ≤ l ^ (m + m - 1) := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : l ^ (m + m) = l ^ (m + m - 1) * l := by
      rw [← pow_succ]
      congr 1
      omega
    have h3 : 1 ≤ l ^ (m + m - 1) := Nat.one_le_pow _ _ hp.pos
    have h4 : l ^ (m + m - 1) * 3 ≤ l ^ (m + m - 1) * l := Nat.mul_le_mul_left _ hl3
    omega
  have hinj : Function.Injective x := by
    intro i j hij
    rw [hxpow, hxpow] at hij
    have h1 := hζ.pow_inj (hsmall i) (hsmall j) hij
    have h2 := Nat.pow_right_injective hp.two_le h1
    exact Fin.ext (by omega)
  have hdiff : ∀ i j, i ≠ j → ‖x j - x i‖ = 1 := by
    intro i j hij
    refine le_antisymm ?_ ?_
    · rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_neg, nx, nx, max_self]
    · by_contra hlt'
      exact hij (hinj (FormalExponential.root_eq_of_norm_lt hN (hxN j) (hxN i) (not_le.1 hlt'))).symm
  have hdet : ‖V.det‖ = 1 := by
    rw [Matrix.det_vandermonde, norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [norm_prod]
    exact Finset.prod_eq_one fun j hj => hdiff i j (ne_of_lt (Finset.mem_Ioi.1 hj))
  have hdet0 : V.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    exact zero_ne_one hdet
  let P : Matrix (Fin m) (Fin m) K := V⁻¹
  have hVP : V * P = 1 := Matrix.mul_nonsing_inv V (isUnit_iff_ne_zero.2 hdet0)
  have hPV : P * V = 1 := Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.2 hdet0)
  have hVint : ∀ k r, ‖V k r‖ ≤ 1 := by
    intro k r
    rw [hVa, norm_pow, nx, one_pow]
  have hPint : ∀ r k, ‖P r k‖ ≤ 1 := by
    intro r k
    show ‖(V⁻¹) r k‖ ≤ 1
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', norm_mul, norm_inv,
      hdet, inv_one, one_mul, Matrix.adjugate_apply]
    refine norm_det_le _ fun i j => ?_
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs <;> simp
    · exact hVint i j
  have hPs := inv_shift τ V P hVP hVs
  have hPn : ∀ (r : Fin m) (j : ℕ), τ^[j] (P r 0) = P r (j : Fin m) := by
    intro r j
    induction j with
    | zero => simp
    | succ j ih => rw [Function.iterate_succ_apply', ih, hPs, Nat.cast_succ]
  refine ⟨fun r => ζ ^ (r : ℕ), fun r => P r 0,
    ⟨fun r => ⟨by rw [norm_pow, nζ, one_pow], hPint r 0⟩, fun r => ⟨?_, ?_⟩⟩, ⟨?_, ?_⟩⟩
  · show σ^[m + m] (ζ ^ (r : ℕ)) = ζ ^ (r : ℕ)
    rw [iterate_map_pow, hper]
  · show σ^[m + m] (P r 0) = P r 0
    rw [← two_mul, ← hτ, hPn, Fin.natCast_self]
  · rw [Fintype.card_fin, two_mul]
  · intro r r'
    show (∑ s : ZMod (m + m), if s.val % 2 = 0 then σ^[s.val] (ζ ^ (r : ℕ) * P r' 0) else 0) = _
    rw [sum_zmod (m + m) (fun i => if i % 2 = 0 then σ^[i] (ζ ^ (r : ℕ) * P r' 0) else 0),
      ← two_mul, sum_range_even m (fun i => σ^[i] (ζ ^ (r : ℕ) * P r' 0)), Finset.sum_range]
    have hterm : ∀ k : Fin m, σ^[2 * (k : ℕ)] (ζ ^ (r : ℕ) * P r' 0) = P r' k * V k r := by
      intro k
      rw [iterate_map_mul, iterate_map_pow, ← hτ k.val (P r' 0), hPn, Fin.cast_val_eq_self, hVa,
        mul_comm]
    rw [Finset.sum_congr rfl fun k _ => hterm k, ← Matrix.mul_apply, hPV, Matrix.one_apply]
    simp only [eq_comm]
end Formalism.L2.Th1.D
