-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.tendsto_sum_coset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:14.445859+00:00
-- url     : https://prove2.me/submissions/0836b875-4fa6-4408-a822-1443a7885b3c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemIdealLatticeIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumCoset
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_sum_le_sum_shift
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_exists_shifts
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_tendsto_ratio
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_tendsto_sum_ideal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
private theorem tendsto_scaled_of_interleaved_tendsto (D : ℕ) {u v : ℕ → ℝ} {L : ℝ}
    (hv : Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-(D : ℤ)) * v j) atTop (𝓝 L))
    (hup : ∀ᶠ j in atTop, u j ≤ v (j + 1))
    (hlo : ∀ᶠ j in atTop, v j ≤ u (j + 1)) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-(D : ℤ)) * u j) atTop (𝓝 L) := by
  have hg : ∀ j : ℕ, ((j : ℝ) ^ 2) ^ (-(D : ℤ)) = (((j : ℝ) ^ 2) ^ D)⁻¹ := fun j => by
    rw [zpow_neg, zpow_natCast]
  simp only [hg] at hv ⊢
  have hs := tendsto_ratio D
  have hs1 : Tendsto (fun j : ℕ => ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) /
      ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)) atTop (𝓝 1) :=
    hs.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun j : ℕ => ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) /
      ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)) atTop (𝓝 1) := by
    have h := hs1.inv₀ one_ne_zero
    simpa only [inv_div, inv_one] using h
  have hv2 : Tendsto (fun j : ℕ => ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1))
      atTop (𝓝 L) :=
    (hv.comp (tendsto_add_atTop_nat 1)).comp (tendsto_add_atTop_nat 1)
  have lowT : Tendsto (fun j : ℕ => (((j : ℝ) ^ 2) ^ D) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) *
      ((((j : ℝ) ^ 2) ^ D)⁻¹ * v j)) atTop (𝓝 L) := by
    simpa only [one_mul] using hs.mul hv
  have upT : Tendsto (fun j : ℕ => ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) /
      ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) *
      (((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1))) atTop (𝓝 L) := by
    simpa only [one_mul] using ht.mul hv2
  have hup1 : ∀ᶠ j in atTop, u (j + 1) ≤ v (j + 1 + 1) := (tendsto_add_atTop_nat 1).eventually hup
  rw [← tendsto_add_atTop_iff_nat 1]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' lowT upT ?_ ?_
  · filter_upwards [hlo, eventually_ge_atTop 1] with j hj hj1
    have hj0 : ((j : ℝ) ^ 2) ^ D ≠ 0 :=
      pow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega)))
    have hpos : 0 ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ := by positivity
    calc (((j : ℝ) ^ 2) ^ D) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) * ((((j : ℝ) ^ 2) ^ D)⁻¹ * v j)
        = ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v j := by
          rw [div_mul_eq_mul_div, ← mul_assoc, mul_inv_cancel₀ hj0, one_mul, div_eq_inv_mul]
      _ ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * u (j + 1) := mul_le_mul_of_nonneg_left hj hpos
  · filter_upwards [hup1] with j hj
    have hpos : 0 ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ := by positivity
    have h0 : ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) ≠ 0 :=
      pow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)))
    calc ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * u (j + 1)
        ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1) := mul_le_mul_of_nonneg_left hj hpos
      _ = ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) *
          (((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1)) := by
          rw [div_mul_eq_mul_div, ← mul_assoc, mul_inv_cancel₀ h0, one_mul, div_eq_inv_mul]
end Formalism.HermitianLattices.Ext.L3.BoxSum
end
end

set_option autoImplicit false
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {m : ℕ} (hm : 1 ≤ m)
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (x₀ : 𝓞 F) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x₀ ∈ I},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1))
      atTop (𝓝 ((m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm I : ℝ))) := by
  obtain ⟨y, y', R, hy, hy', hyI, hy'I⟩ := exists_shifts hI x₀
  obtain ⟨j0, hj0⟩ := exists_nat_ge R
  refine tendsto_scaled_of_interleaved_tendsto _ (tendsto_sum_ideal hK hF hm hI) ?_ ?_
  · filter_upwards [eventually_ge_atTop j0] with j hj
    have hRj : R ≤ (j : ℝ) := le_trans hj0 (by exact_mod_cast hj)
    refine sum_le_sum_shift hK hF m (A := {n | n - x₀ ∈ I}) (B := (I : Set (𝓞 F)))
      (T := (j : ℝ) ^ 2) (T' := ((j + 1 : ℕ) : ℝ) ^ 2) y (fun w => (hy w).1) ?_ ?_
    · intro w
      have h1 := (hy w).2
      have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      push_cast
      nlinarith
    · intro n hn
      exact hyI n hn
  · filter_upwards [eventually_ge_atTop j0] with j hj
    have hRj : R ≤ (j : ℝ) := le_trans hj0 (by exact_mod_cast hj)
    refine sum_le_sum_shift hK hF m (A := (I : Set (𝓞 F))) (B := {n | n - x₀ ∈ I})
      (T := (j : ℝ) ^ 2) (T' := ((j + 1 : ℕ) : ℝ) ^ 2) y' (fun w => (hy' w).1) ?_ ?_
    · intro w
      have h1 := (hy' w).2
      have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      push_cast
      nlinarith
    · intro n hn
      exact hy'I n hn
end Formalism.HermitianLattices.Ext.L3.BoxSum
