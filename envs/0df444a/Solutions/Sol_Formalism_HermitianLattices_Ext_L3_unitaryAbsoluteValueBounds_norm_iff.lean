-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.norm_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:20.155275+00:00
-- url     : https://prove2.me/submissions/bee4eb09-0f77-400e-b0ea-76e85f786026

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityField
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CntIOneOfNotMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_mulW_mk
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_of_mul_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mul_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_sg_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
open NormLifting
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭)
    (h2 : ϖ ∉ 𝔭 ^ 2) (j : ℕ) {M : ℕ} {n n' : 𝓞 K} (hn : n - ι ϖ ^ 2 * n' ∈ extP K 𝔭 ^ (j + 2))
    (y : Fin M → AQ K 𝔭 (j + 1)) :
    ∑ i, sg hF 𝔭 (j + 2) (mulW 𝔭 (map_mem h1) j (y i)) * mulW 𝔭 (map_mem h1) j (y i) =
        Ideal.Quotient.mk _ n ↔
      ∑ i, sg hF 𝔭 j (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ j)) (y i)) *
        Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ j)) (y i) =
        Ideal.Quotient.mk _ n' := by
  choose z hz using fun i => Ideal.Quotient.mk_surjective (y i)
  obtain rfl : (fun i => Ideal.Quotient.mk _ (z i)) = y := funext hz
  simp only [mulW_mk, Ideal.Quotient.factor_mk, sg_mk, ← map_mul, ← map_sum]
  rw [Ideal.Quotient.eq, Ideal.Quotient.eq]
  have e1 : ∑ i, conjO K (ι ϖ * z i) * (ι ϖ * z i) = ι ϖ ^ 2 * ∑ i, conjO K (z i) * z i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, idealPowerSpanBounds.conjO_map hF]
    ring
  rw [e1]
  have h3 : ϖ * ϖ ∉ 𝔭 ^ (1 + 1 + 1) := idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) h2 h2
  constructor
  · intro h
    have h4 := add_mem h hn
    have e2 : ι ϖ ^ 2 * ∑ i, conjO K (z i) * z i - n + (n - ι ϖ ^ 2 * n') =
        ι (ϖ * ϖ) * (∑ i, conjO K (z i) * z i - n') := by rw [map_mul]; ring
    rw [e2] at h4
    exact idealPowerSpanBounds.mem_of_mul_mem h𝔭 (v := 2) (j := j) h3 (by rwa [show 2 + j = j + 2 by ring])
  · intro h
    have h4 : ι ϖ ^ 2 * (∑ i, conjO K (z i) * z i - n') ∈ extP K 𝔭 ^ (j + 2) := by
      rw [show j + 2 = 2 + j by ring, pow_add]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (map_mem h1) 2) h
    have h5 := sub_mem h4 hn
    have e2 : ι ϖ ^ 2 * (∑ i, conjO K (z i) * z i - n') - (n - ι ϖ ^ 2 * n') =
        ι ϖ ^ 2 * ∑ i, conjO K (z i) * z i - n := by ring
    rwa [e2] at h5
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
