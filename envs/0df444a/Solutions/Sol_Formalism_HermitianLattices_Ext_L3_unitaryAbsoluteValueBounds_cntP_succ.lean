-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.cntP_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:55.41214+00:00
-- url     : https://prove2.me/submissions/2f6ad8df-1d15-48d4-be1f-6f6c9a3e3042

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemRangeLinPart
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityField
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_sg_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_sg_sg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_inQ_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_finite_AQ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_card_AQ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_exists_tr_one
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SecondPropositionFree_card_lift_pred
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SecondPropositionFree_mem_range_linPart
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_exists_inv_theta
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_exists_theta
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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k M : ℕ} (hk : 1 ≤ k) (hM : 1 ≤ M) {n : 𝓞 K} (hn : conjO K n = n) :
    cntP hF 𝔭 (k + 1) M n = Ideal.absNorm 𝔭 ^ (2 * M - 1) * cntP hF 𝔭 k M n := by
  have hle : extP K 𝔭 ^ (k + 1) ≤ extP K 𝔭 ^ k := Ideal.pow_le_pow_right (Nat.le_succ k)
  have := finite_AQ (K := K) h𝔭 (k + 1)
  obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
  obtain ⟨e, he⟩ := idealPowerSpanBounds.exists_inv_theta hθ (k + 1)
  have hIn : ∀ a : AQ K 𝔭 (k + 1), InQ 𝔭 k (Ideal.Quotient.factor hle a) ↔ InQ 𝔭 (k + 1) a := by
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.factor_mk, inQ_mk 𝔭 hk, inQ_mk 𝔭 (by omega)]
  have h := SecondPropositionFree.card_lift_pred (σ := sg hF 𝔭 (k + 1)) (τ := sg hF 𝔭 k)
    (π := Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [sg_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, sg_mk])
    (sg_sg hF 𝔭 (k + 1))
    (by
      intro a b ha hb
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at ha hb
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have h2 : a * b ∈ extP K 𝔭 ^ (k + k) := by rw [pow_add]; exact Ideal.mul_mem_mul ha hb
      exact Ideal.pow_le_pow_right (by omega) h2)
    (θ := Ideal.Quotient.mk _ θ) (e := Ideal.Quotient.mk _ e)
    (by
      rw [sg_mk, ← map_sub, ← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      exact he)
    (n := Ideal.Quotient.mk _ n) (by rw [sg_mk, hn]) (Ideal.absNorm 𝔭)
    (by rw [card_AQ hK hF, card_AQ hK hF]; ring) M hM
    (fun x => ¬ ∀ i, InQ 𝔭 k (x i))
    (by
      intro y hy w hw
      push Not at hy
      obtain ⟨i₀, hi₀⟩ := hy
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (y i₀)
      rw [← ha, Ideal.Quotient.factor_mk, inQ_mk 𝔭 hk] at hi₀
      obtain ⟨b, hb⟩ := exists_tr_one hK hF h𝔭 hi₀ (k + 1)
      refine SecondPropositionFree.mem_range_linPart _ y i₀ (b := Ideal.Quotient.mk _ b) ?_ hw
      rw [← ha, sg_mk, sg_mk, ← map_mul, ← map_mul, ← map_add, ← map_one (Ideal.Quotient.mk _),
        Ideal.Quotient.eq]
      exact hb)
  rw [Ideal.Quotient.factor_mk] at h
  unfold cntP
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp only [hIn])
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
