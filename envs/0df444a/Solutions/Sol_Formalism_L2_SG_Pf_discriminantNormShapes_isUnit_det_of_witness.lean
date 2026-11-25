-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.isUnit_det_of_witness
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:41:10.822287+00:00
-- url     : https://prove2.me/submissions/a8de6b1c-3a61-43be-ad28-d71f079444c2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_EQMulDiagQMulEQMem
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOntoOfShape
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_det_one_add_sub_mem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero


section
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
namespace Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.HermitianLattices.Ext.L3.localValuationFiltration Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
private theorem mem_pow_vF_not_mem_pow_vF_succ {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {x : 𝓞 F} (hx : x ≠ 0) :
    x ∈ 𝔭 ^ vF 𝔭 x ∧ x ∉ 𝔭 ^ (vF 𝔭 x + 1) := by
  have hbdd : BddAbove {e : ℕ | x ∈ 𝔭 ^ e} := by
    have h0 : x ∉ ⨅ n : ℕ, 𝔭 ^ n := by
      rw [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top]
      simpa using hx
    simp only [Submodule.mem_iInf, not_forall] at h0
    obtain ⟨n, hn⟩ := h0
    refine ⟨n, fun e he => ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hn (Ideal.pow_le_pow_right hlt.le he)
  refine ⟨?_, fun h => ?_⟩
  · have h1 := Nat.sSup_mem (s := {e : ℕ | x ∈ 𝔭 ^ e}) ⟨0, by simp⟩ hbdd
    exact h1
  · have h2 : vF 𝔭 x + 1 ≤ vF 𝔭 x := le_csSup hbdd h
    omega
private theorem mem_extP_pow_sub_of_mul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} {e k : ℕ}
    (ha : a ∈ 𝔭 ^ e) (ha' : a ∉ 𝔭 ^ (e + 1)) (hek : e ≤ k) {w : 𝓞 K}
    (hw : w * ι a ∈ extP K 𝔭 ^ k) : w ∈ extP K 𝔭 ^ (k - e) := by
  have hkP : extP K 𝔭 ^ k = extP K 𝔭 ^ (k - e) * extP K 𝔭 ^ e := by
    rw [← pow_add, Nat.sub_add_cancel hek]
  obtain ⟨J, hJ⟩ : 𝔭 ^ e ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr ha
  have hJP : J ⊔ 𝔭 = ⊤ := by
    by_contra hne
    have hle : J ≤ 𝔭 := le_sup_left.trans (le_of_eq (h𝔭.eq_of_le hne le_sup_right).symm)
    apply ha'
    have h1 : a ∈ 𝔭 ^ e * J := by
      rw [← hJ]
      exact Ideal.mem_span_singleton_self a
    rw [pow_succ]
    exact Ideal.mul_mono_right hle h1
  have hspan : Ideal.span {algebraMap (𝓞 F) (𝓞 K) a} =
      extP K 𝔭 ^ e * J.map (algebraMap (𝓞 F) (𝓞 K)) := by
    have h1 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hJ
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_mul, Ideal.map_pow] at h1
    exact h1
  have hcop : IsCoprime (extP K 𝔭 ^ (k - e)) (J.map (algebraMap (𝓞 F) (𝓞 K))) := by
    apply IsCoprime.pow_left
    rw [Ideal.isCoprime_iff_sup_eq]
    have h1 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hJP
    rw [Ideal.map_sup, Ideal.map_top] at h1
    rw [sup_comm]
    exact h1
  have hιinj : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) x = 0 → x = 0 := by
    intro x hx
    have h1 : algebraMap F K (algebraMap (𝓞 F) F x) = 0 := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, hx,
        map_zero]
    rw [map_eq_zero_iff _ (algebraMap F K).injective] at h1
    exact IsFractionRing.injective (𝓞 F) F (by rw [h1, map_zero])
  have ha0 : a ≠ 0 := fun h => ha' (h ▸ Ideal.zero_mem _)
  have hPe : extP K 𝔭 ^ e ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot]
    intro h0
    rw [h0, Ideal.bot_mul, Ideal.span_singleton_eq_bot] at hspan
    exact ha0 (hιinj a hspan)
  have hdiv : extP K 𝔭 ^ (k - e) * extP K 𝔭 ^ e ∣
      (Ideal.span {w} * J.map (algebraMap (𝓞 F) (𝓞 K))) * extP K 𝔭 ^ e := by
    rw [← hkP]
    have h2 : extP K 𝔭 ^ k ∣ Ideal.span {w * algebraMap (𝓞 F) (𝓞 K) a} :=
      Ideal.dvd_span_singleton.mpr hw
    rw [← Ideal.span_singleton_mul_span_singleton, hspan, mul_comm (extP K 𝔭 ^ e),
      ← mul_assoc] at h2
    exact h2
  rw [mul_dvd_mul_iff_right hPe] at hdiv
  exact Ideal.dvd_span_singleton.mp (hcop.dvd_of_dvd_mul_right hdiv)
private theorem mem_extP_pow_sub_sum_vF_of_mul_prod_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (a : Fin m → 𝓞 F)
    (ha : ∀ i, a i ≠ 0) (w : 𝓞 K) (s : Finset (Fin m)) :
    ∀ k, w * ∏ i ∈ s, ι (a i) ∈ extP K 𝔭 ^ k → w ∈ extP K 𝔭 ^ (k - ∑ i ∈ s, vF 𝔭 (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro k hk
    simpa using hk
  | @insert i s hi ih =>
    intro k hk
    rw [Finset.prod_insert hi] at hk
    rw [Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := mem_pow_vF_not_mem_pow_vF_succ h𝔭 (ha i)
    by_cases hle : vF 𝔭 (a i) ≤ k
    · have h3 : (w * ∏ j ∈ s, ι (a j)) * ι (a i) ∈ extP K 𝔭 ^ k := by
        convert hk using 1
        ring
      have h4 := ih (k - vF 𝔭 (a i)) (mem_extP_pow_sub_of_mul_mem h𝔭 h1 h2 hle h3)
      rwa [Nat.sub_sub] at h4
    · have h5 : k - (vF 𝔭 (a i) + ∑ j ∈ s, vF 𝔭 (a j)) = 0 := by omega
      rw [h5, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
end Formalism.L2.SG.Pf.discriminantNormShapes
end
end

set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.HermitianLattices.Ext.L3.localValuationFiltration Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.L2.SG.Pf.discriminantNormShapes
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : Fin m → 𝓞 F}
    (ha : ∀ i, a i ≠ 0) {k : ℕ} (hk : vJof 𝔭 a + 1 ≤ k)
    {Y P W : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y)
    (hW : Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a)
    (hWH : ∀ i j, (W * diagQ K 𝔭 k a) i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) :
    IsUnit P.det := by
  classical
  have hk0 : k ≠ 0 := by omega
  have hPk : extP K 𝔭 ^ k ≤ extP K 𝔭 := Ideal.pow_le_self hk0
  have hnil : ∀ z ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)), IsNilpotent z := by
    intro z hz
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hw : w ∈ extP K 𝔭 := (Ideal.mem_quotient_iff_mem hPk).mp hz
    exact ⟨k, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hw k⟩
  have hmat : Yᴴ * P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * (1 + W * diagQ K 𝔭 k a) := by
    rw [Matrix.mul_assoc, hPY, ← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_one,
      ← Matrix.mul_assoc, ← hW]
    abel
  have hdet := congrArg Matrix.det hmat
  simp only [Matrix.det_mul] at hdet
  have hδ : (diagQ K 𝔭 k a).det = Ideal.Quotient.mk (extP K 𝔭 ^ k) (∏ i, ι (a i)) := by
    simp only [diagQ, Matrix.det_diagonal, map_prod]
  have hu := det_one_add_sub_mem hWH
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
    (Yᴴ.det * P.det - (1 + W * diagQ K 𝔭 k a).det)
  have hx : w * ∏ i, ι (a i) ∈ extP K 𝔭 ^ k := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hw, ← hδ, sub_mul, hdet]
    ring
  have hv : vJof 𝔭 a = ∑ i, vF 𝔭 (a i) := rfl
  have hw1 : w ∈ extP K 𝔭 := by
    have h1 := mem_extP_pow_sub_sum_vF_of_mul_prod_mem h𝔭 a ha w Finset.univ k hx
    exact Ideal.pow_le_self (by rw [hv] at hk; omega) h1
  have hsum : Yᴴ.det * P.det - 1 ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
    have h2 : Yᴴ.det * P.det - 1 = (Yᴴ.det * P.det - (1 + W * diagQ K 𝔭 k a).det) +
        ((1 + W * diagQ K 𝔭 k a).det - 1) := by ring
    rw [h2]
    refine Ideal.add_mem _ ?_ hu
    rw [← hw]
    exact Ideal.mem_map_of_mem _ hw1
  have hunit : IsUnit (Yᴴ.det * P.det) := by
    have h3 := (hnil _ hsum).isUnit_one_add
    have h4 : 1 + (Yᴴ.det * P.det - 1) = Yᴴ.det * P.det := by ring
    rw [h4] at h3
    exact h3
  exact isUnit_of_mul_isUnit_right hunit
end Formalism.L2.SG.Pf.discriminantNormShapes
