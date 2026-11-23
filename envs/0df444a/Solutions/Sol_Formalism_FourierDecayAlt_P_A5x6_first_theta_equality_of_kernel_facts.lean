-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.first_theta_equality_of_kernel_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:33.920817+00:00
-- url     : https://prove2.me/submissions/eae978c6-34aa-4340-bab3-42d28abdeb0b

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_pt_det_isUnit
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_isPSD_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_glr_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_cSize_glr
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6
namespace Formalism.FourierDecayAlt.P.A5x6
theorem _root_.solution (hPer : SingleBlockPeriodic) (hGram : SingleBlockPosSemidef) (hPars : SingleBlockParseval) (hSup : NsSupport)
    (hBD : NsBlockDiag) : SingleBlockThetaProps := by
  intro K _ _ _ R ψ hL m
  classical
  have hrep : ∀ x : K ⧸ R.toAddSubgroup, ∃ u : Kˣ, ((u : K) : K ⧸ R.toAddSubgroup) = x := by
    intro x
    obtain ⟨r, hr, hu⟩ := hL.unitRep (Quotient.out x)
    refine ⟨hu.unit, ?_⟩
    rw [IsUnit.unit_spec, QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff r).mpr hr,
      add_zero]
    exact QuotientAddGroup.out_eq' x
  choose cr hcr using hrep
  have hcrsub : ∀ x : K, ((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) - x ∈ R := by
    intro x
    have h1 := QuotientAddGroup.eq.mp (hcr (x : K ⧸ R.toAddSubgroup))
    have h2 := R.toAddSubgroup.neg_mem h1
    have e : -(-((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) + x) =
      ((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) - x := by ring
    rw [e] at h2; exact h2
  let Θ : K → Point K → Point K → ℂ := fun x h h' =>
    Ns R ψ 1 h h' (cr (x : K ⧸ R.toAddSubgroup)) (cr (x : K ⧸ R.toAddSubgroup))
  have hΘt : ∀ (t : Kˣ) (h h' : Point K), h.1.sum = h'.1.sum →
      Θ (t : K) h h' = Ns R ψ 1 h h' t t :=
    fun t h h' e => hPer K R ψ hL h h' _ _ e (hcrsub t)
  have hsum : ∀ h h' : Point K, h.1.sum = h'.1.sum →
      ∑ᶠ x : K ⧸ R.toAddSubgroup, Θ (Quotient.out x) h h' =
        ((cSize R h * cSize R h' : ℝ) : ℂ) * N0 R ψ h h' := by
    intro h h' e
    rw [← (hPars K R ψ hL h h' e cr hcr).2]
    apply finsum_congr
    intro x
    simp only [Θ]
    rw [QuotientAddGroup.out_eq']
  have hglr : ∀ h h' : Point K, InGLR R h → ∀ y : K ⧸ R.toAddSubgroup,
      Ns R ψ 1 h h' (cr y) (cr y) ≠ 0 → y = 0 := by
    intro h h' hh y h0
    obtain ⟨h1, h2, h3⟩ := glr_det R h hh
    have h4 := (hSup K R ψ 1 le_rfl h h' _ _ h0).1
    have h5 : ((cr y : Kˣ) : K) ∈ R := by
      have := R.mul_mem h2 h4
      rwa [← mul_assoc, mul_comm _ (pt h.1 h.2).det, h3, one_mul] at this
    rw [← hcr y]
    exact (QuotientAddGroup.eq_zero_iff _).mpr h5
  refine ⟨Θ, fun t h h' e e' => hΘt t h h' (e.trans e'.symm),
    fun h h' e e' => hsum h h' (e.trans e'.symm), fun F hF => ?_⟩
  have hFF : ∀ h ∈ F, ∀ h' ∈ F, h.1.sum = h'.1.sum := fun h hh h' hh' =>
    (hF h hh).trans (hF h' hh').symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x r hr
    have : ((x + r : K) : K ⧸ R.toAddSubgroup) = (x : K ⧸ R.toAddSubgroup) := by
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff r).mpr hr, add_zero]
    funext h h'
    simp only [Θ]
    rw [this]
  · intro x
    exact hGram K R ψ hL m F hF (cr x)
  · obtain ⟨ϖ, hϖ, hϖx⟩ := hL.unif
    choose M hM using fun h : Point K => hϖx (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K)
    let N := F.sup M
    let L : Submodule R K :=
      { carrier := {x | (ϖ : K) ^ N * x ∈ R}
        add_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          rw [mul_add]; exact R.add_mem ha hb
        zero_mem' := by simp [R.zero_mem]
        smul_mem' := by
          intro c x hx
          simp only [Set.mem_ofPred_eq] at hx ⊢
          rw [Subring.smul_def, smul_eq_mul, mul_left_comm]
          exact R.mul_mem c.2 hx }
    refine ⟨L, ?_, ?_, ?_⟩
    · exact hL.isOpen.preimage (continuous_const_mul ((ϖ : K) ^ N))
    · have : (L : Set K) = (fun x => ((ϖ⁻¹ : Kˣ) : K) ^ N * x) '' (R : Set K) := by
        ext x
        constructor
        · intro hx
          refine ⟨(ϖ : K) ^ N * x, hx, ?_⟩
          simp only
          rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
        · rintro ⟨y, hy, rfl⟩
          show (ϖ : K) ^ N * (((ϖ⁻¹ : Kˣ) : K) ^ N * y) ∈ R
          rw [← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
          exact hy
      rw [this]
      exact hL.isCompact.image (continuous_const_mul _)
    · intro x hx h hh h' _
      by_contra h0
      apply hx
      have h4 := (hSup K R ψ 1 le_rfl h h' _ _ h0).1
      have hle : M h ≤ N := Finset.le_sup (f := M) hh
      show (ϖ : K) ^ N * x ∈ R
      have hpN : (ϖ : K) ^ N ∈ R := R.pow_mem hϖ N
      have e1 : (ϖ : K) ^ N * x = (ϖ : K) ^ (N - M h) *
          (((ϖ : K) ^ M h * (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K)) *
            ((pt h.1 h.2).det * ((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K))) -
          (ϖ : K) ^ N * (((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) - x) := by
        have e2 : (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) * (pt h.1 h.2).det = 1 :=
          IsUnit.val_inv_mul (pt_det_isUnit h)
        have e3 : (ϖ : K) ^ N = (ϖ : K) ^ (N - M h) * (ϖ : K) ^ M h := by
          rw [← pow_add, Nat.sub_add_cancel hle]
        calc (ϖ : K) ^ N * x = (ϖ : K) ^ N * ((((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) *
              (pt h.1 h.2).det) * ((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) -
              (ϖ : K) ^ N * (((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) - x) := by
                rw [e2]; ring
          _ = _ := by rw [e3]; ring
      rw [e1]
      exact R.sub_mem (R.mul_mem (R.pow_mem hϖ _) (R.mul_mem (hM h) h4))
        (R.mul_mem hpN (hcrsub x))
  · intro t
    apply isPSD_zero
    intro h hh h' hh'
    rw [hΘt t h h' (hFF h hh h' hh'), sub_self]
  · apply isPSD_zero
    intro h hh h' hh'
    rw [hsum h h' (hFF h hh h' hh'), pow_one, pow_one, sub_self]
  · intro x h hh h' hh' hne
    by_contra h0
    exact hne ((hBD K R ψ hL h h' (hFF h hh h' hh')).2 1 _ h0)
  · intro hGL x
    apply isPSD_zero
    intro h hh h' hh'
    by_cases hx : x ∈ R
    · rw [if_pos hx]
      have P := (hPars K R ψ hL h h' (hFF h hh h' hh') cr hcr).2
      rw [finsum_eq_single _ (0 : K ⧸ R.toAddSubgroup) (fun y hy => by
        by_contra h0; exact hy (hglr h h' (hGL h hh) y h0)),
        cSize_glr R h (hGL h hh), cSize_glr R h' (hGL h' hh')] at P
      have hx0 : (x : K ⧸ R.toAddSubgroup) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr hx
      simp only [Θ]
      rw [hx0, P]
      simp
    · rw [if_neg hx, zero_sub, neg_eq_zero]
      by_contra h0
      exact hx ((QuotientAddGroup.eq_zero_iff _).mp (hglr h h' (hGL h hh) _ h0))
end Formalism.FourierDecayAlt.P.A5x6
