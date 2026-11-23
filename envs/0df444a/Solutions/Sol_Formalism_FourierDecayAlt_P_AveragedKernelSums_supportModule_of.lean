-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AveragedKernelSums.supportModule_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:55.632736+00:00
-- url     : https://prove2.me/submissions/a688a47f-17b0-405b-80f4-e732cd8f379d

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_glr_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_pt_det_isUnit
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
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.AveragedKernelSums
open Formalism.FourierDecayAlt.P.A5x6
namespace Formalism.FourierDecayAlt.P.AveragedKernelSums
theorem _root_.solution (hSup : NsSupport) (K : Type) [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (R : Subring K) (ψ : AddChar K ℂ) (hL : LocalDatum K R ψ) (s : ℕ)
    (F : Finset (Point K)) (hs : 1 ≤ s) :
    ∃ Lc : Submodule R K, IsCutModule R ψ s F Lc ∧
      ((∀ h ∈ F, InGLR R h) → ∀ x, x ∈ Lc ↔ x ∈ R) := by
  classical
  obtain ⟨ϖ, hϖ, hϖx⟩ := hL.unif
  have hN : ∃ N : ℕ, (∀ h ∈ F, (ϖ : K) ^ N * (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) ∈ R) ∧
      ((∀ h ∈ F, InGLR R h) → N = 0) := by
    by_cases hG : ∀ h ∈ F, InGLR R h
    · refine ⟨0, fun h hh => ?_, fun _ => rfl⟩
      obtain ⟨_, h2, h3⟩ := glr_det R h (hG h hh)
      have e2 : (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) * (pt h.1 h.2).det = 1 :=
        IsUnit.val_inv_mul (pt_det_isUnit h)
      have e : (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) = (pt h.1 h.2)⁻¹.det := by
        calc (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K)
            = (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) *
                ((pt h.1 h.2).det * (pt h.1 h.2)⁻¹.det) := by rw [h3, mul_one]
          _ = (pt h.1 h.2)⁻¹.det := by rw [← mul_assoc, e2, one_mul]
      rw [pow_zero, one_mul, e]; exact h2
    · choose M hM using fun h : Point K => hϖx (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K)
      refine ⟨F.sup M, fun h hh => ?_, fun h => absurd h hG⟩
      have hle : M h ≤ F.sup M := Finset.le_sup (f := M) hh
      have e3 : (ϖ : K) ^ (F.sup M) = (ϖ : K) ^ (F.sup M - M h) * (ϖ : K) ^ M h := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      rw [e3, mul_assoc]; exact R.mul_mem (R.pow_mem hϖ _) (hM h)
  obtain ⟨N, hN1, hN2⟩ := hN
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
  refine ⟨L, ⟨?_, ?_, fun r hr => R.mul_mem (R.pow_mem hϖ N) hr, ?_⟩, ?_⟩
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
  · intro t ht h hh h' _
    by_contra h0
    apply ht
    have h4 := (hSup K R ψ s hs h h' t t h0).1
    show (ϖ : K) ^ N * (t : K) ∈ R
    have e2 : (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) * (pt h.1 h.2).det = 1 :=
      IsUnit.val_inv_mul (pt_det_isUnit h)
    have e : (ϖ : K) ^ N * (t : K) = ((ϖ : K) ^ N * (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K)) *
        ((pt h.1 h.2).det * (t : K)) := by
      calc (ϖ : K) ^ N * (t : K) = (ϖ : K) ^ N * ((((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) *
            (pt h.1 h.2).det) * (t : K) := by rw [e2, mul_one]
        _ = _ := by ring
    rw [e]
    exact R.mul_mem (hN1 h hh) h4
  · intro hG x
    show (ϖ : K) ^ N * x ∈ R ↔ x ∈ R
    rw [hN2 hG, pow_zero, one_mul]
end Formalism.FourierDecayAlt.P.AveragedKernelSums
