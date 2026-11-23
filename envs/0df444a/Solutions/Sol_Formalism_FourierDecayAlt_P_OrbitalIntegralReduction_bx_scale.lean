-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.bx_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:00.992995+00:00
-- url     : https://prove2.me/submissions/cf7ef5c2-08d5-4fbb-9c44-50a03b790151

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_reindex
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_mk_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_indep
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_lat_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_lat_mulLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_volL_mulLat
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
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (hD : LocalDatum K R ψ) {ι : Type} [Fintype ι] (a : Kˣ) {Λ Λ' : AddSubgroup K}
    (hΛ : IsLat Λ) (hΛ' : IsLat Λ') (f : (ι → K) → ℂ) (h : BInv Λ f)
    (h' : BInv Λ' (fun N => f ((a : K) • N))) :
    (modK R (a : K) : ℂ) ^ Fintype.card ι * bx R Λ' ι (fun N => f ((a : K) • N)) = bx R Λ ι f := by
  have hR := lat_R hD.isOpen hD.isCompact
  have hai : (a : K) * ((a⁻¹ : Kˣ) : K) = 1 := by simp
  have hia : ((a⁻¹ : Kˣ) : K) * (a : K) = 1 := by simp
  set Λ₂ : AddSubgroup K := mulLat ((a⁻¹ : Kˣ) : K) Λ with hΛ₂
  have hL2 : IsLat Λ₂ :=
    Formalism.FourierDecayAlt.P.A6x3.lat_iff.2 (Formalism.FourierDecayAlt.P.A6x3.lat_mulLat a⁻¹ (Formalism.FourierDecayAlt.P.A6x3.lat_iff.1 hΛ))
  have hmem : ∀ x : K, x ∈ Λ₂ ↔ (a : K) * x ∈ Λ := by
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      show (a : K) * (((a⁻¹ : Kˣ) : K) * w) ∈ Λ
      rw [← mul_assoc, hai, one_mul]; exact hw
    · intro hx
      exact ⟨_, hx, by
        show ((a⁻¹ : Kˣ) : K) * ((a : K) * x) = x
        rw [← mul_assoc, hia, one_mul]⟩
  have h2 : BInv Λ₂ (fun N : ι → K => f ((a : K) • N)) := by
    intro x l hl
    show f ((a : K) • (x + l)) = f ((a : K) • x)
    rw [smul_add]
    exact h _ _ (fun i => (hmem _).1 (hl i))
  rw [bx_indep hD hΛ' hL2 _ h' h2]
  have hsum : ∑ᶠ y : ι → K ⧸ Λ₂, f ((a : K) • fun i => (Quotient.out (y i) : K)) =
      ∑ᶠ y : ι → K ⧸ Λ, f (fun i => Quotient.out (y i)) := by
    have := tk_reindex (X := ι → K) (fun x i => ((x i : K) : K ⧸ Λ₂))
      (fun x i => (((a : K) * x i : K) : K ⧸ Λ)) (fun q i => (Quotient.out (q i) : K))
      (fun q i => ((a⁻¹ : Kˣ) : K) * (Quotient.out (q i) : K))
      (fun q => funext fun i => QuotientAddGroup.out_eq' _)
      (fun q => funext fun i => by
        show ((((a : K) * (((a⁻¹ : Kˣ) : K) * (Quotient.out (q i) : K)) : K)) : K ⧸ Λ) = q i
        rw [← mul_assoc, hai, one_mul]; exact QuotientAddGroup.out_eq' _)
      (fun x x' => by
        constructor
        · intro e
          funext i
          have := (tk_mk_eq Λ₂ _ _).1 (congrFun e i)
          refine (tk_mk_eq Λ _ _).2 ?_
          rw [← mul_sub]; exact (hmem _).1 this
        · intro e
          funext i
          have := (tk_mk_eq Λ _ _).1 (congrFun e i)
          refine (tk_mk_eq Λ₂ _ _).2 ((hmem _).2 ?_)
          rw [mul_sub]; exact this)
      (fun x => f ((a : K) • x))
      (fun x x' e => by
        have := h2 x' (x - x') (fun i => (tk_mk_eq Λ₂ _ _).1 (congrFun e i))
        simpa using this)
    rw [this]
    refine finsum_congr fun q => ?_
    congr 1
    funext i
    show (a : K) * (((a⁻¹ : Kˣ) : K) * (Quotient.out (q i) : K)) = _
    rw [← mul_assoc, hai, one_mul]
  unfold bx
  rw [hsum, hΛ₂, Formalism.FourierDecayAlt.P.A6x3.volL_mulLat hR a⁻¹ (Formalism.FourierDecayAlt.P.A6x3.lat_iff.1 hΛ)]
  have hm : modK R (a : K) * modK R ((a⁻¹ : Kˣ) : K) = 1 := by
    rw [← modK_mul hD.isOpen hD.isCompact a a⁻¹, hai, modK_one]
  have hm' : (modK R (a : K) : ℂ) * (modK R ((a⁻¹ : Kˣ) : K) : ℂ) = 1 := by exact_mod_cast hm
  push_cast
  rw [← mul_assoc, ← mul_pow, ← mul_assoc, hm', one_mul]
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
