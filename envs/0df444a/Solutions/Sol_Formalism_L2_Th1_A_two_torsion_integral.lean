-- Prove2me | solution 1 for Formalism.L2.Th1.A.two_torsion_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:09:56.843748+00:00
-- url     : https://prove2.me/submissions/0924076c-0340-4dbb-8ecc-c3e20bf2a060

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
import Theorems.Thm_Formalism_L2_Th1_A_two_torsion_unit
import Theorems.Thm_Formalism_L2_Th1_A_Two_tS_mul
import Theorems.Thm_Formalism_L2_Th1_A_Two_sq_dvd_tS
import Theorems.Thm_Formalism_L2_Th1_A_Two_coeff_two_tS
import Theorems.Thm_Formalism_L2_Th1_A_Two_tS_even
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_C
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_apply
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_Plus_coeff_two_tS
import Theorems.Thm_Formalism_L2_Th1_A_Plus_equation_C
import Theorems.Thm_Formalism_L2_Th1_A_Plus_subHom_C
import Theorems.Thm_Formalism_L2_Th1_A_Plus_subHom_apply
import Theorems.Thm_Formalism_L2_Th1_A_Wp_constCurve_dL
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_flowTwoTorsion
import Theorems.Thm_Formalism_L2_Th1_A_flowTwoTorsionWp
import Theorems.Thm_Formalism_L2_Th1_A_flowZ
import Theorems.Thm_Formalism_L2_Th1_A_toL_injective
import Theorems.Thm_P2M_Formalism_L2_Th1_A_Wp_isDer_dL__14cb087f2915
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Two
namespace Formalism.L2.Th1.A
theorem _root_.solution : TwoTorsionZ.{u} := by
  intro K _ _ W xT yT hT h2 e₁ kap w₁
  obtain ⟨he₁⟩ : Nonempty (e₁ = xT + W.b₂ / 12) := ⟨rfl⟩
  obtain ⟨hkap⟩ : Nonempty (kap = 3 * e₁ ^ 2 - g₂ W / 4) := ⟨rfl⟩
  obtain ⟨hw₁⟩ : Nonempty (w₁ = (tS W xT).subst (expSer W)) := ⟨rfl⟩
  clear_value w₁ kap e₁
  have hinj : Function.Injective (HahnSeries.C : K →+* LaurentSeries K) := HahnSeries.C_injective
  have cE : (HahnSeries.C e₁ : LaurentSeries K) = HahnSeries.C xT + HahnSeries.C (W.b₂ / 12) := by
    rw [he₁, map_add]
  have h6 : IsUnit (6 : LaurentSeries K) := by
    have h := (IsUnit.mk0 (6 : K) (by norm_num)).map (HahnSeries.C : K →+* LaurentSeries K)
    rwa [map_ofNat] at h
  have hb : 12 * (HahnSeries.C (W.b₂ / 12) : LaurentSeries K) = (curveL W).b₂ := by
    rw [WeierstrassCurve.map_b₂, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 12, ← map_mul]
    congr 1
    field_simp
  have hg2 : 12 * (HahnSeries.C (g₂ W) : LaurentSeries K) = (curveL W).c₄ := by
    rw [WeierstrassCurve.map_c₄, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 12, ← map_mul]
    congr 1
    rw [g₂]
    field_simp
  have hg3 : 216 * (HahnSeries.C (g₃ W) : LaurentSeries K) = (curveL W).c₆ := by
    rw [WeierstrassCurve.map_c₆, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 216, ← map_mul]
    congr 1
    rw [g₃]
    field_simp
  have hk : 4 * (HahnSeries.C kap : LaurentSeries K)
      = 12 * (HahnSeries.C xT + HahnSeries.C (W.b₂ / 12)) ^ 2 - HahnSeries.C (g₂ W) := by
    have h : 4 * kap = 12 * e₁ ^ 2 - g₂ W := by rw [hkap]; ring
    have h' := congrArg (HahnSeries.C : K →+* LaurentSeries K) h
    rw [← cE]
    simpa only [map_sub, map_mul, map_pow, map_ofNat] using h'
  have h2' : 2 * (HahnSeries.C yT : LaurentSeries K) + (curveL W).a₁ * HahnSeries.C xT
      + (curveL W).a₃ = 0 := by
    have h := congrArg (HahnSeries.C : K →+* LaurentSeries K) h2
    simpa only [map_add, map_mul, map_ofNat, map_zero, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃] using h
  have ht : toL w₁ * (xZ W - HahnSeries.C xT) = 1 := by rw [hw₁]; exact tS_mul W xT
  obtain ⟨p1, p2, -, p4, p5⟩ := flowTwoTorsionWp _ (curveL W) dL (xZ W) (yZ W) (HahnSeries.C xT)
    (HahnSeries.C yT) (toL w₁) (HahnSeries.C (W.b₂ / 12)) (HahnSeries.C (g₂ W))
    (HahnSeries.C (g₃ W)) (HahnSeries.C kap) Wp.isDer_dL' (Wp.constCurve_dL W) (flowZ K W).1
    (Plus.equation_C W hT) (dL_C _) (dL_C _) h2' ht h6 hb hg2 hg3 hk
  obtain ⟨-, -, s3⟩ := flowTwoTorsion _ (curveL W) dL (xZ W) (yZ W) (HahnSeries.C xT)
    (HahnSeries.C yT) (toL w₁) Wp.isDer_dL' (Wp.constCurve_dL W) (flowZ K W).1
    (Plus.equation_C W hT) (dL_C _) (dL_C _) h2' ht
  rw [← cE] at p1 p4 p5
  rw [← p2, ← hb, dL_toL, dL_toL] at s3
  rw [dL_toL] at p4 p5
  have q1 : 4 * e₁ ^ 3 - g₂ W * e₁ - g₃ W = 0 := by
    apply hinj
    simpa only [map_sub, map_mul, map_pow, map_ofNat, map_zero] using p1
  have q3 : kap = 3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT := by
    apply hinj
    simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄] using p2
  refine ⟨q1, ?_, q3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hg3' : g₃ W = 4 * e₁ ^ 3 - g₂ W * e₁ := by linear_combination -q1
    have h4 : (4 : Polynomial K) * Polynomial.C (g₂ W / 4) = Polynomial.C (g₂ W) := by
      rw [← map_ofNat (Polynomial.C : K →+* Polynomial K) 4, ← map_mul]
      congr 1
      field_simp
    rw [hg3']
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    linear_combination (Polynomial.X - Polynomial.C e₁) * h4
  · rw [wpL, cE]
    linear_combination ht
  · rw [hw₁]; exact sq_dvd_tS W xT
  · rw [hw₁]; exact coeff_two_tS W xT
  · rw [hw₁]; exact tS_even W xT
  · apply toL_injective
    simpa only [map_add, map_mul, map_pow, map_one, map_ofNat, toL_C] using p4
  · apply toL_injective
    simp only [map_add, map_mul, map_pow, map_ofNat, toL_C]
    rw [s3, cE]
    ring
  · rw [(two_torsion_unit K W xT yT hT h2).1, ← q3, subst_add (he W), subst_mul (he W), ← hw₁,
      ← ISer.subHom_apply _ (e0 W), ← ISer.subHom_apply _ (e0 W), ISer.subHom_C, ISer.subHom_C,
      he₁, map_add]
    ring
  · intro e₂ e₃ hf
    have v0 := congrArg (Polynomial.eval 0) hf
    have v1 := congrArg (Polynomial.eval 1) hf
    have vm := congrArg (Polynomial.eval (-1)) hf
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_ofNat] at v0 v1 vm
    have s1 : e₁ + e₂ + e₃ = 0 := by linear_combination (1 / 8) * (v1 + vm - 2 * v0)
    have s2 : 4 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) = -g₂ W := by
      linear_combination (-1 / 2) * (v1 - vm)
    refine ⟨by rw [hkap]; linear_combination 2 * e₁ * s1 - (1 / 4) * s2, ?_⟩
    have p := p5 (HahnSeries.C e₂) (HahnSeries.C e₃)
      (by rw [← map_add, ← map_add, s1, map_zero])
      (by
        have h := congrArg (HahnSeries.C : K →+* LaurentSeries K) s2
        simpa only [map_add, map_mul, map_neg, map_ofNat] using h)
    apply toL_injective
    simpa only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, toL_C] using p
end Formalism.L2.Th1.A
