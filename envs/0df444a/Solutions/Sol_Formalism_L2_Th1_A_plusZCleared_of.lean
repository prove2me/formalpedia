-- Prove2me | solution 1 for Formalism.L2.Th1.A.plusZCleared_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:07:33.538799+00:00
-- url     : https://prove2.me/submissions/74cafb05-8262-43e7-b76b-7763a3dfbae3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_XPowSuccDvdOfDerivative
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_Plus_toL_X_mul
import Theorems.Thm_Formalism_L2_Th1_A_Plus_uPow_neg_three
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_uPow_neg_three
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_dL_uPow
import Theorems.Thm_Formalism_L2_Th1_A_toL_injective
import Theorems.Thm_Formalism_L2_Th1_A_wpShape
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
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Nn
namespace Formalism.L2.Th1.A
theorem _root_.solution (hZ : PlusZ.{u}) (hT : TInZ.{u}) : PlusZCleared.{u} := by
  intro K _ _ W xP yP hP
  obtain ⟨-, -, hlog⟩ := hZ K W xP yP hP
  have hT' := hT K W xP
  have hsh := (wpShape K W).1
  set P := wpReg W with hPdef
  set c : K := xP + W.b₂ / 12 with hc
  set T := (tS W xP).subst (expSer W) with hTdef
  set xp := (xPlus W xP yP).subst (expSer W) with hxp
  set xm := (xPlus W xP (W.toAffine.negY xP yP)).subst (expSer W) with hxm
  set f : K⟦X⟧ := 1 + X ^ 2 * (P - C c) with hf
  have hf0 : constantCoeff f = 1 := by simp [hf]
  set g : K⟦X⟧ := invOfUnit f 1 with hg
  have hfg : f * g = 1 := mul_invOfUnit _ _ (by rw [hf0, Units.val_one])
  have hTf : T * f = X ^ 2 := by rw [← hT', hf]; ring
  have hTg : T = X ^ 2 * g := by linear_combination g * hTf - T * hfg
  have hdf : X * derivative K f = 2 * (f - 1) + X ^ 3 * derivative K P := by
    rw [hf]
    simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
      derivative_C, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hdg : derivative K g = -g ^ 2 * derivative K f := by
    have h := congrArg (derivative K) hfg
    rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at h
    linear_combination g * h - derivative K g * hfg
  have hz : (toL X : LaurentSeries K) * uPow (-1) = 1 := Plus.toL_X_mul
  have hxZ : xZ W = uPow (-2) + toL P - HahnSeries.C (W.b₂ / 12) := by
    rw [← hsh, wpL]; ring

  have hdwp : dL (wpL W) = uPow (-1) ^ 3 * (toL X * toL (derivative K f) - 2 * toL f) := by
    have h1 : toL X * toL (derivative K f) = 2 * (toL f - 1) + toL X ^ 3 * toL (derivative K P) := by
      rw [← map_mul, hdf]
      simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
    rw [hsh, map_add, dL_uPow, dL_toL, h1]
    have e3 : (uPow (-2 - 1) : LaurentSeries K) = uPow (-1) ^ 3 := by
      rw [← Plus.uPow_neg_three]; norm_num
    rw [e3]
    have e2 : (HahnSeries.C (((-2 : ℤ) : K)) : LaurentSeries K) = -2 := by
      push_cast
      rw [map_neg, map_ofNat]
    rw [e2]
    linear_combination (-toL (derivative K P)
      * ((toL X * uPow (-1)) ^ 2 + toL X * uPow (-1) + 1)) * hz
  have hprod : toL T * dL (wpL W) = toL (g * derivative K f) - 2 * uPow (-1) := by
    have hfg' : toL f * toL g = 1 := by rw [← map_mul, hfg, map_one]
    rw [hdwp, hTg, map_mul, map_mul, map_pow]
    linear_combination (toL g * toL (derivative K f) * ((toL X * uPow (-1)) ^ 2
        + toL X * uPow (-1) + 1) - 2 * toL g * toL f * uPow (-1) * (toL X * uPow (-1) + 1)) * hz
      - 2 * uPow (-1) * hfg'
  rw [hprod, map_sub, dL_toL, dL_mul, dL_uPow, hxZ] at hlog
  have e2' : (uPow (-1 - 1) : LaurentSeries K) = uPow (-2) := by norm_num
  have e1 : (HahnSeries.C (((-1 : ℤ) : K)) : LaurentSeries K) = -1 := by
    push_cast
    rw [map_neg, map_one]
  have d2 : dL (2 : LaurentSeries K) = 0 := by
    rw [← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 2, dL_C]
  rw [e2', e1, d2] at hlog
  have hmain : derivative K (g * derivative K f) = 2 * P - (xp + C (W.b₂ / 12))
      - (xm + C (W.b₂ / 12)) := by
    apply toL_injective
    simp only [map_add, map_sub, map_mul, map_ofNat, toL_C]
    linear_combination hlog
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hdg] at hmain
  rw [← hmain]
  linear_combination (-(derivative K (derivative K f)) * f
    + derivative K f ^ 2 * (f * g + 1)) * hfg
end Formalism.L2.Th1.A
