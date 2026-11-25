-- Prove2me | solution 1 for Formalism.ELL.chordDeterminantFactor_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:51.835864+00:00
-- url     : https://prove2.me/submissions/082c96c9-de2a-43ca-917b-2df821115763

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_G_sub
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_line_fact
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_q_fact
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_det_rows
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_Hv_mem
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_mem_TT
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_inv_mem_TT
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_X_mem_TT
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_psubst_mem
import Theorems.Thm_P2M_Formalism_ELL_CubeThreeAlt_weq_iff__f07a8575c07b
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_Ca_mem
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_w_eq
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_wU_cc
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_wU_coeff_mem
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_pair
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_lit_facts
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_G_inv
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_chord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constantCoeff_formalSum
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lineCoeffCubic_mem
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lineCoeffQuadratic_mem
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_w_coeff_mem
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_eq_of_xy
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_subst_w
import Theorems.Thm_Formalism_ELL_wSeriesSubstUnique_holds
import Theorems.Thm_P2M_Formalism_ELL_WeierstrassCoordinateSubstitution_X_ne_zero__047225846678


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open CubeThreeAlt WeierstrassChordSeries
set_option maxHeartbeats 4000000
namespace Formalism.ELL
theorem _root_.solution : CubeThree.{u} := by
  intro K _ W w F hw hF0 hch
  have hU := wSeriesSubstUnique_holds.{u}
  have hwu := w_eq hw
  have hu1 := wU_cc hw
  have hFF : F = F2 W w := WeierstrassCoordinateSubstitution.eq_of_xy hwu hu1 F (F2 W w) hF0 (constantCoeff_formalSum hw)
    (hch.1.trans (chord hU hw).1.symm) (hch.2.trans (chord hU hw).2.symm)
  subst hFF
  dsimp only
  have : IsDomain (MvPowerSeries (Fin 3) K) := NoZeroDivisors.to_isDomain _
  have hUc : ∀ i : Fin 3, MvPowerSeries.constantCoeff
      ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K)) = 1 := by
    intro i
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst_single]
    simp [hu1]
  have hUV : ∀ i : Fin 3, (wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) *
      ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))⁻¹ = 1 :=
    fun i => MvPowerSeries.mul_inv_cancel _ (by rw [hUc]; exact one_ne_zero)
  have hVc : ∀ i : Fin 3, MvPowerSeries.constantCoeff
      (((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))⁻¹) = 1 := by
    intro i; rw [MvPowerSeries.constantCoeff_inv, hUc, inv_one]
  have h3 : ∀ i : Fin 3, (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) ^ 3 =
      ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))⁻¹ *
        w.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) := by
    intro i
    rw [WeierstrassCoordinateSubstitution.subst_w hwu _ (by simp)]
    linear_combination (-(MvPowerSeries.X i : MvPowerSeries (Fin 3) K) ^ 3) * hUV i
  have hdet := det_rows (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))
    (fun i => ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))⁻¹)
    (fun i => w.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K)) h3
  rw [hdet]
  have hV0c := hVc 0
  have hV1c := hVc 1
  have hV2c := hVc 2
  have hU0m : (wU w).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ∈ TT W (Fin 3) :=
    psubst_mem (wU_coeff_mem hw) (X_mem_TT 0) (by simp)
  have hU1m : (wU w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) ∈ TT W (Fin 3) :=
    psubst_mem (wU_coeff_mem hw) (X_mem_TT 1) (by simp)
  have hU2m : (wU w).subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ∈ TT W (Fin 3) :=
    psubst_mem (wU_coeff_mem hw) (X_mem_TT 2) (by simp)
  have hVm : ∀ i : Fin 3, (wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) ∈ TT W (Fin 3) →
      ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))⁻¹ ∈ TT W (Fin 3) :=
    fun i h => inv_mem_TT h (by rw [hUc]; exact one_ne_zero)
      (by rw [hUc, inv_one]; exact Subalgebra.one_mem _)
  have hV0m := hVm 0 hU0m
  have hV1m := hVm 1 hU1m
  have hV2m := hVm 2 hU2m
  obtain ⟨hsne, hsX2, hX01⟩ := lit_facts hw
  set X0 : MvPowerSeries (Fin 3) K := MvPowerSeries.X 0 with hX0
  set X1 : MvPowerSeries (Fin 3) K := MvPowerSeries.X 1 with hX1
  set X2 : MvPowerSeries (Fin 3) K := MvPowerSeries.X 2 with hX2
  set V0 := ((wU w).subst X0)⁻¹ with hV0
  set V1 := ((wU w).subst X1)⁻¹ with hV1
  set V2 := ((wU w).subst X2)⁻¹ with hV2
  set w0 := w.subst X0 with hw0d
  set w1 := w.subst X1 with hw1d
  set w2 := w.subst X2 with hw2d
  have k0 : MvPowerSeries.constantCoeff X0 = 0 := by simp [hX0]
  have k1 : MvPowerSeries.constantCoeff X1 = 0 := by simp [hX1]
  have k2 : MvPowerSeries.constantCoeff X2 = 0 := by simp [hX2]
  have m0 : X0 ∈ TT W (Fin 3) := X_mem_TT 0
  have m1 : X1 ∈ TT W (Fin 3) := X_mem_TT 1
  have m2 : X2 ∈ TT W (Fin 3) := X_mem_TT 2
  have hX2ne : X2 ≠ 0 := WeierstrassCoordinateSubstitution.X_ne_zero' 2
  obtain ⟨mA1, mA2, mA3, mA4, mA6⟩ := Ca_mem (W := W) (σ := Fin 3)
  have hUs := fun (s : MvPowerSeries (Fin 3) K) (hs : MvPowerSeries.constantCoeff s = 0) =>
    hU K W w hw (Fin 3) s hs
  have hGw : ∀ s, MvPowerSeries.constantCoeff s = 0 → GG W s (w.subst s) = 0 :=
    fun s hs => (weq_iff' W _ _).mp (hUs s hs).1
  have huniq : ∀ s v, MvPowerSeries.constantCoeff s = 0 → MvPowerSeries.constantCoeff v = 0 →
      GG W s v = 0 → w.subst s = v :=
    fun s v hs hv hG => ((hUs s hs).2 v hv ((weq_iff' W _ _).mpr hG)).symm
  have hwcc : ∀ s : MvPowerSeries (Fin 3) K, MvPowerSeries.constantCoeff s = 0 →
      MvPowerSeries.constantCoeff (w.subst s) = 0 :=
    fun s hs => PowerSeries.constantCoeff_subst_eq_zero hs w hw.1
  have hwm : ∀ s, s ∈ TT W (Fin 3) → MvPowerSeries.constantCoeff s = 0 →
      w.subst s ∈ TT W (Fin 3) := fun s h h0 => psubst_mem (w_coeff_mem hw) h h0
  have hw0c : MvPowerSeries.constantCoeff w0 = 0 := hwcc X0 k0
  have hw1c : MvPowerSeries.constantCoeff w1 = 0 := hwcc X1 k1
  have hw2c : MvPowerSeries.constantCoeff w2 = 0 := hwcc X2 k2
  have hG0 : GG W X0 w0 = 0 := hGw X0 k0
  have hG1 : GG W X1 w1 = 0 := hGw X1 k1
  have hG2 : GG W X2 w2 = 0 := hGw X2 k2

  obtain ⟨l1, n1, u, A1, B1, hl1, hn1, hA1, hz1, hB1, hs1, hl1c, hl1m, hA1m, hB1m⟩ :=
    pair hw X0 X1 k0 k1 m0 m1
  set s := MvPowerSeries.subst ![X0, X1] (F2 W w) with hsdef
  have hn1c : MvPowerSeries.constantCoeff n1 = 0 := by rw [hn1]; simp [hwcc X0 k0, hl1c, k0]
  have hn1m : n1 ∈ TT W (Fin 3) := by
    rw [hn1]; exact (TT W _).sub_mem (hwm X0 m0 k0) ((TT W _).mul_mem hl1m m0)
  have huc : MvPowerSeries.constantCoeff u = 0 := by
    rw [hz1]; simp [chordCoeffQuadraticAt, WeierstrassChordSeries.c2, hl1c, hn1c, k0, k1]
  have hum : u ∈ TT W (Fin 3) := by
    rw [hz1]
    exact (TT W _).sub_mem ((TT W _).sub_mem ((TT W _).neg_mem m0) m1)
      ((TT W _).mul_mem (lineCoeffQuadratic_mem _ mA1 mA2 mA3 mA4 mA6 hl1m hn1m) hA1m)
  have hsc : MvPowerSeries.constantCoeff s = 0 := by rw [hs1]; simp [huc]
  have hsm : s ∈ TT W (Fin 3) := by rw [hs1]; exact (TT W _).mul_mem hum hB1m
  have hw0 : w0 = l1 * X0 + n1 := by rw [hn1]; ring
  have hw1 : w1 = l1 * X1 + n1 := by rw [hn1]; linear_combination -hl1
  have he1 : chordCoeffCubicAt W l1 * (X0 + X1 + u) + chordCoeffQuadraticAt W l1 n1 = 0 := by
    rw [hz1]; linear_combination (-(chordCoeffQuadraticAt W l1 n1)) * hA1
  have line1 := line_fact hX01 (by rw [← hw0]; exact hG0) (by rw [← hw1]; exact hG1) he1
  have hGu : GG W u (l1 * u + n1) = 0 := by
    have h := line1 u; rw [sub_self, mul_zero] at h; exact h
  have huw : w.subst u = l1 * u + n1 :=
    huniq u _ huc (by simp [hl1c, huc, hn1c]) hGu
  set dd1 := DDs W l1 n1 u with hdd1
  have hdd1c : MvPowerSeries.constantCoeff dd1 = -1 := by simp [hdd1, DDs, huc, hl1c, hn1c]
  have hdd10 : dd1 ≠ 0 := fun h => by simp [h] at hdd1c
  have hsd : s * dd1 = u := by rw [hs1]; linear_combination u * hB1
  have hune : u ≠ 0 := by rw [← hsd]; exact mul_ne_zero hsne hdd10
  have hGs' : GG W s ((l1 * u + n1) * B1) = 0 :=
    G_inv hsd (by linear_combination (l1 * u + n1) * hB1) rfl hdd10 hGu
  have hws : w.subst s = (l1 * u + n1) * B1 :=
    huniq s _ hsc (by simp [hl1c, huc, hn1c]) hGs'
  set lam0 := u ^ 2 * (wU w).subst u with hlam0
  have hlam0c : MvPowerSeries.constantCoeff lam0 = 0 := by simp [hlam0, huc]
  have hlam0m : lam0 ∈ TT W (Fin 3) :=
    (TT W _).mul_mem ((TT W _).pow_mem hum 2) (psubst_mem (wU_coeff_mem hw) hum huc)
  have hl0 : l1 * u + n1 = lam0 * u := by
    rw [← huw, WeierstrassCoordinateSubstitution.subst_w hwu u huc, hlam0]; ring
  have hws' : w.subst s = lam0 * s := by
    rw [hws, hl0, hs1]; ring

  have hq := q_fact (a2 := MvPowerSeries.C W.a₂) (a4 := MvPowerSeries.C W.a₄)
    (a6 := MvPowerSeries.C W.a₆) (c := X2) hune hdd10 hsd
    (by rw [hdd1, DDs, hl0]) (by rw [← hl0]; exact hGu)

  obtain ⟨l2, n2, r, A2, B2, hl2, hn2, hA2, hz2, hB2, hs2, hl2c, hl2m, hA2m, hB2m⟩ :=
    pair hw s X2 hsc k2 hsm m2
  set F3 := MvPowerSeries.subst ![s, X2] (F2 W w) with hF3
  have hwsc : MvPowerSeries.constantCoeff (w.subst s) = 0 := hwcc s hsc
  have hn2c : MvPowerSeries.constantCoeff n2 = 0 := by rw [hn2]; simp [hwsc, hl2c, hsc]
  have hn2m : n2 ∈ TT W (Fin 3) := by
    rw [hn2]; exact (TT W _).sub_mem (hwm s hsm hsc) ((TT W _).mul_mem hl2m hsm)
  have hrc : MvPowerSeries.constantCoeff r = 0 := by
    rw [hz2]; simp [chordCoeffQuadraticAt, WeierstrassChordSeries.c2, hl2c, hn2c, hsc, k2]
  have hrm : r ∈ TT W (Fin 3) := by
    rw [hz2]
    exact (TT W _).sub_mem ((TT W _).sub_mem ((TT W _).neg_mem hsm) m2)
      ((TT W _).mul_mem (lineCoeffQuadratic_mem _ mA1 mA2 mA3 mA4 mA6 hl2m hn2m) hA2m)
  have hws2 : w.subst s = l2 * s + n2 := by rw [hn2]; ring
  have hw2 : w2 = l2 * X2 + n2 := by rw [hn2]; linear_combination -hl2
  have he2 : chordCoeffCubicAt W l2 * (s + X2 + r) + chordCoeffQuadraticAt W l2 n2 = 0 := by
    rw [hz2]; linear_combination (-(chordCoeffQuadraticAt W l2 n2)) * hA2
  have line2 := line_fact hsX2 (by rw [← hws2]; exact hGw s hsc) (by rw [← hw2]; exact hG2) he2
  set N := 1 - MvPowerSeries.C W.a₃ * n2 - MvPowerSeries.C W.a₆ * n2 ^ 2 with hN
  have hv : n2 * N = chordCoeffCubicAt W l2 * s * X2 * r := by
    have h := line2 0
    simp only [G] at h
    rw [hN]; unfold chordCoeffCubicAt
    linear_combination -h
  set H1 := HHs W X2 (l1 * X2 + n1) w2 with hH1
  set H0 := HHs W X2 (lam0 * X2) w2 with hH0
  have hE1 : (l1 * X2 + n1 - w2) * H1 = chordCoeffCubicAt W l1 * (X2 - X0) * (X2 - X1) * (X2 - u) := by
    have h := G_sub (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃)
      (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) X2 (l1 * X2 + n1) w2
    have hG2' : G (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃)
      (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) X2 w2 = 0 := hG2
    rw [hG2', line1 X2, sub_zero] at h
    rw [hH1]; unfold HHs chordCoeffCubicAt; exact h.symm
  have hE0 : (lam0 * X2 - w2) * H0 = X2 * chordCoeffCubicAt W lam0 * (X2 - u) * (X2 - s) := by
    have h := G_sub (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃)
      (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) X2 (lam0 * X2) w2
    have hG2' : G (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃)
      (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) X2 w2 = 0 := hG2
    rw [hG2', hq, sub_zero] at h
    rw [hH0]; unfold HHs chordCoeffCubicAt; exact h.symm
  have hnu : (X2 - s) * n2 = s * (lam0 * X2 - w2) := by
    linear_combination (X2 - s) * hn2 - s * hl2 + X2 * hws'
  have hK : (X2 - s) * s * X2 * (chordCoeffCubicAt W l2 * r * H0 - chordCoeffCubicAt W lam0 * (X2 - u) * N) = 0 := by
    linear_combination (-(X2 - s) * H0) * hv + (N * H0) * hnu + (N * s) * hE0
  have hK' : chordCoeffCubicAt W l2 * r * H0 = chordCoeffCubicAt W lam0 * (X2 - u) * N := by
    have hne : (X2 - s) * s * X2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hsX2)) hsne) hX2ne
    exact sub_eq_zero.mp ((mul_eq_zero.mp hK).resolve_left hne)
  set dd2 := DDs W l2 n2 r with hdd2
  have hr : r = F3 * dd2 := by rw [hs2]; linear_combination -r * hB2

  have hH1c : MvPowerSeries.constantCoeff H1 = -1 := by
    simp [hH1, HHs, Hv, k2, hl1c, hn1c, hw2c]
  have hH0c : MvPowerSeries.constantCoeff H0 = -1 := by
    simp [hH0, HHs, Hv, k2, hlam0c, hw2c]
  have hNc : MvPowerSeries.constantCoeff N = 1 := by simp [hN, hn2c]
  have hC30c : MvPowerSeries.constantCoeff (chordCoeffCubicAt W lam0) = 1 := by simp [chordCoeffCubicAt, c3, hlam0c]
  have hPc : MvPowerSeries.constantCoeff (H1 * chordCoeffCubicAt W lam0 * N) = -1 := by
    simp [hH1c, hC30c, hNc]
  set Y := (H1 * chordCoeffCubicAt W lam0 * N)⁻¹ with hYd
  have hY : H1 * chordCoeffCubicAt W lam0 * N * Y = 1 :=
    MvPowerSeries.mul_inv_cancel _ (by rw [hPc]; exact neg_ne_zero.mpr one_ne_zero)
  have hPm : H1 * chordCoeffCubicAt W lam0 * N ∈ TT W (Fin 3) := by
    refine (TT W _).mul_mem ((TT W _).mul_mem ?_ (lineCoeffCubic_mem _ mA2 mA4 mA6 hlam0m)) ?_
    · exact Hv_mem _ mA1 mA2 mA3 mA4 mA6 m2 ((TT W _).add_mem ((TT W _).mul_mem hl1m m2) hn1m)
        (hwm X2 m2 k2)
    · exact (TT W _).sub_mem ((TT W _).sub_mem (TT W _).one_mem ((TT W _).mul_mem mA3 hn2m))
        ((TT W _).mul_mem mA6 ((TT W _).pow_mem hn2m 2))
  have hYm : Y ∈ TT W (Fin 3) :=
    inv_mem_TT hPm (by rw [hPc]; exact neg_ne_zero.mpr one_ne_zero)
      (by rw [hPc, inv_neg, inv_one]; exact Subalgebra.neg_mem _ (Subalgebra.one_mem _))
  have hC31c : MvPowerSeries.constantCoeff (chordCoeffCubicAt W l1) = 1 := by simp [chordCoeffCubicAt, c3, hl1c]
  have hC32c : MvPowerSeries.constantCoeff (chordCoeffCubicAt W l2) = 1 := by simp [chordCoeffCubicAt, c3, hl2c]
  have hdd2c : MvPowerSeries.constantCoeff dd2 = -1 := by simp [hdd2, DDs, hrc, hl2c, hn2c]
  refine ⟨V0 * V1 * V2 * chordCoeffCubicAt W l1 * chordCoeffCubicAt W l2 * dd2 * H0 * Y, ?_, ?_, ?_⟩
  · have hm : V0 * V1 * V2 * chordCoeffCubicAt W l1 * chordCoeffCubicAt W l2 * dd2 * H0 * Y ∈ TT W (Fin 3) := by
      refine (TT W _).mul_mem ((TT W _).mul_mem ((TT W _).mul_mem ((TT W _).mul_mem
        ((TT W _).mul_mem ((TT W _).mul_mem ((TT W _).mul_mem hV0m hV1m) hV2m)
        (lineCoeffCubic_mem _ mA2 mA4 mA6 hl1m)) (lineCoeffCubic_mem _ mA2 mA4 mA6 hl2m)) ?_) ?_) hYm
      · simp only [hdd2, DDs]
        exact (TT W _).add_mem ((TT W _).add_mem ((TT W _).neg_mem (TT W _).one_mem)
          ((TT W _).mul_mem mA1 hrm)) ((TT W _).mul_mem mA3
            ((TT W _).add_mem ((TT W _).mul_mem hl2m hrm) hn2m))
      · exact Hv_mem _ mA1 mA2 mA3 mA4 mA6 m2 ((TT W _).mul_mem hlam0m m2) (hwm X2 m2 k2)
    exact mem_TT.mp hm
  · rw [hYd]
    simp only [map_mul, hV0c, hV1c, hV2c, hC31c, hC32c, hdd2c, hH0c,
      MvPowerSeries.constantCoeff_inv, hPc]
    norm_num
  · have step1 : -(V0 * V1 * V2) * ((w1 - w0) * (X2 - X0) - (w2 - w0) * (X1 - X0))
        = -(V0 * V1 * V2) * (X1 - X0) * (l1 * X2 + n1 - w2) := by
      rw [hw0, hw1]; ring
    rw [step1]
    linear_combination (V0 * V1 * V2 * (X1 - X0) * (l1 * X2 + n1 - w2)) * hY
      + (-Y * (V0 * V1 * V2) * (X1 - X0) * chordCoeffCubicAt W lam0 * N) * hE1
      + (Y * (V0 * V1 * V2) * (X1 - X0) * chordCoeffCubicAt W l1 * (X2 - X0) * (X2 - X1)) * hK'
      + (-Y * (V0 * V1 * V2) * (X1 - X0) * chordCoeffCubicAt W l1 * (X2 - X0) * (X2 - X1) * chordCoeffCubicAt W l2 * H0) * hr
end Formalism.ELL
