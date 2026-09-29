-- Prove2me | solution 1 for Complex.integral_radial_loop_eq_two_mul_I_mul_setIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/263a2867-85fc-59aa-850a-70c180415e61

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_integral_radial_loop_eq_two_mul_I_mul_setIntegral

namespace RadialGreen

open Complex MeasureTheory Set Filter intervalIntegral
open scoped Real Topology Interval

theorem clm_decomp (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    L w = (w.re : ℂ) * L 1 + (w.im : ℂ) * L I := by
  have hw : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • I := by
    rw [real_smul, real_smul, mul_one]; exact (re_add_im w).symm
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul, real_smul, real_smul]

theorem clm_real_mul (L : ℂ →L[ℝ] ℂ) (t : ℝ) (w : ℂ) : L ((t : ℂ) * w) = (t : ℂ) * L w := by
  rw [← real_smul, map_smul, real_smul]

theorem clm_wirtinger_bar (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    I * L w - L (I * w) = 2 * I * (starRingEnd ℂ) w * ((L 1 + I * L I) / 2) := by
  rw [clm_decomp L w, clm_decomp L (I * w)]
  have h1 : ((I * w).re : ℂ) = -(w.im : ℂ) := by simp
  have h2 : ((I * w).im : ℂ) = (w.re : ℂ) := by simp
  have h3 : (starRingEnd ℂ) w = (w.re : ℂ) - (w.im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [h1, h2, h3]
  linear_combination (-(w.re : ℂ) * L I + (w.im : ℂ) * L 1 + I * (w.im : ℂ) * L I) * I_sq

theorem clm_wirtinger (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    I * L w + L (I * w) = 2 * I * w * ((L 1 - I * L I) / 2) := by
  rw [clm_decomp L w, clm_decomp L (I * w)]
  have h1 : ((I * w).re : ℂ) = -(w.im : ℂ) := by simp
  have h2 : ((I * w).im : ℂ) = (w.re : ℂ) := by simp
  have h3 : w = (w.re : ℂ) + (w.im : ℂ) * I := (re_add_im w).symm
  rw [h1, h2]
  conv_rhs => rw [h3]
  linear_combination ((w.re : ℂ) * L I - (w.im : ℂ) * L 1 + I * (w.im : ℂ) * L I) * I_sq

noncomputable def u (φ : ℝ) : ℂ := exp (φ * I)

noncomputable def ub (φ : ℝ) : ℂ := exp (-(φ * I))

theorem u_mul_ub (φ : ℝ) : u φ * ub φ = 1 := by
  rw [u, ub, ← exp_add, add_neg_cancel, exp_zero]

theorem conj_u (φ : ℝ) : (starRingEnd ℂ) (u φ) = ub φ := by
  rw [u, ub, ← exp_conj, map_mul, conj_ofReal, conj_I, mul_neg]

theorem norm_u (φ : ℝ) : ‖u φ‖ = 1 := norm_exp_ofReal_mul_I φ

theorem u_ne_zero (φ : ℝ) : u φ ≠ 0 := exp_ne_zero _

theorem continuous_u : Continuous u := by unfold u; fun_prop

theorem continuous_ub : Continuous ub := by unfold ub; fun_prop

theorem hasDerivAt_u (φ : ℝ) : HasDerivAt u (u φ * I) φ := by
  have h : HasDerivAt (fun x : ℝ => (x : ℂ) * I) (1 * I) φ := (hasDerivAt_id φ).ofReal_comp.mul_const I
  have := (Complex.hasDerivAt_exp ((φ : ℂ) * I)).comp φ h
  simp [u, one_mul] at this
  exact this

theorem hasDerivAt_ub (φ : ℝ) : HasDerivAt ub (ub φ * (-I)) φ := by
  have h : HasDerivAt (fun x : ℝ => -((x : ℂ) * I)) (-(1 * I)) φ :=
    ((hasDerivAt_id φ).ofReal_comp.mul_const I).neg
  have := (Complex.hasDerivAt_exp (-((φ : ℂ) * I))).comp φ h
  simp [ub, one_mul] at this ⊢
  exact this

theorem u_add_two_pi (φ : ℝ) : u (φ + 2 * π) = u φ := by
  rw [u, u, ofReal_add, add_mul, exp_add]
  have : exp (((2 * π : ℝ) : ℂ) * I) = 1 := by
    rw [show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring]
    exact exp_two_pi_mul_I
  rw [this, mul_one]

theorem ub_add_two_pi (φ : ℝ) : ub (φ + 2 * π) = ub φ := by
  rw [← conj_u, ← conj_u, u_add_two_pi]

theorem conj_coef_mul_u (x y φ : ℝ) :
    (starRingEnd ℂ) (((x : ℂ) + (y : ℂ) * I) * u φ) = ((x : ℂ) - (y : ℂ) * I) * ub φ := by
  rw [map_mul, conj_u, map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
  ring

theorem periodic_apply_arg {r : ℝ → ℝ} (hper : Function.Periodic r (2 * π)) {t : ℝ} (ht : 0 < t)
    (φ : ℝ) : r (arg ((t : ℂ) * u φ)) = r φ := by
  rw [arg_real_mul _ ht, u, arg_exp_mul_I, toIocMod]
  exact hper.sub_zsmul_eq _

section Setting

variable (c : ℂ) (r : ℝ → ℝ) (P Q : ℂ → ℂ)

noncomputable def Ψ (φ s : ℝ) : ℂ := c + (s : ℂ) * (r φ : ℂ) * u φ

noncomputable def sc (s : ℝ) : ℝ := (projIcc (0 : ℝ) 1 zero_le_one s : ℝ)

theorem sc_of_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : sc s = s := by
  rw [sc, projIcc_of_mem _ hs]

theorem sc_mem (s : ℝ) : sc s ∈ Icc (0 : ℝ) 1 := (projIcc 0 1 zero_le_one s).2

theorem continuous_sc : Continuous sc := continuous_subtype_val.comp continuous_projIcc

noncomputable def Ψc (φ s : ℝ) : ℂ := Ψ c r φ (sc s)

noncomputable def g (z : ℂ) : ℂ :=
  (fderiv ℝ P z 1 + I * fderiv ℝ P z I) / 2 - (fderiv ℝ Q z 1 - I * fderiv ℝ Q z I) / 2

noncomputable def A (φ s : ℝ) : ℂ :=
  (P (Ψc c r φ s) * u φ + Q (Ψc c r φ s) * ub φ) * r φ

noncomputable def rd (a b : ℝ) (hab : a ≤ b) (φ : ℝ) : ℝ :=
  derivWithin r (Icc a b) (projIcc a b hab φ : ℝ)

noncomputable def Aφ (a b : ℝ) (hab : a ≤ b) (φ s : ℝ) : ℂ :=
  (fderiv ℝ P (Ψc c r φ s) ((sc s : ℂ) * ((rd r a b hab φ : ℂ) + (r φ : ℂ) * I) * u φ) * u φ +
      P (Ψc c r φ s) * (u φ * I) +
      fderiv ℝ Q (Ψc c r φ s) ((sc s : ℂ) * ((rd r a b hab φ : ℂ) + (r φ : ℂ) * I) * u φ) * ub φ +
      Q (Ψc c r φ s) * (ub φ * (-I))) * r φ +
    (P (Ψc c r φ s) * u φ + Q (Ψc c r φ s) * ub φ) * rd r a b hab φ

noncomputable def B (a b : ℝ) (hab : a ≤ b) (φ s : ℝ) : ℂ :=
  P (Ψ c r φ s) * (s : ℂ) * (((rd r a b hab φ : ℂ) + (r φ : ℂ) * I) * u φ) +
    Q (Ψ c r φ s) * (s : ℂ) * (((rd r a b hab φ : ℂ) - (r φ : ℂ) * I) * ub φ)

noncomputable def Bs (a b : ℝ) (hab : a ≤ b) (φ s : ℝ) : ℂ :=
  (fderiv ℝ P (Ψ c r φ s) ((r φ : ℂ) * u φ) * (s : ℂ) + P (Ψ c r φ s) * 1) *
      (((rd r a b hab φ : ℂ) + (r φ : ℂ) * I) * u φ) +
    (fderiv ℝ Q (Ψ c r φ s) ((r φ : ℂ) * u φ) * (s : ℂ) + Q (Ψ c r φ s) * 1) *
      (((rd r a b hab φ : ℂ) - (r φ : ℂ) * I) * ub φ)

noncomputable def Bsc (a b : ℝ) (hab : a ≤ b) (φ s : ℝ) : ℂ :=
  (fderiv ℝ P (Ψc c r φ s) ((r φ : ℂ) * u φ) * (sc s : ℂ) + P (Ψc c r φ s) * 1) *
      (((rd r a b hab φ : ℂ) + (r φ : ℂ) * I) * u φ) +
    (fderiv ℝ Q (Ψc c r φ s) ((r φ : ℂ) * u φ) * (sc s : ℂ) + Q (Ψc c r φ s) * 1) *
      (((rd r a b hab φ : ℂ) - (r φ : ℂ) * I) * ub φ)

noncomputable def Tint (φ s : ℝ) : ℂ :=
  2 * I * (sc s : ℂ) * (r φ : ℂ) ^ 2 * g P Q (Ψc c r φ s)

theorem Bs_eq_Bsc (a b : ℝ) (hab : a ≤ b) (φ : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Bs c r P Q a b hab φ s = Bsc c r P Q a b hab φ s := by
  simp only [Bs, Bsc, Ψc, sc_of_mem hs]

theorem Bsc_eq (a b : ℝ) (hab : a ≤ b) (φ s : ℝ) :
    Bsc c r P Q a b hab φ s = Aφ c r P Q a b hab φ s + Tint c r P Q φ s := by
  simp only [Bsc, Aφ, Tint, g]
  set L := fderiv ℝ P (Ψc c r φ s)
  set M := fderiv ℝ Q (Ψc c r φ s)
  set p := P (Ψc c r φ s)
  set q := Q (Ψc c r φ s)
  have hUUb := u_mul_ub φ
  set U := u φ
  set Ub := ub φ
  have hL1 : L ((r φ : ℂ) * U) = (r φ : ℂ) * L U := clm_real_mul L _ _
  have hM1 : M ((r φ : ℂ) * U) = (r φ : ℂ) * M U := clm_real_mul M _ _
  have hL2 : L ((sc s : ℂ) * ((rd r a b hab φ : ℂ) + (r φ : ℂ) * I) * U) =
      (sc s : ℂ) * ((rd r a b hab φ : ℂ) * L U + (r φ : ℂ) * L (I * U)) := by
    rw [mul_assoc, clm_real_mul, add_mul, map_add, clm_real_mul, mul_assoc, clm_real_mul]
  have hM2 : M ((sc s : ℂ) * ((rd r a b hab φ : ℂ) + (r φ : ℂ) * I) * U) =
      (sc s : ℂ) * ((rd r a b hab φ : ℂ) * M U + (r φ : ℂ) * M (I * U)) := by
    rw [mul_assoc, clm_real_mul, add_mul, map_add, clm_real_mul, mul_assoc, clm_real_mul]
  have hWP := clm_wirtinger_bar L U
  have hWQ := clm_wirtinger M U
  rw [conj_u] at hWP
  rw [hL1, hM1, hL2, hM2]
  linear_combination ((sc s : ℂ) * (r φ : ℂ) ^ 2 * U) * hWP -
    ((sc s : ℂ) * (r φ : ℂ) ^ 2 * Ub) * hWQ +
    (2 * I * (sc s : ℂ) * (r φ : ℂ) ^ 2 *
      ((L 1 + I * L I) / 2 - (M 1 - I * M I) / 2)) * hUUb

end Setting

section Analysis

variable {c : ℂ} {r : ℝ → ℝ} {P Q : ℂ → ℂ} {U : Set ℂ}
  (hcont : Continuous r) (hper : Function.Periodic r (2 * π)) (hpos : ∀ φ, 0 < r φ)
  (hU : IsOpen U) (hKU : ∀ z : ℂ, ‖z - c‖ ≤ r (arg (z - c)) → z ∈ U)
  (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)

include hper hpos in
theorem mem_K_Ψ (φ : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖Ψ c r φ s - c‖ ≤ r (arg (Ψ c r φ s - c)) := by
  have hΨ : Ψ c r φ s - c = ((s * r φ : ℝ) : ℂ) * u φ := by
    simp only [Ψ]; push_cast; ring
  rw [hΨ]
  rcases hs.1.eq_or_lt with h0 | h0
  · rw [← h0]
    simp only [zero_mul, ofReal_zero, norm_zero, arg_zero]
    exact (hpos 0).le
  · have ht : 0 < s * r φ := mul_pos h0 (hpos φ)
    rw [periodic_apply_arg hper ht, norm_mul, norm_u, mul_one, Complex.norm_of_nonneg ht.le]
    calc s * r φ ≤ 1 * r φ := by gcongr; exacts [(hpos φ).le, hs.2]
      _ = r φ := one_mul _

include hper hpos hKU in
theorem Ψ_mem_U (φ : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : Ψ c r φ s ∈ U :=
  hKU _ (mem_K_Ψ hper hpos φ hs)

include hper hpos hKU in
theorem Ψc_mem_U (φ s : ℝ) : Ψc c r φ s ∈ U :=
  Ψ_mem_U hper hpos hKU φ (sc_mem s)

include hcont in
theorem continuous_Ψc : Continuous fun p : ℝ × ℝ => Ψc c r p.1 p.2 := by
  unfold Ψc Ψ
  have h1 : Continuous fun p : ℝ × ℝ => (sc p.2 : ℂ) :=
    continuous_ofReal.comp (continuous_sc.comp continuous_snd)
  have h2 : Continuous fun p : ℝ × ℝ => (r p.1 : ℂ) :=
    continuous_ofReal.comp (hcont.comp continuous_fst)
  have h3 : Continuous fun p : ℝ × ℝ => u p.1 := continuous_u.comp continuous_fst
  exact continuous_const.add ((h1.mul h2).mul h3)

include hcont hper hpos hKU hP in
theorem continuous_P_Ψc : Continuous fun p : ℝ × ℝ => P (Ψc c r p.1 p.2) :=
  hP.continuousOn.comp_continuous (continuous_Ψc hcont) fun p => Ψc_mem_U hper hpos hKU p.1 p.2

include hcont hper hpos hU hKU hP in
theorem continuous_DP_Ψc {v : ℝ × ℝ → ℂ} (hv : Continuous v) :
    Continuous fun p : ℝ × ℝ => fderiv ℝ P (Ψc c r p.1 p.2) (v p) :=
  ((hP.continuousOn_fderiv_of_isOpen hU le_rfl).comp_continuous (continuous_Ψc hcont)
    fun p => Ψc_mem_U hper hpos hKU p.1 p.2).clm_apply hv

theorem continuous_rd {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) :
    Continuous (rd r a b hab.le) :=
  (hC.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)).comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) fun φ => (projIcc a b hab.le φ).2

theorem continuous_atoms (hcont : Continuous r) :
    (Continuous fun p : ℝ × ℝ => u p.1) ∧ (Continuous fun p : ℝ × ℝ => ub p.1) ∧
      (Continuous fun p : ℝ × ℝ => (r p.1 : ℂ)) ∧ (Continuous fun p : ℝ × ℝ => (sc p.2 : ℂ)) :=
  ⟨continuous_u.comp continuous_fst, continuous_ub.comp continuous_fst,
    continuous_ofReal.comp (hcont.comp continuous_fst),
    continuous_ofReal.comp (continuous_sc.comp continuous_snd)⟩

include hcont hper hpos hKU hP hQ in
theorem continuous_A : Continuous fun p : ℝ × ℝ => A c r P Q p.1 p.2 := by
  obtain ⟨hu1, hub1, hr1, -⟩ := continuous_atoms (r := r) hcont
  have hPc := continuous_P_Ψc hcont hper hpos hKU hP
  have hQc := continuous_P_Ψc hcont hper hpos hKU hQ
  show Continuous fun p : ℝ × ℝ =>
    (P (Ψc c r p.1 p.2) * u p.1 + Q (Ψc c r p.1 p.2) * ub p.1) * (r p.1 : ℂ)
  exact ((hPc.mul hu1).add (hQc.mul hub1)).mul hr1

include hcont hper hpos hU hKU hP hQ in
theorem continuous_g_Ψc : Continuous fun p : ℝ × ℝ => g P Q (Ψc c r p.1 p.2) := by
  have h1 := continuous_DP_Ψc hcont hper hpos hU hKU hP (continuous_const (y := (1 : ℂ)))
  have h2 := continuous_DP_Ψc hcont hper hpos hU hKU hP (continuous_const (y := I))
  have h3 := continuous_DP_Ψc hcont hper hpos hU hKU hQ (continuous_const (y := (1 : ℂ)))
  have h4 := continuous_DP_Ψc hcont hper hpos hU hKU hQ (continuous_const (y := I))
  show Continuous fun p : ℝ × ℝ =>
    (fderiv ℝ P (Ψc c r p.1 p.2) 1 + I * fderiv ℝ P (Ψc c r p.1 p.2) I) / 2 -
      (fderiv ℝ Q (Ψc c r p.1 p.2) 1 - I * fderiv ℝ Q (Ψc c r p.1 p.2) I) / 2
  exact ((h1.add (continuous_const.mul h2)).div_const 2).sub
    ((h3.sub (continuous_const.mul h4)).div_const 2)

include hcont hper hpos hU hKU hP hQ in
theorem continuous_Tint : Continuous fun p : ℝ × ℝ => Tint c r P Q p.1 p.2 := by
  obtain ⟨-, -, hr1, hsc2⟩ := continuous_atoms (r := r) hcont
  have hg := continuous_g_Ψc hcont hper hpos hU hKU hP hQ
  show Continuous fun p : ℝ × ℝ =>
    2 * I * (sc p.2 : ℂ) * (r p.1 : ℂ) ^ 2 * g P Q (Ψc c r p.1 p.2)
  exact (((continuous_const.mul hsc2).mul (hr1.pow 2)).mul hg)

include hcont hper hpos hU hKU hP hQ in
theorem continuous_Aφ {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) :
    Continuous fun p : ℝ × ℝ => Aφ c r P Q a b hab.le p.1 p.2 := by
  obtain ⟨hu1, hub1, hr1, hsc2⟩ := continuous_atoms (r := r) hcont
  have hrd1 : Continuous fun p : ℝ × ℝ => (rd r a b hab.le p.1 : ℂ) :=
    continuous_ofReal.comp ((continuous_rd hab hC).comp continuous_fst)
  have hv : Continuous fun p : ℝ × ℝ =>
      (sc p.2 : ℂ) * ((rd r a b hab.le p.1 : ℂ) + (r p.1 : ℂ) * I) * u p.1 :=
    (hsc2.mul (hrd1.add (hr1.mul continuous_const))).mul hu1
  have hPc := continuous_P_Ψc hcont hper hpos hKU hP
  have hQc := continuous_P_Ψc hcont hper hpos hKU hQ
  have hDP := continuous_DP_Ψc hcont hper hpos hU hKU hP hv
  have hDQ := continuous_DP_Ψc hcont hper hpos hU hKU hQ hv
  show Continuous fun p : ℝ × ℝ =>
    (fderiv ℝ P (Ψc c r p.1 p.2)
          ((sc p.2 : ℂ) * ((rd r a b hab.le p.1 : ℂ) + (r p.1 : ℂ) * I) * u p.1) * u p.1 +
        P (Ψc c r p.1 p.2) * (u p.1 * I) +
        fderiv ℝ Q (Ψc c r p.1 p.2)
          ((sc p.2 : ℂ) * ((rd r a b hab.le p.1 : ℂ) + (r p.1 : ℂ) * I) * u p.1) * ub p.1 +
        Q (Ψc c r p.1 p.2) * (ub p.1 * (-I))) * (r p.1 : ℂ) +
      (P (Ψc c r p.1 p.2) * u p.1 + Q (Ψc c r p.1 p.2) * ub p.1) * (rd r a b hab.le p.1 : ℂ)
  exact (((((hDP.mul hu1).add (hPc.mul (hu1.mul continuous_const))).add (hDQ.mul hub1)).add
    (hQc.mul (hub1.mul continuous_const))).mul hr1).add (((hPc.mul hu1).add (hQc.mul hub1)).mul hrd1)

include hcont hper hpos hU hKU hP hQ in
theorem continuous_Bsc {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) :
    Continuous fun p : ℝ × ℝ => Bsc c r P Q a b hab.le p.1 p.2 := by
  obtain ⟨hu1, hub1, hr1, hsc2⟩ := continuous_atoms (r := r) hcont
  have hrd1 : Continuous fun p : ℝ × ℝ => (rd r a b hab.le p.1 : ℂ) :=
    continuous_ofReal.comp ((continuous_rd hab hC).comp continuous_fst)
  have hv : Continuous fun p : ℝ × ℝ => (r p.1 : ℂ) * u p.1 := hr1.mul hu1
  have hPc := continuous_P_Ψc hcont hper hpos hKU hP
  have hQc := continuous_P_Ψc hcont hper hpos hKU hQ
  have hDP := continuous_DP_Ψc hcont hper hpos hU hKU hP hv
  have hDQ := continuous_DP_Ψc hcont hper hpos hU hKU hQ hv
  show Continuous fun p : ℝ × ℝ =>
    (fderiv ℝ P (Ψc c r p.1 p.2) ((r p.1 : ℂ) * u p.1) * (sc p.2 : ℂ) + P (Ψc c r p.1 p.2) * 1) *
        (((rd r a b hab.le p.1 : ℂ) + (r p.1 : ℂ) * I) * u p.1) +
      (fderiv ℝ Q (Ψc c r p.1 p.2) ((r p.1 : ℂ) * u p.1) * (sc p.2 : ℂ) + Q (Ψc c r p.1 p.2) * 1) *
        (((rd r a b hab.le p.1 : ℂ) - (r p.1 : ℂ) * I) * ub p.1)
  exact (((hDP.mul hsc2).add (hPc.mul continuous_const)).mul
      ((hrd1.add (hr1.mul continuous_const)).mul hu1)).add
    (((hDQ.mul hsc2).add (hQc.mul continuous_const)).mul
      ((hrd1.sub (hr1.mul continuous_const)).mul hub1))

theorem continuous_slice_left {f : ℝ → ℝ → ℂ} (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2)
    (φ : ℝ) : Continuous fun s => f φ s :=
  hf.comp (continuous_const.prodMk continuous_id)

theorem continuous_slice_right {f : ℝ → ℝ → ℂ} (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2)
    (s : ℝ) : Continuous fun φ => f φ s :=
  hf.comp (continuous_id.prodMk continuous_const)

theorem continuous_param_integral {f : ℝ → ℝ → ℂ} (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2) :
    Continuous fun φ => ∫ s in (0 : ℝ)..1, f φ s :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := f) hf 0 1

theorem hasDerivAt_Ψ_s (φ s : ℝ) : HasDerivAt (fun s : ℝ => Ψ c r φ s) ((r φ : ℂ) * u φ) s := by
  have h : (fun s : ℝ => Ψ c r φ s) = fun s : ℝ => c + (s : ℂ) * ((r φ : ℂ) * u φ) := by
    ext s; simp only [Ψ, mul_assoc]
  rw [h]
  exact (((hasDerivAt_id s).ofReal_comp.mul_const _).const_add c).congr_deriv (by simp)

theorem hasDerivAt_Ψc_φ {φ δ : ℝ} (hr : HasDerivAt r δ φ) (s : ℝ) :
    HasDerivAt (fun φ => Ψc c r φ s) ((sc s : ℂ) * ((δ : ℂ) + (r φ : ℂ) * I) * u φ) φ := by
  have h1 : HasDerivAt (fun φ => (r φ : ℂ)) (δ : ℂ) φ := hr.ofReal_comp
  have h2 := ((h1.mul (hasDerivAt_u φ)).const_mul (sc s : ℂ)).const_add c
  have h : (fun φ => Ψc c r φ s) = fun φ => c + (sc s : ℂ) * ((r φ : ℂ) * u φ) := by
    ext φ; simp only [Ψc, Ψ, mul_assoc]
  rw [h]
  exact h2.congr_deriv (by ring)

include hP hU in
theorem hasFDerivAt_P {z : ℂ} (hz : z ∈ U) : HasFDerivAt P (fderiv ℝ P z) z :=
  ((hP.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hz)).hasFDerivAt

include hP hQ hU in
theorem hasDerivAt_B {a b : ℝ} (hab : a ≤ b) (φ : ℝ) {s : ℝ} (hs : Ψ c r φ s ∈ U) :
    HasDerivAt (fun s => B c r P Q a b hab φ s) (Bs c r P Q a b hab φ s) s := by
  have hPz := (hasFDerivAt_P hU hP hs).comp_hasDerivAt s (hasDerivAt_Ψ_s (c := c) (r := r) φ s)
  have hQz := (hasFDerivAt_P hU hQ hs).comp_hasDerivAt s (hasDerivAt_Ψ_s (c := c) (r := r) φ s)
  have hs1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := (hasDerivAt_id s).ofReal_comp
  exact ((hPz.mul hs1).mul_const _).add ((hQz.mul hs1).mul_const _)

theorem B_zero {a b : ℝ} (hab : a ≤ b) (φ : ℝ) : B c r P Q a b hab φ 0 = 0 := by
  simp [B]

theorem B_one {a b : ℝ} (hab : a ≤ b) (φ : ℝ) :
    B c r P Q a b hab φ 1 =
      P (c + (r φ : ℂ) * u φ) * (((rd r a b hab φ : ℂ) + (r φ : ℂ) * I) * u φ) +
        Q (c + (r φ : ℂ) * u φ) * (((rd r a b hab φ : ℂ) - (r φ : ℂ) * I) * ub φ) := by
  simp [B, Ψ]

include hcont hper hpos hU hKU hP hQ in

theorem B_one_eq_integral {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) (φ : ℝ) :
    B c r P Q a b hab.le φ 1 = ∫ s in (0 : ℝ)..1, Bsc c r P Q a b hab.le φ s := by
  have hcs : Continuous fun s => Bsc c r P Q a b hab.le φ s :=
    continuous_slice_left (continuous_Bsc hcont hper hpos hU hKU hP hQ hab hC) φ
  have hcs' : ContinuousOn (fun s => Bs c r P Q a b hab.le φ s) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact hcs.continuousOn.congr fun s hs => Bs_eq_Bsc c r P Q a b hab.le φ hs
  have hftc := integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (f := fun s => B c r P Q a b hab.le φ s) (f' := fun s => Bs c r P Q a b hab.le φ s)
    (fun s hs => hasDerivAt_B hU hP hQ hab.le φ
      (Ψ_mem_U hper hpos hKU φ (by rwa [uIcc_of_le zero_le_one] at hs)))
    hcs'.intervalIntegrable
  simp only [B_zero, sub_zero] at hftc
  rw [← hftc]
  exact intervalIntegral.integral_congr fun s hs => Bs_eq_Bsc c r P Q a b hab.le φ
    (by rwa [uIcc_of_le zero_le_one] at hs)

theorem hasDerivAt_rd {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) {φ : ℝ}
    (hφ : φ ∈ Ioo a b) : HasDerivAt r (rd r a b hab.le φ) φ := by
  have hmem : φ ∈ Icc a b := ⟨hφ.1.le, hφ.2.le⟩
  have hd : DifferentiableAt ℝ r φ :=
    (hC.differentiableOn (by norm_num)).differentiableAt (Icc_mem_nhds hφ.1 hφ.2)
  have : rd r a b hab.le φ = deriv r φ := by
    rw [rd, projIcc_of_mem hab.le hmem]
    exact hd.derivWithin (uniqueDiffOn_Icc hab φ hmem)
  rw [this]
  exact hd.hasDerivAt

include hper hpos hU hKU hP hQ in

theorem hasDerivAt_A {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) {φ : ℝ}
    (hφ : φ ∈ Ioo a b) (s : ℝ) :
    HasDerivAt (fun φ => A c r P Q φ s) (Aφ c r P Q a b hab.le φ s) φ := by
  have hr := hasDerivAt_rd hab hC hφ
  have hΨ := hasDerivAt_Ψc_φ (c := c) hr s
  have hPz := (hasFDerivAt_P hU hP (Ψc_mem_U hper hpos hKU φ s)).comp_hasDerivAt φ hΨ
  have hQz := (hasFDerivAt_P hU hQ (Ψc_mem_U hper hpos hKU φ s)).comp_hasDerivAt φ hΨ
  have h2 := ((hPz.mul (hasDerivAt_u φ)).add (hQz.mul (hasDerivAt_ub φ))).mul hr.ofReal_comp
  refine h2.congr_deriv ?_
  simp only [Aφ, Function.comp_apply, Pi.mul_apply, Pi.add_apply]
  ring

include hcont hper hpos hU hKU hP hQ in

theorem hasDerivAt_G {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) {φ₀ : ℝ}
    (hφ₀ : φ₀ ∈ Ioo a b) :
    HasDerivAt (fun φ => ∫ s in (0 : ℝ)..1, A c r P Q φ s)
      (∫ s in (0 : ℝ)..1, Aφ c r P Q a b hab.le φ₀ s) φ₀ := by
  have hAc := continuous_A hcont hper hpos hKU hP hQ (c := c)
  have hAφc := continuous_Aφ hcont hper hpos hU hKU hP hQ (c := c) hab hC
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc a b ×ˢ Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hAφc.continuousOn
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := volume) (a := (0 : ℝ)) (b := 1) (F := fun φ s => A c r P Q φ s)
    (F' := fun φ s => Aφ c r P Q a b hab.le φ s) (x₀ := φ₀) (s := Ioo a b) (bound := fun _ => M)
    (Ioo_mem_nhds hφ₀.1 hφ₀.2)
    (Filter.Eventually.of_forall fun φ => (continuous_slice_left hAc φ).aestronglyMeasurable)
    ((continuous_slice_left hAc φ₀).intervalIntegrable _ _)
    (continuous_slice_left hAφc φ₀).aestronglyMeasurable
    (by
      refine Filter.Eventually.of_forall fun s hs φ hφ => hM (φ, s) ⟨⟨hφ.1.le, hφ.2.le⟩, ?_⟩
      rw [uIoc_of_le zero_le_one] at hs
      exact ⟨hs.1.le, hs.2⟩)
    _root_.intervalIntegrable_const
    (Filter.Eventually.of_forall fun s _ φ hφ => hasDerivAt_A hper hpos hU hKU hP hQ hab hC hφ s)
  exact key.2

end Analysis

section Arcs

variable {c : ℂ} {r : ℝ → ℝ} {P Q : ℂ → ℂ} {U : Set ℂ}
  (hcont : Continuous r) (hper : Function.Periodic r (2 * π)) (hpos : ∀ φ, 0 < r φ)
  (hU : IsOpen U) (hKU : ∀ z : ℂ, ‖z - c‖ ≤ r (arg (z - c)) → z ∈ U)
  (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)

noncomputable def bd (c : ℂ) (r : ℝ → ℝ) (P Q : ℂ → ℂ) (φ : ℝ) : ℂ :=
  P (c + r φ * exp (φ * I)) * ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I)) +
    Q (c + r φ * exp (φ * I)) * (starRingEnd ℂ) ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I))

theorem conj_coef_mul_exp (x y φ : ℝ) :
    (starRingEnd ℂ) (((x : ℂ) + (y : ℂ) * I) * exp (φ * I)) = ((x : ℂ) - (y : ℂ) * I) * ub φ :=
  conj_coef_mul_u x y φ

theorem bd_eq_B_one {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) {φ : ℝ}
    (hφ : φ ∈ Ioo a b) : bd c r P Q φ = B c r P Q a b hab.le φ 1 := by
  rw [bd, B_one, (hasDerivAt_rd hab hC hφ).deriv, conj_coef_mul_exp]
  rfl

include hcont hper hpos hU hKU hP hQ in

theorem arc_integral {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) :
    (∫ φ in a..b, bd c r P Q φ) =
        ((∫ s in (0 : ℝ)..1, A c r P Q b s) - ∫ s in (0 : ℝ)..1, A c r P Q a s) +
          ∫ φ in a..b, ∫ s in (0 : ℝ)..1, Tint c r P Q φ s ∧
      IntervalIntegrable (bd c r P Q) volume a b := by
  have hAφc := continuous_Aφ hcont hper hpos hU hKU hP hQ (c := c) hab hC
  have hTc := continuous_Tint hcont hper hpos hU hKU hP hQ (c := c)
  have hAc := continuous_A hcont hper hpos hKU hP hQ (c := c)
  have hD : Continuous fun φ => ∫ s in (0 : ℝ)..1, Aφ c r P Q a b hab.le φ s :=
    continuous_param_integral hAφc
  have hT : Continuous fun φ => ∫ s in (0 : ℝ)..1, Tint c r P Q φ s := continuous_param_integral hTc
  have hG : Continuous fun φ => ∫ s in (0 : ℝ)..1, A c r P Q φ s := continuous_param_integral hAc
  have hpt : ∀ φ ∈ Ioo a b, bd c r P Q φ =
      (∫ s in (0 : ℝ)..1, Aφ c r P Q a b hab.le φ s) + ∫ s in (0 : ℝ)..1, Tint c r P Q φ s := by
    intro φ hφ
    rw [bd_eq_B_one hab hC hφ, B_one_eq_integral hcont hper hpos hU hKU hP hQ hab hC φ,
      ← intervalIntegral.integral_add ((continuous_slice_left hAφc φ).intervalIntegrable _ _)
        ((continuous_slice_left hTc φ).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun s _ => Bsc_eq c r P Q a b hab.le φ s
  have hae : ∀ᵐ φ ∂(volume : Measure ℝ), φ ∈ Ι a b → bd c r P Q φ =
      (∫ s in (0 : ℝ)..1, Aφ c r P Q a b hab.le φ s) + ∫ s in (0 : ℝ)..1, Tint c r P Q φ s := by
    have hb : ∀ᵐ φ ∂(volume : Measure ℝ), φ ∉ ({b} : Set ℝ) :=
      compl_mem_ae_iff.2 (measure_singleton b)
    filter_upwards [hb] with φ hφb hφI
    rw [uIoc_of_le hab.le] at hφI
    exact hpt φ ⟨hφI.1, lt_of_le_of_ne hφI.2 hφb⟩
  refine ⟨?_, ?_⟩
  · rw [intervalIntegral.integral_congr_ae hae,
      intervalIntegral.integral_add (hD.intervalIntegrable _ _) (hT.intervalIntegrable _ _),
      integral_eq_sub_of_hasDerivAt_of_le hab.le hG.continuousOn
        (fun φ hφ => hasDerivAt_G hcont hper hpos hU hKU hP hQ hab hC hφ) (hD.intervalIntegrable _ _)]
  · rw [intervalIntegrable_iff]
    refine (intervalIntegrable_iff.1 ((hD.add hT).intervalIntegrable a b)).congr ?_
    exact (ae_restrict_iff' measurableSet_uIoc).2 (hae.mono fun φ hφ hφI => (hφ hφI).symm)

include hper in
theorem A_add_two_pi (φ s : ℝ) : A c r P Q (φ + 2 * π) s = A c r P Q φ s := by
  simp only [A, Ψc, Ψ, hper φ, u_add_two_pi, ub_add_two_pi]

include hcont hper hpos hU hKU hP hQ in

theorem boundary_integral_eq (N : ℕ) (φs : Fin (N + 1) → ℝ) (hφ0 : φs 0 = 0)
    (hφN : φs (Fin.last N) = 2 * π) (hmono : StrictMono φs)
    (hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Icc (φs i.castSucc) (φs i.succ))) :
    (∫ φ in (0 : ℝ)..(2 * π), bd c r P Q φ) =
      ∫ φ in (0 : ℝ)..(2 * π), ∫ s in (0 : ℝ)..1, Tint c r P Q φ s := by
  set aN : ℕ → ℝ := fun k => if h : k < N + 1 then φs ⟨k, h⟩ else 2 * π with haN
  have haN0 : aN 0 = 0 := by
    have h0 : 0 < N + 1 := Nat.succ_pos N
    have : aN 0 = φs ⟨0, h0⟩ := by simp only [haN, dif_pos h0]
    rw [this, show (⟨0, h0⟩ : Fin (N + 1)) = 0 from rfl, hφ0]
  have haNN : aN N = 2 * π := by
    have hN : N < N + 1 := Nat.lt_succ_self N
    have : aN N = φs ⟨N, hN⟩ := by simp only [haN, dif_pos hN]
    rw [this, show (⟨N, hN⟩ : Fin (N + 1)) = Fin.last N from rfl, hφN]
  have hk1 : ∀ k (hk : k < N), aN k = φs (⟨k, hk⟩ : Fin N).castSucc := by
    intro k hk
    have h : k < N + 1 := by omega
    simp only [haN, dif_pos h]; rfl
  have hk2 : ∀ k (hk : k < N), aN (k + 1) = φs (⟨k, hk⟩ : Fin N).succ := by
    intro k hk
    have h : k + 1 < N + 1 := by omega
    simp only [haN, dif_pos h]; rfl
  have hlt : ∀ k, k < N → aN k < aN (k + 1) := by
    intro k hk; rw [hk1 k hk, hk2 k hk]; exact hmono Fin.castSucc_lt_succ
  have hCk : ∀ k, k < N → ContDiffOn ℝ 2 r (Icc (aN k) (aN (k + 1))) := by
    intro k hk; rw [hk1 k hk, hk2 k hk]; exact hC2 _
  have harc := fun k (hk : k < N) =>
    arc_integral hcont hper hpos hU hKU hP hQ (c := c) (hlt k hk) (hCk k hk)
  have hT : Continuous fun φ => ∫ s in (0 : ℝ)..1, Tint c r P Q φ s :=
    continuous_param_integral (continuous_Tint hcont hper hpos hU hKU hP hQ)
  have hper' : (∫ s in (0 : ℝ)..1, A c r P Q (2 * π) s) = ∫ s in (0 : ℝ)..1, A c r P Q 0 s := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    have := A_add_two_pi hper (c := c) (P := P) (Q := Q) 0 s
    rwa [zero_add] at this
  have htel : ∑ k ∈ Finset.range N, ((∫ s in (0 : ℝ)..1, A c r P Q (aN (k + 1)) s) -
      ∫ s in (0 : ℝ)..1, A c r P Q (aN k) s) =
      (∫ s in (0 : ℝ)..1, A c r P Q (aN N) s) - ∫ s in (0 : ℝ)..1, A c r P Q (aN 0) s :=
    Finset.sum_range_sub (fun k => ∫ s in (0 : ℝ)..1, A c r P Q (aN k) s) N
  have key : (∫ φ in aN 0..aN N, bd c r P Q φ) =
      ∫ φ in aN 0..aN N, ∫ s in (0 : ℝ)..1, Tint c r P Q φ s := by
    rw [← sum_integral_adjacent_intervals (a := aN) (n := N) fun k hk => (harc k hk).2,
      ← sum_integral_adjacent_intervals (a := aN) (n := N) fun k hk => hT.intervalIntegrable _ _,
      Finset.sum_congr rfl fun k hk => (harc k (Finset.mem_range.1 hk)).1, Finset.sum_add_distrib,
      htel, haNN, haN0, hper', sub_self, zero_add]
  rw [haN0, haNN] at key
  exact key

end Arcs

section Area

variable {c : ℂ} {r : ℝ → ℝ} {P Q : ℂ → ℂ} {U : Set ℂ}
  (hcont : Continuous r) (hper : Function.Periodic r (2 * π)) (hpos : ∀ φ, 0 < r φ)
  (hU : IsOpen U) (hKU : ∀ z : ℂ, ‖z - c‖ ≤ r (arg (z - c)) → z ∈ U)
  (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)

theorem u_periodic : Function.Periodic u (2 * π) := u_add_two_pi

include hcont in
theorem continuous_Ψ2 : Continuous fun p : ℝ × ℝ => Ψ c r p.1 p.2 := by
  unfold Ψ
  exact continuous_const.add (((continuous_ofReal.comp continuous_snd).mul
    (continuous_ofReal.comp (hcont.comp continuous_fst))).mul (continuous_u.comp continuous_fst))

include hcont hper hpos in

theorem isCompact_K : IsCompact {z : ℂ | ‖z - c‖ ≤ r (arg (z - c))} := by
  have hK : {z : ℂ | ‖z - c‖ ≤ r (arg (z - c))} =
      (fun p : ℝ × ℝ => Ψ c r p.1 p.2) '' (Icc 0 (2 * π) ×ˢ Icc (0 : ℝ) 1) := by
    ext z
    simp only [mem_setOf_eq, mem_image, mem_prod, mem_Icc, Prod.exists]
    constructor
    · intro hz
      by_cases hzc : z = c
      · exact ⟨0, 0, ⟨⟨le_rfl, by positivity⟩, le_rfl, zero_le_one⟩, by simp [Ψ, hzc]⟩
      have hw : z - c ≠ 0 := sub_ne_zero.2 hzc
      have hρ : 0 < ‖z - c‖ := norm_pos_iff.2 hw
      set θ := arg (z - c) with hθ
      have hrθ : 0 < r θ := hpos θ
      set φ := toIcoMod Real.two_pi_pos 0 θ with hφ
      have hφmem : φ ∈ Ico (0 : ℝ) (0 + 2 * π) := toIcoMod_mem_Ico _ _ _
      refine ⟨φ, ‖z - c‖ / r θ, ⟨⟨hφmem.1, by linarith [hφmem.2]⟩, div_nonneg hρ.le hrθ.le,
        (div_le_one hrθ).2 hz⟩, ?_⟩
      have hrφ : r φ = r θ := by rw [hφ, toIcoMod]; exact hper.sub_zsmul_eq _
      have huφ : u φ = u θ := by rw [hφ, toIcoMod]; exact u_periodic.sub_zsmul_eq _
      simp only [Ψ, hrφ, huφ]
      have h1 : ((‖z - c‖ / r θ : ℝ) : ℂ) * (r θ : ℂ) = (‖z - c‖ : ℂ) := by
        rw [← ofReal_mul, div_mul_cancel₀ _ hrθ.ne']
      rw [h1, u, hθ, norm_mul_exp_arg_mul_I, add_sub_cancel]
    · rintro ⟨φ, s, ⟨-, hs0, hs1⟩, rfl⟩
      exact mem_K_Ψ hper hpos φ ⟨hs0, hs1⟩
  rw [hK]
  exact (isCompact_Icc.prod isCompact_Icc).image (continuous_Ψ2 hcont)

include hcont hper in
theorem r_bounded : ∃ R, ∀ φ, r φ ≤ R := by
  obtain ⟨φ₀, -, hφ₀⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by positivity :
    (0 : ℝ) ≤ 2 * π)) hcont.continuousOn
  refine ⟨r φ₀, fun φ => ?_⟩
  have hmem : toIcoMod Real.two_pi_pos 0 φ ∈ Icc (0 : ℝ) (2 * π) := by
    have := toIcoMod_mem_Ico Real.two_pi_pos 0 φ
    rw [zero_add] at this
    exact ⟨this.1, this.2.le⟩
  have : r φ = r (toIcoMod Real.two_pi_pos 0 φ) := by
    rw [toIcoMod]; exact (hper.sub_zsmul_eq _).symm
  rw [this]
  exact hφ₀ hmem

theorem measurable_g : Measurable (g P Q) := by
  unfold g
  exact (((measurable_fderiv_apply_const ℝ P (1 : ℂ)).add
    ((measurable_fderiv_apply_const ℝ P I).const_mul I)).div_const 2).sub
    (((measurable_fderiv_apply_const ℝ Q (1 : ℂ)).sub
      ((measurable_fderiv_apply_const ℝ Q I).const_mul I)).div_const 2)

include hU hP hQ in
theorem continuousOn_g : ContinuousOn (g P Q) U := by
  have hP' := hP.continuousOn_fderiv_of_isOpen hU le_rfl
  have hQ' := hQ.continuousOn_fderiv_of_isOpen hU le_rfl
  unfold g
  exact (((hP'.clm_apply continuousOn_const).add
    (continuousOn_const.mul (hP'.clm_apply continuousOn_const))).div_const 2).sub
    (((hQ'.clm_apply continuousOn_const).sub
      (continuousOn_const.mul (hQ'.clm_apply continuousOn_const))).div_const 2)

noncomputable def F (c : ℂ) (r : ℝ → ℝ) (P Q : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  if p.1 ≤ r p.2 then (p.1 : ℂ) * g P Q (c + (p.1 : ℂ) * u p.2) else 0

noncomputable def V (c : ℂ) (r : ℝ → ℝ) (P Q : ℂ → ℂ) (φ : ℝ) : ℂ :=
  (r φ : ℂ) * ∫ s in (0 : ℝ)..1, ((r φ * s : ℝ) : ℂ) * g P Q (c + ((r φ * s : ℝ) : ℂ) * u φ)

include hpos in
theorem inner_integral (φ : ℝ) : ∫ ρ in Ioi (0 : ℝ), F c r P Q (ρ, φ) = V c r P Q φ := by
  have h1 : (fun ρ : ℝ => F c r P Q (ρ, φ)) =
      (Iic (r φ)).indicator fun ρ : ℝ => (ρ : ℂ) * g P Q (c + (ρ : ℂ) * u φ) := by
    ext ρ; simp only [F, indicator_apply, mem_Iic]
  rw [h1, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic,
    ← intervalIntegral.integral_of_le (hpos φ).le]
  have hsub := smul_integral_comp_mul_left
    (f := fun ρ : ℝ => (ρ : ℂ) * g P Q (c + (ρ : ℂ) * u φ)) (a := 0) (b := 1) (r φ)
  rw [mul_zero, mul_one] at hsub
  rw [← hsub, V, real_smul]

include hper in
theorem V_add_two_pi (φ : ℝ) : V c r P Q (φ + 2 * π) = V c r P Q φ := by
  simp only [V, hper φ, u_add_two_pi]

theorem Tint_integral_eq (φ : ℝ) :
    (∫ s in (0 : ℝ)..1, Tint c r P Q φ s) = 2 * I * V c r P Q φ := by
  rw [V, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine integral_congr fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  simp only [Tint, Ψc, Ψ, sc_of_mem hs]
  have : c + ((r φ * s : ℝ) : ℂ) * u φ = c + (s : ℂ) * (r φ : ℂ) * u φ := by push_cast; ring
  rw [this]
  push_cast
  ring

include hcont hper hpos hU hKU hP hQ in

theorem area_integral_eq :
    (∫ z in {z : ℂ | ‖z - c‖ ≤ r (arg (z - c))}, g P Q z) = ∫ φ in (0 : ℝ)..(2 * π), V c r P Q φ := by
  set K := {z : ℂ | ‖z - c‖ ≤ r (arg (z - c))} with hKdef
  have hKc : IsCompact K := isCompact_K hcont hper hpos
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKU' : K ⊆ U := fun z hz => hKU z hz
  obtain ⟨Mg, hMg⟩ := hKc.exists_bound_of_continuousOn ((continuousOn_g hU hP hQ).mono hKU')
  obtain ⟨R, hR⟩ := r_bounded hcont hper
  have hR0 : 0 ≤ R := (hpos 0).le.trans (hR 0)
  have hMg0 : 0 ≤ Mg := (norm_nonneg _).trans (hMg c (by
    simp only [hKdef, mem_setOf_eq, sub_self, norm_zero, arg_zero]; exact (hpos 0).le))

  have h12 : (∫ z in K, g P Q z) = ∫ w, K.indicator (g P Q) (c + w) := by
    rw [← MeasureTheory.integral_indicator hKm]
    exact (integral_add_left_eq_self (μ := (volume : Measure ℂ)) (K.indicator (g P Q)) c).symm

  have h3 := (Complex.integral_comp_polarCoord_symm fun w => K.indicator (g P Q) (c + w)).symm

  have htarget : (polarCoord.target : Set (ℝ × ℝ)) = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  have h4 : (∫ p in polarCoord.target, p.1 • K.indicator (g P Q) (c + Complex.polarCoord.symm p)) =
      ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, F c r P Q p := by
    rw [htarget]
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
    have hp1 : 0 < p.1 := hp.1
    have hsymm : Complex.polarCoord.symm p = (p.1 : ℂ) * u p.2 := by
      rw [Complex.polarCoord_symm_apply, u, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    have hmem : (c + (p.1 : ℂ) * u p.2 ∈ K) ↔ p.1 ≤ r p.2 := by
      simp only [hKdef, mem_setOf_eq, add_sub_cancel_left, norm_mul, norm_u, mul_one,
        Complex.norm_of_nonneg hp1.le, periodic_apply_arg hper hp1]
    rw [hsymm]
    simp only [F, indicator_apply, hmem]
    split_ifs <;> simp [real_smul]

  have hmeasF : Measurable (F c r P Q) := by
    unfold F
    refine Measurable.ite (measurableSet_le measurable_fst (hcont.measurable.comp measurable_snd))
      ?_ measurable_const
    exact (measurable_ofReal.comp measurable_fst).mul (measurable_g.comp (measurable_const.add
      ((measurable_ofReal.comp measurable_fst).mul (continuous_u.measurable.comp measurable_snd))))
  have hbound : ∀ p : ℝ × ℝ, 0 < p.1 → ‖F c r P Q p‖ ≤ R * Mg := by
    intro p hp1
    unfold F
    split_ifs with h
    · have hzK : c + (p.1 : ℂ) * u p.2 ∈ K := by
        simp only [hKdef, mem_setOf_eq, add_sub_cancel_left, norm_mul, norm_u, mul_one,
          Complex.norm_of_nonneg hp1.le, periodic_apply_arg hper hp1]
        exact h
      rw [norm_mul, Complex.norm_of_nonneg hp1.le]
      exact mul_le_mul (h.trans (hR _)) (hMg _ hzK) (norm_nonneg _) hR0
    · rw [norm_zero]; positivity
  have hint : IntegrableOn (fun z : ℝ × ℝ => F c r P Q z.swap) (Ioo (-π) π ×ˢ Ioi (0 : ℝ))
      ((volume : Measure ℝ).prod volume) := by
    rw [← Ioc_union_Ioi_eq_Ioi hR0, Set.prod_union]
    refine IntegrableOn.union ?_ ?_
    · refine Measure.integrableOn_of_bounded (M := R * Mg) ?_
        (hmeasF.comp measurable_swap).aestronglyMeasurable ?_
      · rw [Measure.prod_prod]
        exact (ENNReal.mul_lt_top measure_Ioo_lt_top measure_Ioc_lt_top).ne
      · refine (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioc)).2
          (Filter.Eventually.of_forall fun z hz => ?_)
        exact hbound z.swap hz.2.1
    · refine integrableOn_zero.congr_fun (fun z hz => ?_) (measurableSet_Ioo.prod measurableSet_Ioi)
      have hz2 : R < z.2 := hz.2
      simp only [F, Prod.swap]
      rw [if_neg (not_le.2 ((hR _).trans_lt hz2))]
  have h5 : (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, F c r P Q p) =
      ∫ φ in Ioo (-π) π, ∫ ρ in Ioi (0 : ℝ), F c r P Q (ρ, φ) := by
    rw [Measure.volume_eq_prod, ← setIntegral_prod_swap, setIntegral_prod _ hint]
    rfl

  have h6 : (∫ φ in Ioo (-π) π, ∫ ρ in Ioi (0 : ℝ), F c r P Q (ρ, φ)) =
      ∫ φ in (0 : ℝ)..(2 * π), V c r P Q φ := by
    simp_rw [inner_integral hpos]
    rw [setIntegral_congr_set (Ioo_ae_eq_Ioc (a := -π) (b := π)),
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -π ≤ π)]
    have hV : Function.Periodic (V c r P Q) (2 * π) := V_add_two_pi hper
    have := hV.intervalIntegral_add_eq (-π) 0
    rw [zero_add, show -π + 2 * π = π by ring] at this
    exact this
  rw [h12, h3, h4, h5, h6]

end Area

end RadialGreen

open RadialGreen Complex MeasureTheory Set in
theorem solution
    (c : ℂ) (r : ℝ → ℝ) (hcont : Continuous r) (hper : Function.Periodic r (2 * Real.pi))
    (hpos : ∀ φ, 0 < r φ)
    (N : ℕ) (φs : Fin (N + 1) → ℝ) (hφ0 : φs 0 = 0) (hφN : φs (Fin.last N) = 2 * Real.pi)
    (hmono : StrictMono φs)
    (hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Set.Icc (φs i.castSucc) (φs i.succ)))
    (P Q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hKU : ∀ z : ℂ, ‖z - c‖ ≤ r (arg (z - c)) → z ∈ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
        (P (c + r φ * exp (φ * I)) * ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I)) +
          Q (c + r φ * exp (φ * I)) *
            (starRingEnd ℂ) ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I))) =
      2 * I * ∫ z in {z : ℂ | ‖z - c‖ ≤ r (arg (z - c))},
        ((fderiv ℝ P z 1 + I * fderiv ℝ P z I) / 2 - (fderiv ℝ Q z 1 - I * fderiv ℝ Q z I) / 2) := by
  have h1 := boundary_integral_eq hcont hper hpos hU hKU hP hQ (c := c) N φs hφ0 hφN hmono hC2
  have h2 := area_integral_eq hcont hper hpos hU hKU hP hQ (c := c)
  change (∫ φ in (0 : ℝ)..(2 * Real.pi), bd c r P Q φ) = 2 * I * ∫ z in _, g P Q z
  rw [h1, h2, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun φ _ => Tint_integral_eq (c := c) (r := r) (P := P) (Q := Q) φ

end S_Complex_integral_radial_loop_eq_two_mul_I_mul_setIntegral
end P2MW
export P2MW.S_Complex_integral_radial_loop_eq_two_mul_I_mul_setIntegral (solution)
