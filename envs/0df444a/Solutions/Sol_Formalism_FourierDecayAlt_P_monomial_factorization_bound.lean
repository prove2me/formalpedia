-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.monomial_factorization_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:59:54.507145+00:00
-- url     : https://prove2.me/submissions/314bf16b-d0e8-4323-b72c-b91194453441

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UpperMinorIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetSubmatrixUnitriangularEqOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeDivOfMulEqLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_le_div_of_mul_eq_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_lt_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_EntryMinorBounds_inv_entry_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EntryMinorBounds_minor_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EntryMinorBounds_mx_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_lower_minor_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_lower_parabolic_entry_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_minor_C_nonzero
import Theorems.Thm_Formalism_FourierDecayAlt_P_upper_minor_identity


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2 EntryMinorBounds
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.MonomialFactorizationBound := by
  intro m P hP
  obtain ⟨w, d, hd, rfl⟩ := hP
  have hcn : ∀ a : Fin m, C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1)) ≠ 0 :=
    fun a => minor_C_nonzero m w d hd (a.val + 1) a.isLt
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (Nat.factorial m : ℝ) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hK]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1 + ∑ a : Fin m,
      K / ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖ := ⟨_, rfl⟩
  have hterm0 : ∀ a : Fin m, 0 ≤ K / ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖ :=
    fun a => div_nonneg (by linarith) (norm_nonneg _)
  have hB1 : 1 ≤ B := by rw [hB]; linarith [Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => hterm0 a)]
  have hBa : ∀ a : Fin m, K / ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖ ≤ B := by
    intro a; rw [hB]
    linarith [Finset.single_le_sum (fun a (_ : a ∈ Finset.univ) => hterm0 a) (Finset.mem_univ a)]
  refine ⟨K * B ^ m, fun l hl u' hu => ?_⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = C2.mx (l * C2.monoP w d * u') := ⟨_, rfl⟩
  rw [← hY]
  have hY0 : 0 ≤ Y := by rw [hY]; exact norm_nonneg _
  have hY1 : 1 ≤ (1 + Y) ^ m := one_le_pow₀ (by linarith)
  have hΔ : ∀ I J : Finset (Fin m), ‖C2.minorS (l * C2.monoP w d * u') I J‖ ≤ K * (1 + Y) ^ m := by
    intro I J; rw [hK, hY]; exact minor_le _ I J
  have hEB : 0 ≤ B * (1 + Y) ^ m := by positivity
  have hfin : ∀ (a : Fin m) (x : ℝ) (J : Finset (Fin m)),
      x * ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖ =
        ‖C2.minorS (l * C2.monoP w d * u') (C2.wSet w (a.val + 1)) J‖ → x ≤ B * (1 + Y) ^ m := by
    intro a x J hx
    have hcpos := norm_pos_iff.mpr (hcn a)
    calc x ≤ K * (1 + Y) ^ m / ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖ :=
          le_div_of_mul_eq_le _ _ _ _ hcpos (hΔ _ _) hx
      _ = (K / ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖) * (1 + Y) ^ m := by
          ring
      _ ≤ B * (1 + Y) ^ m := mul_le_mul_of_nonneg_right (hBa a) (by positivity)
  have hfin' : ∀ (a : Fin m) (x : ℝ) (J : Finset (Fin m)),
      x * ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖ =
        ‖C2.minorS (l * C2.monoP w d * u') J (C2.iSet m (a.val + 1))‖ → x ≤ B * (1 + Y) ^ m := by
    intro a x J hx
    have hcpos := norm_pos_iff.mpr (hcn a)
    calc x ≤ K * (1 + Y) ^ m / ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖ :=
          le_div_of_mul_eq_le _ _ _ _ hcpos (hΔ _ _) hx
      _ = (K / ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖) * (1 + Y) ^ m := by
          ring
      _ ≤ B * (1 + Y) ^ m := mul_le_mul_of_nonneg_right (hBa a) (by positivity)
  have hu_ent : ∀ a b, ‖u' a b‖ ≤ B * (1 + Y) ^ m := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · obtain ⟨ε, hε, hf⟩ := upper_minor_identity m w d hd a b h
      have e := hf l hl u' hu
      have hεn : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
      exact hfin a _ _ (by rw [← norm_mul, e, norm_mul, hεn, one_mul])
    · rw [hu.2, norm_one]; nlinarith
    · rw [hu.1 a b h, norm_zero]; exact hEB
  have hl_ent : ∀ x y, ‖l x y‖ ≤ B * (1 + Y) ^ m := by
    intro x y
    obtain ⟨a, rfl⟩ : ∃ a, y = w a := ⟨w.symm y, by simp⟩
    by_cases hx : x ∈ C2.wSet w a.val
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      have hpa : p < a := by
        simp only [C2.iSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp; rw [Fin.lt_def]; exact hp
      rw [lower_parabolic_entry_zero w d hd l hl p a hpa, norm_zero]; exact hEB
    · obtain ⟨ε, hε, hf⟩ := lower_minor_identity m w d hd a x hx
      have e := hf l hl u' hu
      have hεn : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
      exact hfin' a _ _ (by rw [← norm_mul, e, norm_mul, hεn, one_mul])
  have hX1 : 1 ≤ B * (1 + Y) ^ m := by nlinarith
  have hinvl : ∀ i j, ‖l⁻¹ i j‖ ≤ K * (B * (1 + Y) ^ m) ^ (m - 1) := fun i j => by
    rw [hK]; exact inv_entry_le l (lt_det hl.1) _ hX1 hl_ent i j
  have hinvu : ∀ i j, ‖u'⁻¹ i j‖ ≤ K * (B * (1 + Y) ^ m) ^ (m - 1) := fun i j => by
    rw [hK]; exact inv_entry_le u' (ut_det hu) _ hX1 hu_ent i j
  have hpow : K * (B * (1 + Y) ^ m) ^ (m - 1) ≤ K * B ^ m * (1 + Y) ^ ((m - 1) * m) := by
    rw [mul_pow, ← pow_mul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [mul_comm m (m - 1)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 (Nat.sub_le m 1)) (by positivity)
  have hfirst : B * (1 + Y) ^ m ≤ K * B ^ m * (1 + Y) ^ m := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      rw [hB, Finset.univ_eq_empty, Finset.sum_empty, add_zero, pow_zero, mul_one]; exact hK1
    · calc B = B ^ 1 := (pow_one B).symm
        _ ≤ B ^ m := pow_le_pow_right₀ hB1 hpos
        _ ≤ K * B ^ m := le_mul_of_one_le_left (by positivity) hK1
  have hI0 : 0 ≤ K * (B * (1 + Y) ^ m) ^ (m - 1) := by positivity
  exact ⟨(mx_le l _ hEB hl_ent).trans hfirst, (mx_le u' _ hEB hu_ent).trans hfirst,
    (mx_le _ _ hI0 hinvl).trans hpow, (mx_le _ _ hI0 hinvu).trans hpow⟩
end Formalism.FourierDecayAlt.P
