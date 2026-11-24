-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.prekopa_leindler
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:27:26.359158+00:00
-- url     : https://prove2.me/submissions/5ce4d03b-f446-4473-af45-62554195d540

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_append_measurable
public import Theorems.Thm_P2M_GaussianPerimeter_VolumeComparison_append_measurable__f5f150faf8d6
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_append_linear
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_fix_measurable
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_fix_apply
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_lintegral_fix_eq_lmarginal
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_lintegral_fix_lintegral_eq_lintegral
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_prekopa_leindler_1d_fin1
attribute [local fun_prop] GaussianPerimeter.VolumeComparison.append_measurable
attribute [local fun_prop] GaussianPerimeter.VolumeComparison.append_measurable'
attribute [local fun_prop] GaussianPerimeter.VolumeComparison.fix_measurable

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution
    {d : ℕ} {θ : ℝ} {f g h : (Fin (d + 1) → ℝ) → ENNReal} (hθfgh : PLConditions (d + 1) θ f g h)
    : ENNReal.ofReal ((1 - θ) ^ ((d + 1) * (1 - θ)) * θ ^ ((d + 1) * θ))⁻¹
      * (∫⁻ x, f x) ^ (1 - θ) * (∫⁻ x, g x) ^ θ ≤ ∫⁻ x, h x := by

  induction d using Nat.case_strong_induction_on with
  | hz => simpa using (prekopa_leindler_1d_fin1 hθfgh)
  | hi d hd =>

  -- The goal is to prove the result for Fin (d + 2) → ℝ.
  let ⟨hθ0, hθ1, hf_measurable, hg_measurable, hh_measurable, hfgh⟩ := hθfgh

  -- The inductive hypotheses for Fin 1 → ℝ and Fin (d + 1) → ℝ
  have hyp_0 : ∀ {f g h : (Fin 1 → ℝ) → ENNReal}, PLConditions 1 θ f g h →
      ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)⁻¹
      * (∫⁻ (x : Fin 1 → ℝ), f x)^(1-θ) * (∫⁻ (x : Fin 1 → ℝ), g x)^θ
      ≤ ∫⁻ (x : Fin 1 → ℝ), h x := by
    have := hd 0
    simp_all
  have hyp_d : ∀ {f g h : (Fin (d + 1) → ℝ) → ENNReal}, PLConditions (d + 1) θ f g h →
      ENNReal.ofReal ((1-θ)^((d+1)*(1-θ)) * θ^((d+1)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 1) → ℝ), f x)^(1-θ) * (∫⁻ (x : Fin (d + 1) → ℝ), g x)^θ
      ≤ ∫⁻ (x : Fin (d + 1) → ℝ), h x := by
    have := hd d
    simp_all

  -- F, G, H are f, g, h with the last coordinate marginalized out
  let F : (Fin (d + 1) → ℝ) → ENNReal := fun x1 ↦ ∫⁻ x, (fix f x1) x
  let G : (Fin (d + 1) → ℝ) → ENNReal := fun x1 ↦ ∫⁻ x, (fix g x1) x
  let H : (Fin (d + 1) → ℝ) → ENNReal :=
    fun x1 ↦ ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ) * ∫⁻ x, (fix h x1) x
  -- F', G', H' are F, G, H written using lmarginal, to use theorems written for lmarginal
  let F' : (Fin (d + 1) → ℝ) → ENNReal :=
    fun x1 ↦ (∫⋯∫⁻_{⟨d + 1, by simp⟩}, f ∂fun _ ↦ volume) (append x1 default)
  let G' : (Fin (d + 1) → ℝ) → ENNReal :=
    fun x1 ↦ (∫⋯∫⁻_{⟨d + 1, by simp⟩}, g ∂fun _ ↦ volume) (append x1 default)
  let H' : (Fin (d + 1) → ℝ) → ENNReal :=
    fun x1 ↦ ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)
      * (∫⋯∫⁻_{⟨d + 1, by simp⟩}, h ∂fun _ ↦ volume) (append x1 default)
  have h_F_eq_F' : F = F' := by unfold F F'; ext; rw [lintegral_fix_eq_lmarginal]
  have h_G_eq_G' : G = G' := by unfold G G'; ext; rw [lintegral_fix_eq_lmarginal]
  have h_H_eq_H' : H = H' := by unfold H H'; ext; rw [lintegral_fix_eq_lmarginal]
  -- Apply the inductive hypothesis to F, G, H
  have happend : Measurable (fun x : Fin (d + 1) → ℝ => append x default) :=
    append_measurable' default
  have hF_measurable : Measurable F := by
    rw [h_F_eq_F']
    exact (Measurable.lmarginal (fun _ : Fin (d + 2) => volume)
      (s := {⟨d + 1, by omega⟩}) hf_measurable).comp happend
  have hG_measurable : Measurable G := by
    rw [h_G_eq_G']
    exact (Measurable.lmarginal (fun _ : Fin (d + 2) => volume)
      (s := {⟨d + 1, by omega⟩}) hg_measurable).comp happend
  have hH_measurable : Measurable H := by
    rw [h_H_eq_H']
    apply measurable_const.mul
    exact (Measurable.lmarginal (fun _ : Fin (d + 2) => volume)
      (s := {⟨d + 1, by omega⟩}) hh_measurable).comp happend
  have factor_pos : 0 < (1-θ)^(1-θ)*θ^θ :=
    mul_pos (Real.rpow_pos_of_pos (by linarith) (1-θ)) (Real.rpow_pos_of_pos (by linarith) θ)
  have fix_plconditions : ∀ x1 y1 : Fin (d + 1) → ℝ,
      PLConditions 1 θ (fix f x1) (fix g y1) (fix h (x1 + y1)) := by
    intro x1 y1
    exact ⟨
      hθ0, hθ1, by fun_prop, by fun_prop, by fun_prop, by
        intro x y
        rw [fix_apply, fix_apply, fix_apply]
        have h_result : f (append x1 x)^(1-θ) * g (append y1 y)^θ ≤ h (append x1 x + append y1 y) :=
          hfgh (append x1 x) (append y1 y)
        rw [append_linear x1 y1 x y] at h_result
        exact h_result
    ⟩
  have marginal_pl_condition : ∀ x1 y1 : Fin (d + 1) → ℝ,
      (F x1)^(1-θ) * (G y1)^θ ≤ H (x1 + y1) := by
    intro x1 y1
    calc
      (F x1)^(1-θ) * (G y1)^θ = 1 * (F x1)^(1-θ) * (G y1)^θ := by ring
      _ = (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ) * (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ))⁻¹)
          * (F x1)^(1-θ) * (G y1)^θ := by
        congr
        symm
        exact ENNReal.mul_inv_cancel
          (ENNReal.ofReal_ne_zero_iff.mpr factor_pos) (Ne.symm ENNReal.top_ne_ofReal)
      _ = (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ) * ENNReal.ofReal ((1 - θ)^(1-θ)*θ^θ)⁻¹)
          * (F x1)^(1-θ) * (G y1)^θ := by
        congr
        rw [ENNReal.ofReal_inv_of_pos (by linarith)]
      _ = ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)
          * (ENNReal.ofReal ((1 - θ)^(1-θ)*θ^θ)⁻¹ * (F x1)^(1-θ) * (G y1)^θ) := by
        ring
      _ ≤ H (x1 + y1) := by
        rw [ENNReal.mul_le_mul_iff_right
          (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith)
          (by simp only [ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true])]
        exact hyp_0 (fix_plconditions x1 y1)
  have result_d : ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 1) → ℝ), F x)^(1-θ)
      * (∫⁻ (x : Fin (d + 1) → ℝ), G x)^θ
      ≤ ∫⁻ (x : Fin (d + 1) → ℝ), H x :=
    hyp_d ⟨hθ0, hθ1, hF_measurable, hG_measurable, hH_measurable, marginal_pl_condition⟩

  -- Now perform manipulations and use Fubini-Tonelli to conclude the theorem for f, g, h.
  have result_d_2 : (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ))⁻¹ *
      (ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 2) → ℝ), f x)^(1-θ) *
      (∫⁻ (x : Fin (d + 2) → ℝ), g x)^θ) ≤ ∫⁻ (x : Fin (d + 2) → ℝ), h x := by
    unfold F G H at result_d
    have extract_constant :
        ∫⁻ (x : Fin (d + 1) → ℝ), ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ) * ∫⁻ t, (fix h x) t
        = ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ) * ∫⁻ (x : Fin (d + 1) → ℝ), ∫⁻ t, (fix h x) t := by
      rw [lintegral_const_mul']
      exact Ne.symm ENNReal.top_ne_ofReal
    rw [lintegral_fix_lintegral_eq_lintegral hf_measurable,
      lintegral_fix_lintegral_eq_lintegral hg_measurable,
      extract_constant,
      lintegral_fix_lintegral_eq_lintegral hh_measurable,
      ← ENNReal.inv_mul_le_iff
        (ENNReal.ofReal_ne_zero_iff.mpr factor_pos) (Ne.symm ENNReal.top_ne_ofReal)] at result_d
    exact result_d
  have rewrite_lhs_of_result_d_2 :
      (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ))⁻¹ * (ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 2) → ℝ), f x)^(1-θ) * (∫⁻ (x : Fin (d + 2) → ℝ), g x)^θ)
      = (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ))⁻¹ * ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 2) → ℝ), f x)^(1-θ) * (∫⁻ (x : Fin (d + 2) → ℝ), g x)^θ := by ring
  have combine_consts_of_result_d_2 : (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ))⁻¹
      * ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹ =
      ENNReal.ofReal ((1-θ)^((d+2)*(1-θ))*θ^((d+2)*θ))⁻¹ := calc
    _ = ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ)⁻¹
        * ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹ := by
      congr; exact Eq.symm (ENNReal.ofReal_inv_of_pos factor_pos)
    _ = ENNReal.ofReal (((1-θ)^(1-θ)*θ^θ)⁻¹ * ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹) :=
      Eq.symm (ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt factor_pos)))
    _ = ENNReal.ofReal (((1-θ)^(1-θ)*(1-θ)^((d+1)*(1-θ))) * (θ^θ * θ^((d+1)*θ)))⁻¹ := by grind
    _ = ENNReal.ofReal ((1-θ)^((d+2)*(1-θ))*θ^((d+2)*θ))⁻¹ := by
      congr
      · exact Eq.symm <| Real.rpow_of_add_eq
          (by linarith) (ne_of_gt <| mul_pos (by linarith) (by linarith)) (by grind)
      exact Eq.symm <| Real.rpow_of_add_eq
        (by linarith) (ne_of_gt <| mul_pos (by linarith) (by linarith)) (by grind)
  have result_d_3 : ENNReal.ofReal ((1-θ)^((d+2)*(1-θ))*θ^((d+2)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 2) → ℝ), f x) ^ (1 - θ) * (∫⁻ (x : Fin (d + 2) → ℝ), g x) ^ θ ≤
      ∫⁻ (x : Fin (d + 2) → ℝ), h x := by
    rw [rewrite_lhs_of_result_d_2, combine_consts_of_result_d_2] at result_d_2
    exact result_d_2
  have rewrite_const_of_result_d_3 :
      ENNReal.ofReal ((1-θ)^((d+2)*(1-θ))*θ^((d+2)*θ))⁻¹ =
      ENNReal.ofReal ((1-θ)^((↑(d+1)+1)*(1-θ))*θ^((↑(d+1)+1)*θ))⁻¹ := by
    congr 5
    · simp only [Nat.cast_add, Nat.cast_one]
      ring
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  change ENNReal.ofReal ((1-θ)^((↑(d+1)+1)*(1-θ))*θ^((↑(d+1)+1)*θ))⁻¹
    * (∫⁻ (x : Fin (d + 2) → ℝ), f x)^(1-θ) * (∫⁻ (x : Fin (d + 2) → ℝ), g x)^θ
    ≤ ∫⁻ (x : Fin (d + 2) → ℝ), h x
  rw [rewrite_const_of_result_d_3] at result_d_3
  exact result_d_3
end GaussianPerimeter.VolumeComparison
