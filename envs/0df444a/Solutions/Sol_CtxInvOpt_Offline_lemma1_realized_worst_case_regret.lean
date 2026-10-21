-- Prove2me | solution 1 for CtxInvOpt.Offline.lemma1_realized_worst_case_regret
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:49:31.68418+00:00
-- url     : https://prove2.me/submissions/e0f28bac-d4fe-4fe3-a4e0-2a63b6ba3e3d

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry

set_option autoImplicit false
open CtxInvOpt.Offline Real

namespace CIO1
variable {d : ℕ}

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

lemma norm_of_mem (x : E d) (hx : x ∈ unitSphere d) : ‖x‖ = 1 := by
  simpa [unitSphere] using hx

lemma cap_eq (cpi cstar : E d) (hcpi : ‖cpi‖ = 1) (hcstar : ‖cstar‖ = 1) :
    regretCap (vecAngle cstar cpi) =
      if 0 < inner ℝ cstar cpi then Real.sqrt (1 - inner ℝ cstar cpi ^ 2) else 1 := by
  have h1 : cstar ≠ 0 := by intro h; rw [h] at hcstar; simp at hcstar
  have h2 : cpi ≠ 0 := by intro h; rw [h] at hcpi; simp at hcpi
  have hv : vecAngle cstar cpi = Real.arccos (inner ℝ cstar cpi) := by
    unfold vecAngle
    rw [if_neg (by tauto), hcpi, hcstar]; simp
  rw [hv]
  unfold regretCap
  have hcs := abs_real_inner_le_norm cstar cpi
  rw [hcpi, hcstar, mul_one] at hcs
  by_cases ht : 0 < inner ℝ cstar cpi
  · rw [if_pos ht, if_pos, Real.sin_arccos]
    exact Real.arccos_lt_pi_div_two.2 ht
  · rw [if_neg ht, if_neg (by rwa [Real.arccos_lt_pi_div_two])]


/-- upper bound -/
lemma upper (cpi cstar : E d) (hcpi : ‖cpi‖ = 1) (hcstar : ‖cstar‖ = 1) (δ : E d)
    (hδ : ‖δ‖ ≤ 1) (hδp : inner ℝ δ cpi ≤ 0) :
    inner ℝ δ cstar ≤ (if 0 < inner ℝ cstar cpi then Real.sqrt (1 - inner ℝ cstar cpi ^ 2) else 1) := by
  set t := inner ℝ cstar cpi with ht
  by_cases hpos : 0 < t
  · rw [if_pos hpos]
    set v : E d := cstar - t • cpi with hv
    have hvp : inner ℝ v cpi = 0 := by
      rw [hv, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hcpi]; simp [ht]
    have hvn : ‖v‖ ^ 2 = 1 - t ^ 2 := by
      rw [hv, @norm_sub_sq_real, inner_smul_right, norm_smul, hcstar, hcpi, ← ht,
        Real.norm_eq_abs, mul_one, sq_abs]
      ring
    have hvn' : ‖v‖ = Real.sqrt (1 - t ^ 2) := by
      rw [← hvn, Real.sqrt_sq (norm_nonneg _)]
    have hsplit : inner ℝ δ cstar = inner ℝ δ v + t * inner ℝ δ cpi := by
      rw [hv, inner_sub_right, inner_smul_right]; ring
    rw [hsplit]
    have h1 : inner ℝ δ v ≤ ‖δ‖ * ‖v‖ := real_inner_le_norm _ _
    have h2 : ‖δ‖ * ‖v‖ ≤ ‖v‖ := by
      calc ‖δ‖ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hδ (norm_nonneg _)
        _ = ‖v‖ := one_mul _
    have h3 : t * inner ℝ δ cpi ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpos.le hδp
    rw [← hvn']
    linarith
  · rw [if_neg hpos]
    calc inner ℝ δ cstar ≤ ‖δ‖ * ‖cstar‖ := real_inner_le_norm _ _
      _ ≤ 1 := by rw [hcstar, mul_one]; exact hδ

/-- a suitable δ for the lower bound -/
lemma exists_delta (cpi cstar : E d) (hcpi : ‖cpi‖ = 1) (hcstar : ‖cstar‖ = 1) :
    ∃ δ : E d, ‖δ‖ ≤ 1 ∧ inner ℝ δ cpi ≤ 0 ∧
      inner ℝ δ cstar =
        (if 0 < inner ℝ cstar cpi then Real.sqrt (1 - inner ℝ cstar cpi ^ 2) else 1) := by
  set t := inner ℝ cstar cpi with ht
  by_cases hpos : 0 < t
  · rw [if_pos hpos]
    set v : E d := cstar - t • cpi with hv
    have hvp : inner ℝ v cpi = 0 := by
      rw [hv, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hcpi]; simp [ht]
    have hvn : ‖v‖ ^ 2 = 1 - t ^ 2 := by
      rw [hv, @norm_sub_sq_real, inner_smul_right, norm_smul, hcstar, hcpi, ← ht,
        Real.norm_eq_abs, mul_one, sq_abs]
      ring
    have hvn' : ‖v‖ = Real.sqrt (1 - t ^ 2) := by
      rw [← hvn, Real.sqrt_sq (norm_nonneg _)]
    have hvc : inner ℝ v cstar = ‖v‖ ^ 2 := by
      rw [hvn, hv, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hcstar,
        real_inner_comm, ← ht]
      simp; ring
    by_cases hv0 : v = 0
    · refine ⟨0, by simp, by simp, ?_⟩
      rw [← hvn', hv0]; simp
    · have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
      refine ⟨‖v‖⁻¹ • v, ?_, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne']
      · rw [inner_smul_left, hvp]; simp
      · rw [inner_smul_left, hvc, ← hvn']
        simp
        field_simp
  · rw [if_neg hpos]
    refine ⟨cstar, by rw [hcstar], ?_, ?_⟩
    · exact not_lt.1 hpos
    · rw [real_inner_self_eq_norm_sq, hcstar]; norm_num

end CIO1

open CIO1 in
theorem solution {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d)
    (cpi cstar : EuclideanSpace ℝ (Fin d)) (hcpi : cpi ∈ unitSphere d)
    (hcstar : cstar ∈ unitSphere d) :
    IsGreatest
      {r : ℝ | ∃ (X : Set (EuclideanSpace ℝ (Fin n)))
          (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
          (xpi xstar : EuclideanSpace ℝ (Fin n)),
          IsActionSet X ∧ IsContext f ∧ xpi ∈ argminSet cpi X f ∧
          xstar ∈ argminSet cstar X f ∧ r = inner ℝ (f xpi - f xstar) cstar}
      (regretCap (vecAngle cstar cpi)) := by
  have hn1 : ‖cpi‖ = 1 := norm_of_mem _ hcpi
  have hn2 : ‖cstar‖ = 1 := norm_of_mem _ hcstar
  rw [cap_eq cpi cstar hn1 hn2]
  constructor
  · obtain ⟨δ, hδ, hδp, hδc⟩ := exists_delta cpi cstar hn1 hn2
    set u : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (1 : ℝ) with hu
    have hun : ‖u‖ = 1 := by simp [hu]
    have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hun]; norm_num
    set f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) := fun x => inner ℝ x u • δ with hf
    have hρ : 0 ≤ (if 0 < inner ℝ cstar cpi then Real.sqrt (1 - inner ℝ cstar cpi ^ 2) else 1) := by
      split_ifs
      · exact Real.sqrt_nonneg _
      · exact zero_le_one
    refine ⟨{0, u}, f, u, 0, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨⟨0, by simp⟩, (Set.toFinite _).isCompact, ?_⟩
      rw [Metric.diam_pair, dist_zero_left, hun]
    · refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
      rw [dist_eq_norm, dist_eq_norm, hf]
      simp only
      rw [← sub_smul, norm_smul, ← inner_sub_left, Real.norm_eq_abs]
      have h1 : |inner ℝ (x - y) u| ≤ ‖x - y‖ * ‖u‖ := abs_real_inner_le_norm _ _
      rw [hun, mul_one] at h1
      calc |inner ℝ (x - y) u| * ‖δ‖ ≤ ‖x - y‖ * 1 :=
            mul_le_mul h1 hδ (norm_nonneg _) (norm_nonneg _)
        _ = _ := by simp
    · refine ⟨by simp, fun y hy => ?_⟩
      rcases hy with rfl | rfl
      · simp only [hf, inner_zero_left, zero_smul, huu, one_smul]; exact hδp
      · exact le_rfl
    · refine ⟨by simp, fun y hy => ?_⟩
      rcases hy with rfl | rfl
      · exact le_rfl
      · simp only [hf, inner_zero_left, zero_smul, huu, one_smul]
        rw [hδc]; exact hρ
    · simp only [hf, inner_zero_left, zero_smul, huu, one_smul, sub_zero]
      exact hδc.symm
  · rintro r ⟨X, f, xpi, xstar, ⟨hXne, hXc, hXd⟩, hf, ⟨hxpiX, hxpi⟩, ⟨hxsX, hxs⟩, rfl⟩
    have hδ : ‖f xpi - f xstar‖ ≤ 1 := by
      rw [← dist_eq_norm]
      calc dist (f xpi) (f xstar) ≤ 1 * dist xpi xstar := by
            have := hf.dist_le_mul xpi xstar
            simpa using this
        _ ≤ 1 := by
            rw [one_mul]
            exact (Metric.dist_le_diam_of_mem hXc.isBounded hxpiX hxsX).trans hXd
    have hδp : inner ℝ (f xpi - f xstar) cpi ≤ 0 := by
      rw [inner_sub_left]
      have := hxpi xstar hxsX
      linarith
    exact upper cpi cstar hn1 hn2 _ hδ hδp
