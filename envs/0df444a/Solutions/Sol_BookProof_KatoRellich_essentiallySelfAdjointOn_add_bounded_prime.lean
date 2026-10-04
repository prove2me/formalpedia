-- Prove2me | solution 1 for BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded_prime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T15:30:36.630998+00:00
-- url     : https://prove2.me/submissions/3bec4556-4b55-4f19-91d2-f91cc84da7f8

import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterKatoRellichRelative
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterA4

set_option autoImplicit false

section P0cec59b0_aux

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

open BookProof.FarisLavine in
lemma P0cec59b0_im_inner_self (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H) (v : D) :
    (inner ℂ (H v) (v : F) : ℂ).im = 0 := by
  have h1 := hH v v
  have h2 : (inner ℂ (v : F) (H v) : ℂ) = (starRingEnd ℂ) (inner ℂ (H v) (v : F)) := by
    rw [inner_conj_symm]
  rw [h2] at h1
  have := congrArg Complex.im h1
  simp only [Complex.conj_im] at this
  linarith

open BookProof.FarisLavine in
lemma P0cec59b0_norm_le (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H) (z : ℂ) (hz : |z.im| = 1)
    (v : D) : ‖(v : F)‖ ≤ ‖H v - (starRingEnd ℂ z) • (v : F)‖ := by
  set u := H v - (starRingEnd ℂ z) • (v : F) with hu
  have hin : (inner ℂ u (v : F) : ℂ) =
      inner ℂ (H v) (v : F) - z * ((‖(v : F)‖ : ℂ) ^ 2) := by
    rw [hu, inner_sub_left, inner_smul_left, Complex.conj_conj, inner_self_eq_norm_sq_to_K]
    rfl
  have him : (inner ℂ u (v : F) : ℂ).im = -(z.im * ‖(v : F)‖ ^ 2) := by
    rw [hin, Complex.sub_im, P0cec59b0_im_inner_self H hH v, ← Complex.ofReal_pow,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hab : |(inner ℂ u (v : F) : ℂ).im| ≤ ‖u‖ * ‖(v : F)‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  rw [him, abs_neg, abs_mul, hz, abs_of_nonneg (sq_nonneg _), one_mul] at hab
  by_contra hlt
  push Not at hlt
  have hv : 0 < ‖(v : F)‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  nlinarith

open BookProof.FarisLavine in
lemma P0cec59b0_defic [CompleteSpace F] (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H) (z : ℂ)
    (hz : |z.im| = 1) (hd : DeficiencyTrivialAt D H z) (B : F →L[ℂ] F)
    (hB : ∀ x y : F, (inner ℂ (B x) y : ℂ) = inner ℂ x (B y)) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c < 1) (hBc : ∀ x, ‖B x‖ ≤ c * ‖x‖) :
    DeficiencyTrivialAt D (H + (B.toLinearMap ∘ₗ D.subtype)) z := by
  intro w hw
  set T : D →ₗ[ℂ] F := H - (starRingEnd ℂ z) • D.subtype with hT
  have hTv : ∀ v : D, T v = H v - (starRingEnd ℂ z) • (v : F) := fun v => rfl
  have hperp : (LinearMap.range T)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    apply hd u
    intro v
    have h0 : (inner ℂ (T v) u : ℂ) = 0 :=
      (Submodule.mem_orthogonal _ _).1 hu (T v) (LinearMap.mem_range_self T v)
    rw [hTv, inner_sub_left, inner_smul_left, Complex.conj_conj] at h0
    exact sub_eq_zero.1 h0
  have hdense : (LinearMap.range T).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.mpr hperp
  have hwcl : w ∈ closure ((LinearMap.range T : Submodule ℂ F) : Set F) := by
    rw [← Submodule.topologicalClosure_coe, hdense]
    trivial
  have hkey : ∀ v : D, (inner ℂ (T v) w : ℂ) = -(inner ℂ (v : F) (B w)) := by
    intro v
    have h := hw v
    simp only [LinearMap.add_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      Submodule.subtype_apply, inner_add_left] at h
    rw [hTv, inner_sub_left, inner_smul_left, Complex.conj_conj, ← hB]
    linear_combination h
  by_contra hne
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hne
  set ε : ℝ := (1 - c) * ‖w‖ / (2 * (1 + c)) with hε
  have hεpos : 0 < ε := by
    rw [hε]; apply div_pos
    · exact mul_pos (by linarith) hwpos
    · linarith
  obtain ⟨u, ⟨v, rfl⟩, hdist⟩ := Metric.mem_closure_iff.1 hwcl ε hεpos
  rw [dist_eq_norm] at hdist
  have h1 : ‖(v : F)‖ ≤ ‖T v‖ := by rw [hTv]; exact P0cec59b0_norm_le H hH z hz v
  have h2 : ‖T v‖ ≤ ‖w‖ + ε := by
    have := norm_sub_norm_le (T v) w
    rw [norm_sub_rev] at this
    linarith
  have h3 : ‖(inner ℂ (T v) w : ℂ)‖ ≤ ‖(v : F)‖ * (c * ‖w‖) := by
    rw [hkey, norm_neg]
    calc ‖(inner ℂ (v : F) (B w) : ℂ)‖ ≤ ‖(v : F)‖ * ‖B w‖ := norm_inner_le_norm _ _
      _ ≤ ‖(v : F)‖ * (c * ‖w‖) := by gcongr; exact hBc w
  have hsplit : (inner ℂ w w : ℂ) = inner ℂ (w - T v) w + inner ℂ (T v) w := by
    rw [inner_sub_left]; ring
  have hre : (inner ℂ w w : ℂ).re = ‖w‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    show (((‖w‖ : ℂ)) ^ 2).re = _
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have h4 : ‖w‖ ^ 2 ≤ ‖w - T v‖ * ‖w‖ + ‖(inner ℂ (T v) w : ℂ)‖ := by
    rw [← hre, hsplit, Complex.add_re]
    have a1 := (Complex.re_le_norm (inner ℂ (w - T v) w : ℂ)).trans (norm_inner_le_norm _ _)
    have a2 := Complex.re_le_norm (inner ℂ (T v) w : ℂ)
    linarith
  have h5 : ‖w‖ ^ 2 ≤ ε * ‖w‖ + (‖w‖ + ε) * (c * ‖w‖) := by
    have e1 : ‖w - T v‖ * ‖w‖ ≤ ε * ‖w‖ :=
      mul_le_mul_of_nonneg_right hdist.le (norm_nonneg _)
    have e2 : ‖(v : F)‖ * (c * ‖w‖) ≤ (‖w‖ + ε) * (c * ‖w‖) :=
      mul_le_mul_of_nonneg_right (h1.trans h2) (mul_nonneg hc0 (norm_nonneg _))
    linarith
  have h6 : ‖w‖ ≤ ε + (‖w‖ + ε) * c := by
    have : ‖w‖ * ‖w‖ ≤ (ε + (‖w‖ + ε) * c) * ‖w‖ := by nlinarith
    exact le_of_mul_le_mul_right this hwpos
  have h7 : ε * (1 + c) = (1 - c) * ‖w‖ / 2 := by
    rw [hε]; field_simp
  nlinarith

open BookProof.FarisLavine in
lemma P0cec59b0_step [CompleteSpace F] (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H)
    (hesa : EssentiallySelfAdjointOn D H) (B : F →L[ℂ] F)
    (hB : ∀ x y : F, (inner ℂ (B x) y : ℂ) = inner ℂ x (B y)) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c < 1) (hBc : ∀ x, ‖B x‖ ≤ c * ‖x‖) :
    SymmetricOn D (H + (B.toLinearMap ∘ₗ D.subtype)) ∧
      EssentiallySelfAdjointOn D (H + (B.toLinearMap ∘ₗ D.subtype)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    simp only [LinearMap.add_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      Submodule.subtype_apply, inner_add_left, inner_add_right, hH x y, hB]
  · exact P0cec59b0_defic H hH Complex.I (by simp) hesa.1 B hB c hc0 hc hBc
  · exact P0cec59b0_defic H hH (-Complex.I) (by simp) hesa.2 B hB c hc0 hc hBc

lemma P0cec59b0_realsmul_symm (B : F →L[ℂ] F)
    (hB : ∀ x y : F, (inner ℂ (B x) y : ℂ) = inner ℂ x (B y)) (r : ℝ) :
    ∀ x y : F, (inner ℂ (((r : ℂ) • B) x) y : ℂ) = inner ℂ x (((r : ℂ) • B) y) := by
  intro x y
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal, hB]

end P0cec59b0_aux

open BookProof.FarisLavine in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F} [CompleteSpace F] (H : D →ₗ[ℂ] F)
    (hH : SymmetricOn D H) (hesa : EssentiallySelfAdjointOn D H) (B : F →L[ℂ] F)
    (hB : ∀ x y : F, (inner ℂ (B x) y : ℂ) = inner ℂ x (B y)) :
    EssentiallySelfAdjointOn D (H + (B.toLinearMap ∘ₗ D.subtype)) := by
  set N : ℕ := ⌈‖B‖⌉₊ + 1 with hN
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  have hNgt : ‖B‖ < N := by
    rw [hN]; push_cast
    have := Nat.le_ceil ‖B‖
    linarith
  set B' : F →L[ℂ] F := (((N : ℝ)⁻¹ : ℝ) : ℂ) • B with hB'
  have hB'sym := P0cec59b0_realsmul_symm B hB ((N : ℝ)⁻¹)
  have hc0 : 0 ≤ ‖B‖ / N := div_nonneg (norm_nonneg _) hNpos.le
  have hc1 : ‖B‖ / N < 1 := (div_lt_one hNpos).2 hNgt
  have hB'c : ∀ x, ‖B' x‖ ≤ ‖B‖ / N * ‖x‖ := by
    intro x
    rw [hB', ContinuousLinearMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hNpos)]
    calc (N : ℝ)⁻¹ * ‖B x‖ ≤ (N : ℝ)⁻¹ * (‖B‖ * ‖x‖) := by
          gcongr; exact B.le_opNorm x
      _ = ‖B‖ / N * ‖x‖ := by ring
  have key : ∀ k : ℕ,
      SymmetricOn D (H + (((((k : ℝ) / N : ℝ) : ℂ) • B).toLinearMap ∘ₗ D.subtype)) ∧
      EssentiallySelfAdjointOn D
        (H + (((((k : ℝ) / N : ℝ) : ℂ) • B).toLinearMap ∘ₗ D.subtype)) := by
    intro k
    induction k with
    | zero =>
      have : H + (((((0 : ℕ) : ℝ) / N : ℝ) : ℂ) • B).toLinearMap ∘ₗ D.subtype = H := by
        ext x; simp
      rw [this]; exact ⟨hH, hesa⟩
    | succ k ih =>
      have heq : H + (((((k + 1 : ℕ) : ℝ) / N : ℝ) : ℂ) • B).toLinearMap ∘ₗ D.subtype =
          (H + (((((k : ℝ) / N : ℝ) : ℂ) • B).toLinearMap ∘ₗ D.subtype)) +
            (B'.toLinearMap ∘ₗ D.subtype) := by
        ext x
        simp only [hB', LinearMap.add_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
          Submodule.subtype_apply, ContinuousLinearMap.smul_apply, add_assoc, ← add_smul]
        congr 2
        push_cast
        ring
      rw [heq]
      exact P0cec59b0_step _ ih.1 ih.2 B' hB'sym (‖B‖ / N) hc0 hc1 hB'c
  have hfin := (key N).2
  have : (((N : ℝ) / N : ℝ) : ℂ) • B = B := by
    rw [div_self hNpos.ne', Complex.ofReal_one, one_smul]
  rw [this] at hfin
  exact hfin
