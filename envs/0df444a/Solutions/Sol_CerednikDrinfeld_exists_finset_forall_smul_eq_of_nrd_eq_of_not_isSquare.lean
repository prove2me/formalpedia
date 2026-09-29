-- Prove2me | solution 1 for CerednikDrinfeld.exists_finset_forall_smul_eq_of_nrd_eq_of_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1891046b-f8f6-5949-b9b3-d00f37f2c6c1

import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.NumberTheory.Real.Irrational
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_det_eq_nrd_of_injective
import Theorems.Thm_CerednikDrinfeld_exists_isUnitOf_nrd_eq_one_of_mem_fuchsianGroup
import Theorems.Thm_QuaternionAlgebra_IsOrder_finite_setOf_mem_forall_abs_apply_le
import Theorems.Thm_CerednikDrinfeld_exists_isCompact_forall_exists_fuchsianGroup_smul_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_finset_forall_smul_eq_of_nrd_eq_of_not_isSquare

set_option autoImplicit false

open scoped MatrixGroups Topology TensorProduct Pointwise Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

namespace CMOrbit11

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ}

theorem hdiv_of (hB : IsIndefiniteRamifiedExactlyAt a b q q') : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x :=
  fun x hx => QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB x hx

omit [Fact q'.Prime] in
theorem ne_zero_and_ne_zero (hB : IsIndefiniteRamifiedExactlyAt a b q q') : a ≠ 0 ∧ b ≠ 0 := by
  have key : ∀ y : ℍ[ℚ, a, b], y ≠ 0 → y * y = 0 → False := by
    intro y hy hyy
    obtain ⟨u, rfl⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB y hy
    apply hy
    calc (u : ℍ[ℚ, a, b]) = ↑u⁻¹ * (↑u * ↑u) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = 0 := by rw [hyy, mul_zero]
  refine ⟨fun h0 => key ⟨0, 1, 0, 0⟩ ?_ ?_, fun h0 => key ⟨0, 0, 1, 0⟩ ?_ ?_⟩
  · intro h; simpa using congrArg QuaternionAlgebra.imI h
  · ext <;> simp [h0]
  · intro h; simpa using congrArg QuaternionAlgebra.imJ h
  · ext <;> simp [h0]

theorem trace_eq_trd (ha : a ≠ 0) (hb : b ≠ 0)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (x : ℍ[ℚ, a, b]) :
    (ι x).trace = ((trd x : ℚ) : ℝ) := by
  have h1 := QuaternionAlgebra.det_eq_nrd_of_injective ha hb ι hι x
  have h2 := QuaternionAlgebra.det_eq_nrd_of_injective ha hb ι hι (x + 1)
  rw [map_add, map_one] at h2
  have e1 : (ι x + 1).det = (ι x).det + (ι x).trace + 1 := by
    simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
    ring
  have e2 : nrd (x + 1) = nrd x + trd x + 1 := by
    obtain ⟨x₀, x₁, x₂, x₃⟩ := x
    simp [nrd, trd]
    ring
  have : (ι x).trace = (ι x + 1).det - (ι x).det - 1 := by rw [e1]; ring
  rw [this, h1, h2, e2]; push_cast; ring

theorem not_mem_center (ha : a ≠ 0) (hb : b ≠ 0)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (ν : ℤ) (hsq : ¬ IsSquare ν) (α : ℍ[ℚ, a, b]) (hα : nrd α = (ν : ℚ))
    (g : GL (Fin 2) ℝ) (hg : ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ι α) :
    g ∉ Subgroup.center (GL (Fin 2) ℝ) := by
  intro hc
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hc
  obtain ⟨c, hc⟩ := hc

  have hcomm : ∀ y : ℍ[ℚ, a, b], α * y = y * α := by
    intro y
    apply hι
    rw [map_mul, map_mul, ← hg]
    change g.val * ι y = ι y * g.val
    rw [← hc]
    exact (Matrix.scalar_commute c (fun r' => (Commute.all c r')) (ι y)).eq
  obtain ⟨r, x₁, x₂, x₃⟩ := α
  have hi := hcomm ⟨0, 1, 0, 0⟩
  have hj := hcomm ⟨0, 0, 1, 0⟩
  have h2 : x₂ = 0 := by
    have := congrArg QuaternionAlgebra.imK hi; simp at this; linarith
  have h3 : x₃ = 0 := by
    have := congrArg QuaternionAlgebra.imJ hi; simp at this
    rcases mul_eq_zero.mp (by linarith : a * x₃ = 0) with h | h
    · exact absurd h ha
    · exact h
  have h1' : x₁ = 0 := by
    have := congrArg QuaternionAlgebra.imK hj; simp at this; linarith
  subst h1' h2 h3
  have hν : IsSquare ((ν : ℤ) : ℚ) := ⟨r, by rw [← hα]; simp [nrd, pow_two]⟩
  exact hsq (Rat.isSquare_intCast_iff.mp hν)

end CMOrbit11

namespace CMOrbit11

theorem entries_of_smul_eq (g : GL (Fin 2) ℝ) (hpos : 0 < g.val.det) (τ : UpperHalfPlane) (hτ : g • τ = τ) :
    g 1 1 - g 0 0 = -2 * g 1 0 * (τ : ℂ).re ∧
    g 0 1 = - g 1 0 * ((τ : ℂ).re ^ 2 + (τ : ℂ).im ^ 2) ∧
    g.val.det = (g 0 0 + g 1 1) ^ 2 / 4 + (g 1 0) ^ 2 * (τ : ℂ).im ^ 2 := by
  have hq := (UpperHalfPlane.gl_smul_eq_self_iff_quadratic hpos).mp hτ
  have hre := congrArg Complex.re hq
  have him := congrArg Complex.im hq
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
    Complex.add_im, Complex.mul_im, Complex.neg_im, Complex.zero_re, Complex.zero_im, zero_mul, sub_zero,
    Complex.sub_re, Complex.sub_im, add_zero, neg_zero] at hre him
  have hy : 0 < (τ : ℂ).im := τ.im_pos
  set x := (τ : ℂ).re with hx
  set y := (τ : ℂ).im with hy'
  have h1 : g 1 1 - g 0 0 = -2 * g 1 0 * x := by
    have : (g 1 0 * (2 * x) + (g 1 1 - g 0 0)) * y = 0 := by linear_combination him
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hy.ne'
  have h2 : g 0 1 = - g 1 0 * (x ^ 2 + y ^ 2) := by linear_combination (-1 : ℝ) * hre + x * h1
  refine ⟨h1, h2, ?_⟩
  have hdet : g.val.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two _
  rw [hdet, h2]
  linear_combination (-(g 1 1 - g 0 0 - 2 * g 1 0 * x) / 4) * h1

theorem abs_entry_le (g : GL (Fin 2) ℝ) (ν X Y y₀ : ℝ) (hy₀ : 0 < y₀) (hν : 0 ≤ ν) (hdet : g.val.det = ν)
    (hpos : 0 < g.val.det) (τ : UpperHalfPlane) (hτ : g • τ = τ)
    (hX : |(τ : ℂ).re| ≤ X) (hY : (τ : ℂ).im ≤ Y) (hy : y₀ ≤ (τ : ℂ).im) :
    ∀ i j : Fin 2, |g i j| ≤ (ν + ν / y₀ ^ 2) * (2 + 2 * X ^ 2 + (X ^ 2 + Y ^ 2) ^ 2) + 1 := by
  obtain ⟨h1, h2, h3⟩ := entries_of_smul_eq g hpos τ hτ
  set x := (τ : ℂ).re with hx
  set y := (τ : ℂ).im with hy'
  set c := g 1 0 with hc
  set s := g 0 0 + g 1 1 with hs
  have hypos : 0 < y := lt_of_lt_of_le hy₀ hy
  have hX0 : 0 ≤ X := le_trans (abs_nonneg _) hX
  have hx2 : x ^ 2 ≤ X ^ 2 := by
    have := abs_le.mp hX
    nlinarith [this.1, this.2, hX0]
  have hy2 : y ^ 2 ≤ Y ^ 2 := by nlinarith [hY, hypos]
  have hcy : c ^ 2 * y ^ 2 ≤ ν := by nlinarith [h3, hdet, sq_nonneg s]
  have hs2 : s ^ 2 ≤ 4 * ν := by nlinarith [h3, hdet, sq_nonneg (c * y)]

  set A := ν with hA
  set B := ν / y₀ ^ 2 with hB
  set P := (X ^ 2 + Y ^ 2) ^ 2 with hP
  set Q := X ^ 2 with hQ
  have hB0 : 0 ≤ B := by positivity
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hc2 : c ^ 2 ≤ B := by
    rw [hB, le_div_iff₀ (by positivity)]
    calc c ^ 2 * y₀ ^ 2 ≤ c ^ 2 * y ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact pow_le_pow_left₀ hy₀.le hy 2
      _ ≤ ν := hcy
  have hcx : (c * x) ^ 2 ≤ B * Q := by
    rw [mul_pow]; exact mul_le_mul hc2 hx2 (sq_nonneg _) hB0
  have hM : (A + B) * (2 + 2 * Q + P) = 2*A + 2*(A*Q) + A*P + 2*B + 2*(B*Q) + B*P := by ring
  have hAQ : 0 ≤ A * Q := mul_nonneg hν hQ0
  have hAP : 0 ≤ A * P := mul_nonneg hν hP0
  have hBQ : 0 ≤ B * Q := mul_nonneg hB0 hQ0
  have hBP : 0 ≤ B * P := mul_nonneg hB0 hP0

  have ha2 : (g 0 0) ^ 2 ≤ (A + B) * (2 + 2 * Q + P) := by
    have ha : g 0 0 = s / 2 + c * x := by linarith [h1, hs]
    have e : 2 * (s / 2) ^ 2 + 2 * (c * x) ^ 2 - (s / 2 + c * x) ^ 2 = (s / 2 - c * x) ^ 2 := by ring
    have hsq : (s / 2 + c * x) ^ 2 ≤ 2 * (s / 2) ^ 2 + 2 * (c * x) ^ 2 := by
      linarith only [e, sq_nonneg (s / 2 - c * x)]
    have hs4 : (s / 2) ^ 2 ≤ A := by
      have : (s / 2) ^ 2 = s ^ 2 / 4 := by ring
      rw [this, hA]; linarith [hs2]
    rw [ha, hM]; linarith only [hsq, hs4, hcx, hAQ, hAP, hBQ, hBP, hB0, hν, hA]
  have hd2 : (g 1 1) ^ 2 ≤ (A + B) * (2 + 2 * Q + P) := by
    have hd : g 1 1 = s / 2 - c * x := by linarith [h1, hs]
    have e : 2 * (s / 2) ^ 2 + 2 * (c * x) ^ 2 - (s / 2 - c * x) ^ 2 = (s / 2 + c * x) ^ 2 := by ring
    have hsq : (s / 2 - c * x) ^ 2 ≤ 2 * (s / 2) ^ 2 + 2 * (c * x) ^ 2 := by
      linarith only [e, sq_nonneg (s / 2 + c * x)]
    have hs4 : (s / 2) ^ 2 ≤ A := by
      have : (s / 2) ^ 2 = s ^ 2 / 4 := by ring
      rw [this, hA]; linarith [hs2]
    rw [hd, hM]; linarith only [hsq, hs4, hcx, hAQ, hAP, hBQ, hBP, hB0, hν, hA]
  have hb2 : (g 0 1) ^ 2 ≤ (A + B) * (2 + 2 * Q + P) := by
    have hxy : (x ^ 2 + y ^ 2) ^ 2 ≤ P := by
      rw [hP]; exact pow_le_pow_left₀ (by positivity) (add_le_add hx2 hy2) 2
    have : (g 0 1) ^ 2 = c ^ 2 * (x ^ 2 + y ^ 2) ^ 2 := by rw [h2]; ring
    have : (g 0 1) ^ 2 ≤ B * P := by
      rw [this]; exact mul_le_mul hc2 hxy (by positivity) hB0
    rw [hM]; linarith only [this, hAQ, hAP, hBQ, hBP, hB0, hν, hA]
  have hc2' : (g 1 0) ^ 2 ≤ (A + B) * (2 + 2 * Q + P) := by
    rw [hM]; linarith only [hc2, hAQ, hAP, hBQ, hBP, hB0, hν, hA, hc]
  have key : ∀ e : ℝ, e ^ 2 ≤ (A + B) * (2 + 2 * Q + P) → |e| ≤ (A + B) * (2 + 2 * Q + P) + 1 := by
    intro e he
    rcases le_or_gt |e| 1 with h | h
    · have : 0 ≤ (A + B) * (2 + 2 * Q + P) := by rw [hM]; linarith
      linarith
    · have : |e| ≤ |e| ^ 2 := by nlinarith
      rw [sq_abs] at this; linarith
  intro i j
  fin_cases i <;> fin_cases j
  · exact key _ ha2
  · exact key _ hb2
  · exact key _ hc2'
  · exact key _ hd2

end CMOrbit11

namespace CMOrbit11

variable {a b : ℚ}

theorem box_of_isCompact {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ X Y y₀ : ℝ, 0 < y₀ ∧ ∀ τ ∈ K, |(τ : ℂ).re| ≤ X ∧ (τ : ℂ).im ≤ Y ∧ y₀ ≤ (τ : ℂ).im := by
  by_cases hne : K.Nonempty
  · obtain ⟨X₁, hX₁⟩ := (hK.image UpperHalfPlane.continuous_re).bddAbove
    obtain ⟨X₂, hX₂⟩ := (hK.image UpperHalfPlane.continuous_re).bddBelow
    obtain ⟨Y, hY⟩ := (hK.image UpperHalfPlane.continuous_im).bddAbove
    obtain ⟨τm, hτm, hmin⟩ := hK.exists_isMinOn hne UpperHalfPlane.continuous_im.continuousOn
    refine ⟨max X₁ (-X₂), Y, τm.im, τm.im_pos, fun τ hτ => ⟨?_, ?_, ?_⟩⟩
    · rw [UpperHalfPlane.coe_re, abs_le]
      constructor
      · have := hX₂ ⟨τ, hτ, rfl⟩
        linarith [le_max_right X₁ (-X₂)]
      · exact le_trans (hX₁ ⟨τ, hτ, rfl⟩) (le_max_left _ _)
    · rw [UpperHalfPlane.coe_im]; exact hY ⟨τ, hτ, rfl⟩
    · rw [UpperHalfPlane.coe_im]; exact hmin hτ
  · refine ⟨0, 0, 1, one_pos, fun τ hτ => absurd ⟨τ, hτ⟩ hne⟩

theorem nrd_mul' (ha : a ≠ 0) (hb : b ≠ 0)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (y z : ℍ[ℚ, a, b]) :
    nrd (y * z) = nrd y * nrd z := by
  have h := QuaternionAlgebra.det_eq_nrd_of_injective ha hb ι hι (y * z)
  rw [map_mul, Matrix.det_mul, QuaternionAlgebra.det_eq_nrd_of_injective ha hb ι hι y,
    QuaternionAlgebra.det_eq_nrd_of_injective ha hb ι hι z] at h
  exact_mod_cast h.symm

end CMOrbit11

open CMOrbit11 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (ν : ℤ) (hν : 0 < ν) (hsq : ¬ IsSquare ν) :
    ∃ F : Finset UpperHalfPlane,
      ∀ (τ : UpperHalfPlane) (α : ℍ[ℚ, a, b]) (g : GL (Fin 2) ℝ),
        α ∈ Λ → nrd α = (ν : ℚ) → (g : Matrix (Fin 2) (Fin 2) ℝ) = ι α → g • τ = τ →
          ∃ γ ∈ fuchsianGroup Λ ι, ∃ τ₀ ∈ F, γ • τ₀ = τ := by
  classical
  obtain ⟨ha, hb⟩ := ne_zero_and_ne_zero hB
  have hdiv := hdiv_of hB
  obtain ⟨K, hK, hKorb⟩ :=
    CerednikDrinfeld.exists_isCompact_forall_exists_fuchsianGroup_smul_mem hdiv Λ hΛ.1 ι hι
  obtain ⟨X, Y, y₀, hy₀, hbox⟩ := box_of_isCompact hK
  set C : ℝ := ((ν : ℝ) + (ν : ℝ) / y₀ ^ 2) * (2 + 2 * X ^ 2 + (X ^ 2 + Y ^ 2) ^ 2) + 1 with hC
  have hfin := QuaternionAlgebra.IsOrder.finite_setOf_mem_forall_abs_apply_le hdiv Λ hΛ.1 ι hι C

  have hdetα : ∀ (α : ℍ[ℚ, a, b]) (g : GL (Fin 2) ℝ), nrd α = (ν : ℚ) →
      ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ι α → g.val.det = (ν : ℝ) := by
    intro α g hn hg
    change ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = _
    rw [hg, QuaternionAlgebra.det_eq_nrd_of_injective ha hb ι hι α, hn]; push_cast; rfl
  have hνR : (0 : ℝ) < (ν : ℝ) := by exact_mod_cast hν

  let T : Set UpperHalfPlane := {τ | τ ∈ K ∧ ∃ α : ℍ[ℚ, a, b], α ∈ Λ ∧ nrd α = (ν : ℚ) ∧
    ∃ g : GL (Fin 2) ℝ, ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ι α ∧ g • τ = τ}
  have hT : T.Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion hfin (t := fun α => {τ : UpperHalfPlane |
      nrd α = (ν : ℚ) ∧ ∃ g : GL (Fin 2) ℝ, ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ι α ∧ g • τ = τ})
      ?_) ?_
    · intro α _
      apply Set.Subsingleton.finite
      rintro τ₁ ⟨hn, g₁, hg₁, h₁⟩ τ₂ ⟨-, g₂, hg₂, h₂⟩
      have hg12 : g₁ = g₂ := Units.ext (hg₁.trans hg₂.symm)
      subst hg12
      have hpos : 0 < g₁.val.det := by rw [hdetα α g₁ hn hg₁]; exact hνR
      have hell := UpperHalfPlane.isElliptic_of_exists_smul_eq_self hpos
        (not_mem_center ha hb ι hι ν hsq α hn g₁ hg₁) ⟨τ₁, h₁⟩
      rw [UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt hpos hell] at h₁ h₂
      exact h₁.trans h₂.symm
    · rintro τ ⟨hτK, α, hαΛ, hn, g, hg, hgt⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      refine ⟨α, ⟨hαΛ, ?_⟩, hn, g, hg, hgt⟩
      obtain ⟨hXτ, hYτ, hyτ⟩ := hbox τ hτK
      have hdet := hdetα α g hn hg
      intro i j
      have := abs_entry_le g (ν : ℝ) X Y y₀ hy₀ hνR.le hdet (by rw [hdet]; exact hνR) τ hgt hXτ hYτ hyτ i j
      rw [← hg]
      exact this
  refine ⟨hT.toFinset, ?_⟩
  intro τ α g hαΛ hn hg hgt
  obtain ⟨γ, hγ, hγK⟩ := hKorb τ
  obtain ⟨u, hu, hu1, hγu⟩ :=
    CerednikDrinfeld.exists_isUnitOf_nrd_eq_one_of_mem_fuchsianGroup ha hb Λ hΛ.1 ι hι γ hγ
  obtain ⟨huΛ, v, hvΛ, huv, hvu⟩ := hu
  refine ⟨γ⁻¹, inv_mem hγ, γ • τ, ?_, inv_smul_smul γ τ⟩
  rw [Set.Finite.mem_toFinset]
  refine ⟨hγK, u * α * v, hΛ.1.mul_mem (hΛ.1.mul_mem huΛ hαΛ) hvΛ, ?_, γ * g * γ⁻¹, ?_, ?_⟩
  · have hv1 : nrd v = 1 := by
      have := nrd_mul' ha hb ι hι u v
      rw [huv, nrd_one, hu1, one_mul] at this
      exact this.symm
    rw [nrd_mul' ha hb ι hι, nrd_mul' ha hb ι hι, hu1, hv1, hn, one_mul, mul_one]
  · have hγv : ((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ι v := by
      rw [Matrix.coe_units_inv]
      apply Matrix.inv_eq_right_inv
      rw [hγu, ← map_mul, huv, map_one]
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hγu, hg, hγv]
  · rw [mul_smul, mul_smul, inv_smul_smul, hgt]

end S_CerednikDrinfeld_exists_finset_forall_smul_eq_of_nrd_eq_of_not_isSquare
end P2MW
export P2MW.S_CerednikDrinfeld_exists_finset_forall_smul_eq_of_nrd_eq_of_not_isSquare (solution)
