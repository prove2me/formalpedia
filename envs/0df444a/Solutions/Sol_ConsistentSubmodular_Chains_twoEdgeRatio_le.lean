-- Prove2me | solution 1 for ConsistentSubmodular.Chains.twoEdgeRatio_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:58.867261+00:00
-- url     : https://prove2.me/submissions/3de5926a-2f61-446b-b689-177b426b592d

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains
import Theorems.Thm_ConsistentSubmodular_Chains_psi_root_unique
import Theorems.Thm_ConsistentSubmodular_Chains_qStar_bounds
import Theorems.Thm_ConsistentSubmodular_Chains_hasDerivAt_twoEdgeRatio_fst
import Theorems.Thm_ConsistentSubmodular_Chains_hasDerivAt_twoEdgeRatio_snd
import Theorems.Thm_ConsistentSubmodular_Chains_twoEdgeRatio_critical

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

theorem continuous_psi : Continuous psi := by
  unfold psi
  fun_prop

/-- Existence in Proposition 1: `Ψ(1/2) = -83/16 < 0 < 24 = Ψ(1)`, so the
intermediate value theorem gives a root in `(1/2, 1)`. -/
theorem exists_psi_root : ∃ ξ : ℝ, 1 / 2 < ξ ∧ ξ < 1 ∧ psi ξ = 0 := by
  have hsub := intermediate_value_Ioo (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    continuous_psi.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (psi (1 / 2)) (psi 1) := by
    constructor <;> norm_num [psi]
  obtain ⟨ξ, ⟨h1, h2⟩, hξ⟩ := hsub hmem
  exact ⟨ξ, h1, h2, hξ⟩

/-- The root of `Ψ` in `(1/2, 1)` is `ξ⋆`. -/
theorem eq_xiStar {ξ : ℝ} (h₁ : 1 / 2 < ξ) (h₂ : ξ < 1) (hψ : psi ξ = 0) : ξ = xiStar := by
  have hset : {ξ : ℝ | 1 / 2 < ξ ∧ ξ < 1 ∧ psi ξ = 0} = {ξ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx₁, hx₂, hx⟩
      exact psi_root_unique hx₁ hx₂ h₁ h₂ hx hψ
    · rintro rfl
      exact ⟨h₁, h₂, hψ⟩
  rw [xiStar, hset, csSup_singleton]

/-- `ξ⋆` is the root of `Ψ` in `(1/2, 1)`. -/
theorem xiStar_root : 1 / 2 < xiStar ∧ xiStar < 1 ∧ psi xiStar = 0 := by
  obtain ⟨ξ, h1, h2, hψ⟩ := exists_psi_root
  have h := eq_xiStar h1 h2 hψ
  subst h
  exact ⟨h1, h2, hψ⟩

theorem xiStar_pos : 0 < xiStar := by linarith [xiStar_root.1]

theorem xiStar_lt_one : xiStar < 1 := xiStar_root.2.1

theorem quartic_eq_psi {t : ℝ} (ht : 0 < 1 + t) :
    quartic t = (1 + t) ^ 4 * psi (1 / (1 + t)) := by
  unfold quartic psi
  field_simp
  ring

theorem continuous_quartic : Continuous quartic := by
  unfold quartic
  fun_prop

theorem hasDerivAt_quartic (t : ℝ) :
    HasDerivAt quartic (4 * t ^ 3 + 3 * t ^ 2 - 44 * t - 87) t := by
  have h := ((((hasDerivAt_pow 4 t).add (hasDerivAt_pow 3 t)).sub
    ((hasDerivAt_pow 2 t).const_mul (22 : ℝ))).sub ((hasDerivAt_id t).const_mul (87 : ℝ)))
  refine (h.add_const (24 : ℝ)).congr_deriv ?_
  norm_num
  ring

/-- `Q' < 0` on `(0, 1)`, so `Q` is strictly decreasing on `[0, 1]`. -/
theorem quartic_strictAntiOn : StrictAntiOn quartic (Set.Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) continuous_quartic.continuousOn
  rw [interior_Icc]
  intro t ht
  rw [(hasDerivAt_quartic t).deriv]
  nlinarith [ht.1, ht.2, mul_pos ht.1 ht.1, mul_pos (mul_pos ht.1 ht.1) ht.1]

theorem xiStar_eq_qStar : xiStar = 1 / (1 + qStar) := by
  have h := xiStar_pos
  unfold qStar
  field_simp
  ring

theorem one_add_qStar : 1 + qStar = 1 / xiStar := by
  have h := xiStar_pos
  unfold qStar
  field_simp
  ring

/-- `Q(q) = 0`, since `Ψ(ξ⋆) = 0` and `ξ⋆ = 1/(1 + q)`. -/
theorem quartic_qStar : quartic qStar = 0 := by
  have hq : 0 < 1 + qStar := by
    rw [one_add_qStar]
    exact one_div_pos.mpr xiStar_pos
  rw [quartic_eq_psi hq, ← xiStar_eq_qStar, xiStar_root.2.2, mul_zero]

theorem qStar_pos : 0 < qStar := div_pos (by linarith [xiStar_lt_one]) xiStar_pos

theorem qStar_lt_one : qStar < 1 := by
  have h := xiStar_root.1
  unfold qStar
  rw [div_lt_one xiStar_pos]
  linarith

/-- The root of `Q` in `[0, 1]` is unique. -/
theorem eq_qStar {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) (hQ : quartic t = 0) : t = qStar :=
  quartic_strictAntiOn.injOn ⟨h₀, h₁⟩ ⟨qStar_pos.le, qStar_lt_one.le⟩ (hQ.trans quartic_qStar.symm)

/-- The identity `Q(2u² + 3u - 2) = Φ(u) (16u⁴ + 80u³ + 112u² + 60u + 59)` used in the
proof of Lemma 4. -/
theorem quartic_comp (u : ℝ) :
    quartic (2 * u ^ 2 + 3 * u - 2) =
      phi u * (16 * u ^ 4 + 80 * u ^ 3 + 112 * u ^ 2 + 60 * u + 59) := by
  unfold quartic phi
  ring

end ConsistentSubmodular.Chains

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

theorem isCompact_ratioRegion : IsCompact ratioRegion := by
  have hclosed : IsClosed ratioRegion := by
    have h1 : IsClosed {p : ℝ × ℝ | 1 ≤ p.2} := isClosed_le continuous_const continuous_snd
    have h2 : IsClosed {p : ℝ × ℝ | p.2 ≤ p.1} := isClosed_le continuous_snd continuous_fst
    have h3 : IsClosed {p : ℝ × ℝ | p.1 ≤ 8} := isClosed_le continuous_fst continuous_const
    exact h1.inter (h2.inter h3)
  refine (isCompact_Icc (a := ((1 : ℝ), (1 : ℝ))) (b := ((8 : ℝ), (8 : ℝ)))).of_isClosed_subset
    hclosed ?_
  rintro ⟨x, y⟩ ⟨hy, hyx, hx⟩
  exact ⟨⟨by simp only; linarith, by simpa using hy⟩, ⟨by simpa using hx, by simp only; linarith⟩⟩

theorem continuousOn_twoEdgeRatio :
    ContinuousOn (fun p : ℝ × ℝ => twoEdgeRatio p.1 p.2) ratioRegion := by
  intro p hp
  obtain ⟨hy, hyx, -⟩ := hp
  have hx0 : p.1 ≠ 0 := by linarith
  have hy0 : p.2 ≠ 0 := by linarith
  have hd0 : p.1 + p.2 - 1 ≠ 0 := by linarith
  apply ContinuousAt.continuousWithinAt
  unfold twoEdgeRatio
  fun_prop (disch := assumption)

/-- `R(x, y) ≤ 2/x`. -/
theorem twoEdgeRatio_le_two_div {x y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    twoEdgeRatio x y ≤ 2 / x := by
  have hx : 0 < x := by linarith
  unfold twoEdgeRatio
  rw [div_le_div_iff₀ (by linarith) hx]
  have h1 : 0 < y / x := div_pos (by linarith) hx
  have h2 : 0 < 1 / y := one_div_pos.mpr (by linarith)
  nlinarith

/-- On the boundary `y = 1`, `R(x, 1) = (x - 1)/x² ≤ 1/4`. -/
theorem twoEdgeRatio_one_le {x : ℝ} (hx : 1 ≤ x) : twoEdgeRatio x 1 ≤ 1 / 4 := by
  unfold twoEdgeRatio
  rw [div_le_iff₀ (by linarith)]
  have hx0 : 0 < x := by linarith
  have h : 1 / x ≥ 1 - x / 4 := by
    rw [ge_iff_le, le_div_iff₀ hx0]
    nlinarith [sq_nonneg (x - 2)]
  nlinarith

/-- On the boundary `y = x`, `R(x, x) = (1 - 1/x)/(2x - 1) ≤ 1/4`. -/
theorem twoEdgeRatio_diag_le {x : ℝ} (hx : 1 ≤ x) : twoEdgeRatio x x ≤ 1 / 4 := by
  have hx0 : 0 < x := by linarith
  unfold twoEdgeRatio
  rw [div_self hx0.ne', div_le_iff₀ (by linarith)]
  have h : 1 / x ≥ 1 - (2 * x - 1) / 4 := by
    rw [ge_iff_le, le_div_iff₀ hx0]
    nlinarith [sq_nonneg (x - 5 / 4)]
  linarith

end ConsistentSubmodular.Chains

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem solution {x y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) : twoEdgeRatio x y ≤ qStar := by
  obtain ⟨p, hpK, hmax⟩ := isCompact_ratioRegion.exists_isMaxOn
    ⟨((2 : ℝ), (6 / 5 : ℝ)), by norm_num [ratioRegion]⟩ continuousOn_twoEdgeRatio
  have hmax' : ∀ a b : ℝ, (a, b) ∈ ratioRegion → twoEdgeRatio a b ≤ twoEdgeRatio p.1 p.2 :=
    fun a b hab => isMaxOn_iff.mp hmax (a, b) hab
  obtain ⟨hy1, hyx', hx8⟩ := hpK
  -- `R(2, 6/5) = 17/66 > 1/4`, so the maximum is not on the boundary.
  have hR0 : (17 : ℝ) / 66 ≤ twoEdgeRatio p.1 p.2 := by
    have h := hmax' 2 (6 / 5) (by norm_num [ratioRegion])
    have h2 : twoEdgeRatio 2 (6 / 5) = 17 / 66 := by norm_num [twoEdgeRatio]
    linarith
  have hy1' : 1 < p.2 := by
    rcases eq_or_lt_of_le hy1 with h | h
    · rw [← h] at hR0
      have := twoEdgeRatio_one_le (show 1 ≤ p.1 by linarith)
      linarith
    · exact h
  have hyx'' : p.2 < p.1 := by
    rcases eq_or_lt_of_le hyx' with h | h
    · rw [h] at hR0
      have := twoEdgeRatio_diag_le (show 1 ≤ p.1 by linarith)
      linarith
    · exact h
  have hx8' : p.1 < 8 := by
    rcases eq_or_lt_of_le hx8 with h | h
    · have := twoEdgeRatio_le_two_div hy1 hyx'
      rw [h] at this hR0
      linarith
    · exact h
  have hx0 : 0 < p.1 := by linarith
  have hy0 : 0 < p.2 := by linarith
  have hD : p.1 + p.2 - 1 ≠ 0 := by linarith
  -- The first-order conditions at the interior maximum.
  have hlocx : IsLocalMax (fun t => twoEdgeRatio t p.2) p.1 := by
    filter_upwards [Ioo_mem_nhds hyx'' hx8'] with t ht
    exact hmax' t p.2 ⟨hy1, ht.1.le, ht.2.le⟩
  have hlocy : IsLocalMax (fun s => twoEdgeRatio p.1 s) p.2 := by
    filter_upwards [Ioo_mem_nhds hy1' hyx''] with s hs
    exact hmax' p.1 s ⟨hs.1.le, hs.2.le, hx8⟩
  obtain ⟨hphi, hR, hRu⟩ := twoEdgeRatio_critical hy1' hyx''
    (hlocx.hasDerivAt_eq_zero (hasDerivAt_twoEdgeRatio_fst hx0 hD))
    (hlocy.hasDerivAt_eq_zero (hasDerivAt_twoEdgeRatio_snd hx0 hy0 hD))
  -- With `u = y/x`: `R = u³ (1 + u) = 2u² + 3u - 2`, a root of `Q` in `[0, 1]`.
  have hRu' : twoEdgeRatio p.1 p.2 = 2 * (p.2 / p.1) ^ 2 + 3 * (p.2 / p.1) - 2 := by
    rw [hRu]
    unfold phi at hphi
    linear_combination hphi
  have hQ : quartic (twoEdgeRatio p.1 p.2) = 0 := by
    rw [hRu', quartic_comp, hphi, zero_mul]
  have hR1 : twoEdgeRatio p.1 p.2 ≤ 1 := by
    rw [hR, div_le_one (by positivity)]
    nlinarith
  have hRq : twoEdgeRatio p.1 p.2 = qStar :=
    eq_qStar (by rw [hR]; positivity) hR1 hQ
  by_cases hx : x ≤ 8
  · exact hRq ▸ hmax' x y ⟨hy, hyx, hx⟩
  · have h := twoEdgeRatio_le_two_div hy hyx
    have h' : 2 / x ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith [qStar_bounds.1]

end
