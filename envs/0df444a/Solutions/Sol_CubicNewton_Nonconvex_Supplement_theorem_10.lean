-- Prove2me | solution 1 for CubicNewton.Nonconvex.Supplement.theorem_10
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:40:49.040301+00:00
-- url     : https://prove2.me/submissions/366a86fa-2eba-4f18-b5ed-78cab0f0d11c

import Mathlib
import Definitions.Def_CubicNewton_Nonconvex_Supplement_CubicDual

open scoped RealInnerProductSpace

open CubicNewton
open CubicNewton.Nonconvex
open CubicNewton.Nonconvex.Supplement

/-- Nesterov–Polyak 2006, Theorem 10, (5.2)–(5.3), p. 198. For any vector `g`, any symmetric
operator `H` and any `M > 0`:
* (5.2) the primal cubic function `v_u` attains its minimum over `ℝⁿ`, and its minimal value is
  the supremum (least upper bound, not necessarily attained) of `v_l` over the dual domain `𝒟`;
* (5.3) for every `r ∈ 𝒟`, with `h(r) = −(H + (Mr/2) I)⁻¹ g`,
  `0 ≤ v_u(h(r)) − v_l(r) = (M/12)(r + 2‖h(r)‖)(‖h(r)‖ − r)²
     = (4/(3M)) · ((r + 2‖h(r)‖)/(r + ‖h(r)‖)²) · v_l′(r)²`,
  where `v_l′` is the derivative of `v_l`. -/
theorem solution {n : ℕ} (g : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ a b : EuclideanSpace ℝ (Fin n), ⟪H a, b⟫ = ⟪a, H b⟫)
    (M : ℝ) (hM : 0 < M) :
    (∃ hs : EuclideanSpace ℝ (Fin n), (∀ h, vu g H M hs ≤ vu g H M h) ∧
        IsLUB (vl g H M '' dualDomain H M) (vu g H M hs)) ∧
      ∀ r ∈ dualDomain H M,
        0 ≤ vu g H M (hDir g H M r) - vl g H M r ∧
        vu g H M (hDir g H M r) - vl g H M r =
          M / 12 * (r + 2 * ‖hDir g H M r‖) * (‖hDir g H M r‖ - r) ^ 2 ∧
        vu g H M (hDir g H M r) - vl g H M r =
          4 / (3 * M) * ((r + 2 * ‖hDir g H M r‖) / (r + ‖hDir g H M r‖) ^ 2) *
            deriv (vl g H M) r ^ 2 := by
              have happ : ∀ r (a : EuclideanSpace ℝ (Fin n)), shiftedOp H M r a = H a + (M * r / 2) • a := by
                intro r a; simp [shiftedOp]
              have hshift : ∀ r (w : EuclideanSpace ℝ (Fin n)),
                  ⟪shiftedOp H M r w, w⟫ = ⟪H w, w⟫ + M * r / 2 * ‖w‖ ^ 2 := by
                intro r w
                rw [happ, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
              have hsym : ∀ r (a b : EuclideanSpace ℝ (Fin n)),
                  ⟪shiftedOp H M r a, b⟫ = ⟪a, shiftedOp H M r b⟫ := by
                intro r a b
                rw [happ, happ, inner_add_left, inner_add_right, hH, real_inner_smul_left,
                  real_inner_smul_right]
              have hsmall : ∀ a K : ℝ, (∀ ε : ℝ, 0 < ε → ε ≤ 1 → a ≤ ε * K) → a ≤ 0 := by
                intro a K h
                by_contra ha
                push Not at ha
                rcases le_or_gt K 0 with hK | hK
                · have := h 1 one_pos le_rfl; linarith
                · have h1 := h (min 1 (a / (2 * K))) (by positivity) (min_le_left _ _)
                  have h2 : min 1 (a / (2 * K)) * K ≤ a / (2 * K) * K :=
                    mul_le_mul_of_nonneg_right (min_le_right _ _) hK.le
                  have h3 : a / (2 * K) * K = a / 2 := by field_simp
                  linarith
              have hunit : ∀ r ∈ dualDomain H M, IsUnit (shiftedOp H M r) := by
                intro r hr
                rw [ContinuousLinearMap.isUnit_iff_bijective]
                have hinj : Function.Injective (shiftedOp H M r) := by
                  intro a b hab
                  by_contra hne
                  have := hr.2 (a - b) (sub_ne_zero.mpr hne)
                  rw [map_sub, hab, sub_self, inner_zero_left] at this
                  exact lt_irrefl _ this
                exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
              have hAinv : ∀ r ∈ dualDomain H M, ∀ x,
                  shiftedOp H M r (ContinuousLinearMap.inverse (shiftedOp H M r) x) = x := by
                intro r hr x
                have := Ring.mul_inverse_cancel _ (hunit r hr)
                rw [ContinuousLinearMap.ringInverse_eq_inverse] at this
                have := congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => T x) this
                simpa using this
              have hh : ∀ r ∈ dualDomain H M, shiftedOp H M r (hDir g H M r) = -g := by
                intro r hr
                simp [hDir, hAinv r hr]
              have key : ∀ r ∈ dualDomain H M, ∀ h, vu g H M h - vl g H M r =
                  1 / 2 * ⟪shiftedOp H M r (h - hDir g H M r), h - hDir g H M r⟫ +
                    M / 12 * (‖h‖ - r) ^ 2 * (2 * ‖h‖ + r) := by
                intro r hr h
                have hinvg : ContinuousLinearMap.inverse (shiftedOp H M r) g = -hDir g H M r := by
                  simp [hDir]
                have f1 : ⟪shiftedOp H M r (h - hDir g H M r), h - hDir g H M r⟫ =
                    ⟪shiftedOp H M r h, h⟫ - 2 * ⟪h, shiftedOp H M r (hDir g H M r)⟫ +
                      ⟪shiftedOp H M r (hDir g H M r), hDir g H M r⟫ := by
                  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hsym r h (hDir g H M r),
                    real_inner_comm (shiftedOp H M r (hDir g H M r)) h]
                  ring
                have f3 : ⟪g, h⟫ = -⟪h, shiftedOp H M r (hDir g H M r)⟫ := by
                  rw [hh r hr, inner_neg_right, real_inner_comm]; ring
                have f4 : ⟪-hDir g H M r, g⟫ = ⟪shiftedOp H M r (hDir g H M r), hDir g H M r⟫ := by
                  rw [hh r hr, inner_neg_left, inner_neg_left, real_inner_comm]
                unfold vu vl
                rw [hinvg, f1, f3, f4]; simp only [hshift]
                ring
              have hpos : ∀ r ∈ dualDomain H M, ∀ w, 0 ≤ ⟪shiftedOp H M r w, w⟫ := by
                intro r hr w
                by_cases hw : w = 0
                · simp [hw]
                · exact (hr.2 w hw).le
              have weak : ∀ r ∈ dualDomain H M, ∀ h, vl g H M r ≤ vu g H M h := by
                intro r hr h
                have e := key r hr h
                have p := hpos r hr (h - hDir g H M r)
                have q : 0 ≤ M / 12 * (‖h‖ - r) ^ 2 * (2 * ‖h‖ + r) := by
                  have := hr.1; have := norm_nonneg h; positivity
                linarith
              have hcont : Continuous (vu g H M) := by unfold vu; fun_prop
              have htend : Filter.Tendsto (vu g H M) (Filter.cocompact _) Filter.atTop := by
                have hlow : ∀ h, M / 6 * ‖h‖ ^ 3 - ‖H‖ / 2 * ‖h‖ ^ 2 - ‖g‖ * ‖h‖ ≤ vu g H M h := by
                  intro h; unfold vu
                  have h1 : |⟪g, h⟫| ≤ ‖g‖ * ‖h‖ := abs_real_inner_le_norm g h
                  have h2 : |⟪H h, h⟫| ≤ ‖H‖ * ‖h‖ ^ 2 := by
                    calc |⟪H h, h⟫| ≤ ‖H h‖ * ‖h‖ := abs_real_inner_le_norm _ _
                      _ ≤ ‖H‖ * ‖h‖ * ‖h‖ := by gcongr; exact H.le_opNorm h
                      _ = _ := by ring
                  have := neg_abs_le ⟪g, h⟫
                  have := neg_abs_le ⟪H h, h⟫
                  linarith
                have hp : Filter.Tendsto (fun t : ℝ => M / 6 * t ^ 3 - ‖H‖ / 2 * t ^ 2 - ‖g‖ * t)
                    Filter.atTop Filter.atTop := by
                  rw [Filter.tendsto_atTop_atTop]
                  intro b
                  refine ⟨1 + 6 * (‖H‖ / 2 + ‖g‖ + |b| + 1) / M, fun t ht => ?_⟩
                  have hc := norm_nonneg H
                  have hd := norm_nonneg g
                  have hb := le_abs_self b
                  have hb0 := abs_nonneg b
                  have hT : 6 * (‖H‖ / 2 + ‖g‖ + |b| + 1) / M ≥ 0 := by positivity
                  have ht1 : 1 ≤ t := by linarith
                  have hk : ‖g‖ + |b| + 1 ≤ M / 6 * t - ‖H‖ / 2 := by
                    have : 6 * (‖H‖ / 2 + ‖g‖ + |b| + 1) / M ≤ t := by linarith
                    rw [div_le_iff₀ hM] at this
                    linarith
                  have h3 : M / 6 * t - ‖H‖ / 2 ≤ t * (M / 6 * t - ‖H‖ / 2) := by
                    nlinarith
                  have h4 : |b| + 1 ≤ t * (M / 6 * t - ‖H‖ / 2) - ‖g‖ := by linarith
                  have h5 : t * (M / 6 * t - ‖H‖ / 2) - ‖g‖ ≤ t * (t * (M / 6 * t - ‖H‖ / 2) - ‖g‖) := by
                    nlinarith
                  have : M / 6 * t ^ 3 - ‖H‖ / 2 * t ^ 2 - ‖g‖ * t = t * (t * (M / 6 * t - ‖H‖ / 2) - ‖g‖) := by
                    ring
                  linarith
                exact Filter.tendsto_atTop_mono hlow (hp.comp tendsto_norm_cocompact_atTop)
              obtain ⟨hs, hmin⟩ := hcont.exists_forall_le htend
              set s := ‖hs‖ with hs_def
              have hs0 : 0 ≤ s := norm_nonneg _
              -- expansion around hs
              have hexp : ∀ d, vu g H M (hs + d) - vu g H M hs =
                  ⟪shiftedOp H M s hs + g, d⟫ + 1 / 2 * ⟪shiftedOp H M s d, d⟫ +
                    M / 12 * (‖hs + d‖ - s) ^ 2 * (2 * ‖hs + d‖ + s) := by
                intro d
                have ht2 : ‖hs + d‖ ^ 2 = ‖hs‖ ^ 2 + 2 * ⟪hs, d⟫ + ‖d‖ ^ 2 := norm_add_sq_real hs d
                unfold vu
                rw [inner_add_left, happ, inner_add_left, real_inner_smul_left, hshift, map_add,
                  inner_add_left, inner_add_right, inner_add_right, inner_add_right, hH d hs,
                  real_inner_comm (H hs) d]
                rw [hs_def]
                linear_combination (M * ‖hs‖ / 4) * ht2
              have hgrad0 : shiftedOp H M s hs + g = 0 := by
                set u := shiftedOp H M s hs + g with hu_def
                set K := 1 / 2 * |⟪shiftedOp H M s u, u⟫| + M / 12 * ‖u‖ ^ 2 * (3 * s + 2 * ‖u‖) with hK
                have hu : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ‖u‖ ^ 2 ≤ ε * K := by
                  intro ε hε hε1
                  have e := hexp (-(ε • u))
                  have m := hmin (hs + -(ε • u))
                  have hn : ‖-(ε • u)‖ = ε * ‖u‖ := by
                    rw [norm_neg, norm_smul, Real.norm_of_nonneg hε.le]
                  have ht1 : |‖hs + -(ε • u)‖ - s| ≤ ε * ‖u‖ := by
                    rw [← hn]
                    have := abs_norm_sub_norm_le (hs + -(ε • u)) hs
                    simpa using this
                  have ht2 : (‖hs + -(ε • u)‖ - s) ^ 2 ≤ (ε * ‖u‖) ^ 2 := by
                    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ht1 2
                  have ht3 : ‖hs + -(ε • u)‖ ≤ s + ε * ‖u‖ := by
                    rw [← hn]; exact norm_add_le _ _
                  have hnu := norm_nonneg u
                  have hεu : ε * ‖u‖ ≤ ‖u‖ := mul_le_of_le_one_left hnu hε1
                  have ht4 : 2 * ‖hs + -(ε • u)‖ + s ≤ 3 * s + 2 * ‖u‖ := by linarith
                  have hin : ⟪u, -(ε • u)⟫ = -(ε * ‖u‖ ^ 2) := by
                    rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
                  have hB : ⟪shiftedOp H M s (-(ε • u)), -(ε • u)⟫ = ε ^ 2 * ⟪shiftedOp H M s u, u⟫ := by
                    rw [map_neg, map_smul, inner_neg_left, inner_neg_right, real_inner_smul_left,
                      real_inner_smul_right]; ring
                  rw [hin, hB] at e
                  have hc : M / 12 * (‖hs + -(ε • u)‖ - s) ^ 2 * (2 * ‖hs + -(ε • u)‖ + s) ≤
                      M / 12 * (ε * ‖u‖) ^ 2 * (3 * s + 2 * ‖u‖) := by
                    have : 0 ≤ 2 * ‖hs + -(ε • u)‖ + s := by positivity
                    have := mul_le_mul ht2 ht4 this (sq_nonneg _)
                    rw [mul_assoc, mul_assoc]
                    exact mul_le_mul_of_nonneg_left this (by positivity)
                  have hab := le_abs_self ⟪shiftedOp H M s u, u⟫
                  have hab2 := mul_le_mul_of_nonneg_left hab (sq_nonneg ε)
                  have hK2 : ε * (ε * K) = 1 / 2 * (ε ^ 2 * |⟪shiftedOp H M s u, u⟫|) +
                      M / 12 * (ε * ‖u‖) ^ 2 * (3 * s + 2 * ‖u‖) := by rw [hK]; ring
                  have h5 : ε * ‖u‖ ^ 2 ≤ ε * (ε * K) := by
                    rw [hK2]; linarith
                  exact le_of_mul_le_mul_left h5 hε
                have := hsmall _ _ hu
                have h0 : ‖u‖ ^ 2 = 0 := le_antisymm this (sq_nonneg _)
                exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
              have hgrad : shiftedOp H M s hs = -g := eq_neg_of_add_eq_zero_left hgrad0
              have hexp' : ∀ d, 0 ≤ 1 / 2 * ⟪shiftedOp H M s d, d⟫ +
                  M / 12 * (‖hs + d‖ - s) ^ 2 * (2 * ‖hs + d‖ + s) := by
                intro d
                have := hexp d
                rw [hgrad0, inner_zero_left, zero_add] at this
                have := hmin (hs + d)
                linarith
              have hpsd : ∀ w, 0 ≤ ⟪shiftedOp H M s w, w⟫ := by
                intro w
                by_cases hw : ⟪hs, w⟫ = 0
                · have hw3 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → -⟪shiftedOp H M s w, w⟫ ≤ ε * (M / 3 * ‖w‖ ^ 3) := by
                    intro ε hε hε1
                    have e := hexp' (ε • w)
                    have hn : ‖ε • w‖ = ε * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg hε.le]
                    have ht2 : ‖hs + ε • w‖ ^ 2 = s ^ 2 + (ε * ‖w‖) ^ 2 := by
                      rw [norm_add_sq_real, real_inner_smul_right, hw, hn]; ring
                    have ht3 : ‖hs + ε • w‖ ≤ s + ε * ‖w‖ := by rw [← hn]; exact norm_add_le _ _
                    have htn := norm_nonneg (hs + ε • w)
                    have hwn := norm_nonneg w
                    have ht4 : s ≤ ‖hs + ε • w‖ := by
                      refine (pow_le_pow_iff_left₀ hs0 htn two_ne_zero).mp ?_
                      rw [ht2]; exact le_add_of_nonneg_right (sq_nonneg _)
                    have hB : ⟪shiftedOp H M s (ε • w), ε • w⟫ = ε ^ 2 * ⟪shiftedOp H M s w, w⟫ := by
                      rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
                    rw [hB] at e
                    have hc : (‖hs + ε • w‖ - s) ^ 2 * (2 * ‖hs + ε • w‖ + s) ≤ 2 * ε ^ 3 * ‖w‖ ^ 3 := by
                      have h1 : (‖hs + ε • w‖ - s) ^ 2 * (2 * ‖hs + ε • w‖ + s) ≤
                          2 * (‖hs + ε • w‖ - s) * ((‖hs + ε • w‖ - s) * (‖hs + ε • w‖ + s)) := by
                        have := mul_nonneg (sq_nonneg (‖hs + ε • w‖ - s)) hs0
                        have e2 : 2 * (‖hs + ε • w‖ - s) * ((‖hs + ε • w‖ - s) * (‖hs + ε • w‖ + s)) -
                            (‖hs + ε • w‖ - s) ^ 2 * (2 * ‖hs + ε • w‖ + s) =
                            (‖hs + ε • w‖ - s) ^ 2 * s := by ring
                        linarith
                      have h2 : (‖hs + ε • w‖ - s) * (‖hs + ε • w‖ + s) = (ε * ‖w‖) ^ 2 := by
                        linear_combination ht2
                      rw [h2] at h1
                      have h3 : 2 * (‖hs + ε • w‖ - s) * (ε * ‖w‖) ^ 2 ≤ 2 * (ε * ‖w‖) * (ε * ‖w‖) ^ 2 := by
                        gcongr; linarith
                      have e3 : 2 * (ε * ‖w‖) * (ε * ‖w‖) ^ 2 = 2 * ε ^ 3 * ‖w‖ ^ 3 := by ring
                      linarith
                    have hc' : M / 12 * (‖hs + ε • w‖ - s) ^ 2 * (2 * ‖hs + ε • w‖ + s) ≤
                        M / 12 * (2 * ε ^ 3 * ‖w‖ ^ 3) := by
                      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hc (by positivity)
                    have : ε ^ 2 * -⟪shiftedOp H M s w, w⟫ ≤ ε ^ 2 * (ε * (M / 3 * ‖w‖ ^ 3)) := by
                      linarith
                    exact le_of_mul_le_mul_left this (by positivity)
                  have := hsmall _ _ hw3
                  linarith
                · have hw0 : w ≠ 0 := by rintro rfl; simp at hw
                  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
                  set α := -2 * ⟪hs, w⟫ / ‖w‖ ^ 2 with hα
                  have hα0 : α ≠ 0 := by
                    rw [hα]; exact div_ne_zero (mul_ne_zero (by norm_num) hw) (by positivity)
                  have hαw : α * ‖w‖ ^ 2 = -2 * ⟪hs, w⟫ := by rw [hα]; field_simp
                  have e := hexp' (α • w)
                  have ht : ‖hs + α • w‖ = s := by
                    have : ‖hs + α • w‖ ^ 2 = s ^ 2 := by
                      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
                        sq_abs]
                      linear_combination α * hαw
                    exact (pow_left_inj₀ (norm_nonneg _) hs0 two_ne_zero).mp this
                  rw [ht, sub_self, map_smul, real_inner_smul_left, real_inner_smul_right] at e
                  have : 0 ≤ α ^ 2 * ⟪shiftedOp H M s w, w⟫ := by linarith
                  by_contra hneg
                  push Not at hneg
                  have := mul_neg_of_pos_of_neg (by positivity : (0:ℝ) < α ^ 2) hneg
                  linarith
              have hD : ∀ δ : ℝ, 0 < δ → s + δ ∈ dualDomain H M := by
                intro δ hδ
                refine ⟨by linarith, fun w hw => ?_⟩
                have h1 := hpsd w
                rw [hshift] at h1 ⊢
                have : 0 < ‖w‖ := norm_pos_iff.mpr hw
                have : 0 < M * δ / 2 * ‖w‖ ^ 2 := by positivity
                linarith
              have hbound : ∀ δ : ℝ, 0 < δ →
                  vu g H M hs - vl g H M (s + δ) ≤ M * δ * s ^ 2 / 4 + M / 12 * (δ ^ 2 * (3 * s + δ)) := by
                intro δ hδ
                have hr := hD δ hδ
                have k := key (s + δ) hr hs
                set h0 := hDir g H M (s + δ) with hh0
                set e := hs - h0 with he
                have hAe : shiftedOp H M (s + δ) e = (M * δ / 2) • hs := by
                  rw [he, map_sub, hh _ hr, ← hgrad]
                  simp only [happ]
                  rw [show M * (s + δ) / 2 = M * s / 2 + M * δ / 2 by ring, add_smul]
                  abel
                have i1 : ⟪shiftedOp H M (s + δ) e, e⟫ = M * δ / 2 * ⟪hs, e⟫ := by
                  rw [hAe, real_inner_smul_left]
                have i2 : ⟪shiftedOp H M (s + δ) e, e⟫ = ⟪shiftedOp H M s e, e⟫ + M * δ / 2 * ‖e‖ ^ 2 := by
                  rw [hshift, hshift]; ring
                have i3 := hpsd e
                have hMd : 0 < M * δ / 2 := by positivity
                have i4 : ‖e‖ ^ 2 ≤ ⟪hs, e⟫ := by
                  have : M * δ / 2 * ‖e‖ ^ 2 ≤ M * δ / 2 * ⟪hs, e⟫ := by linarith
                  exact le_of_mul_le_mul_left this hMd
                have i5 : ⟪hs, e⟫ ≤ s * ‖e‖ := real_inner_le_norm hs e
                have i7 : ‖e‖ ≤ s := by
                  by_contra hc
                  push Not at hc
                  have := mul_lt_mul_of_pos_left hc (lt_of_le_of_lt hs0 hc)
                  have : ‖e‖ ^ 2 = ‖e‖ * ‖e‖ := by ring
                  have : s * ‖e‖ = ‖e‖ * s := by ring
                  linarith
                have i6 : ⟪hs, e⟫ ≤ s ^ 2 := by
                  have := mul_le_mul_of_nonneg_left i7 hs0
                  have : s * s = s ^ 2 := by ring
                  linarith
                have i8 := mul_le_mul_of_nonneg_left i6 hMd.le
                have e9 : (s - (s + δ)) ^ 2 * (2 * s + (s + δ)) = δ ^ 2 * (3 * s + δ) := by ring
                have : M / 12 * (‖hs‖ - (s + δ)) ^ 2 * (2 * ‖hs‖ + (s + δ)) =
                    M / 12 * (δ ^ 2 * (3 * s + δ)) := by
                  rw [← hs_def, mul_assoc, e9]
                rw [k, i1, this]
                have : M * δ / 2 * s ^ 2 = 2 * (M * δ * s ^ 2 / 4) := by ring
                linarith
              have hderiv : ∀ r ∈ dualDomain H M,
                  HasDerivAt (vl g H M) (M / 4 * (‖hDir g H M r‖ ^ 2 - r ^ 2)) r := by
                intro r hr
                have hS : HasDerivAt (fun ρ => shiftedOp H M ρ)
                    ((M / 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) r := by
                  have h1 := ((hasDerivAt_id r).const_mul (M / 2)).smul_const
                    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
                  have h2 := h1.const_add H
                  have hfe : (fun ρ => shiftedOp H M ρ) = fun x => H + (M / 2 * id x) •
                      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
                    funext ρ; simp only [shiftedOp, id]; rw [show M * ρ / 2 = M / 2 * ρ by ring]
                  rw [hfe]; exact h2.congr_deriv (by simp)
                have hU := hasFDerivAt_ringInverse (𝕜 := ℝ) (hunit r hr).unit
                rw [IsUnit.unit_spec] at hU
                have hI := hU.comp_hasDerivAt r hS
                have hA := hI.clm_apply (hasDerivAt_const r g)
                have hin := hA.inner ℝ (hasDerivAt_const r g)
                have hfin := (hin.const_mul (-(1 / 2 : ℝ))).sub ((hasDerivAt_pow 3 r).const_mul (M / 12))
                refine (hfin.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun ρ => ?_)
                · rw [← Ring.inverse_unit, IsUnit.unit_spec]
                  simp only [Function.comp_apply, ContinuousLinearMap.ringInverse_eq_inverse, map_zero,
                    inner_zero_right, add_zero, zero_add, ContinuousLinearMap.neg_apply,
                    ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.mul_apply,
                    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_smul, map_neg]
                  have hinvg : ContinuousLinearMap.inverse (shiftedOp H M r) g = -hDir g H M r := by
                    simp [hDir]
                  have hq : ⟪ContinuousLinearMap.inverse (shiftedOp H M r) (hDir g H M r), g⟫ =
                      -‖hDir g H M r‖ ^ 2 := by
                    have hg : g = -(shiftedOp H M r (hDir g H M r)) := by rw [hh r hr, neg_neg]
                    calc ⟪ContinuousLinearMap.inverse (shiftedOp H M r) (hDir g H M r), g⟫
                        = ⟪ContinuousLinearMap.inverse (shiftedOp H M r) (hDir g H M r),
                            -(shiftedOp H M r (hDir g H M r))⟫ := by rw [← hg]
                      _ = -⟪shiftedOp H M r (ContinuousLinearMap.inverse (shiftedOp H M r) (hDir g H M r)),
                            hDir g H M r⟫ := by rw [inner_neg_right, hsym]
                      _ = -‖hDir g H M r‖ ^ 2 := by rw [hAinv r hr, real_inner_self_eq_norm_sq]
                  rw [hinvg, map_neg, neg_neg, real_inner_smul_left, hq]
                  push_cast
                  ring
                · simp only [vl, Pi.sub_apply, Function.comp_apply, ContinuousLinearMap.ringInverse_eq_inverse]
              refine ⟨⟨hs, hmin, ?_, ?_⟩, ?_⟩
              · rintro y ⟨r, hr, rfl⟩
                exact weak r hr hs
              · intro b hb
                have hb' : ∀ δ : ℝ, 0 < δ → vl g H M (s + δ) ≤ b := fun δ hδ => hb ⟨s + δ, hD δ hδ, rfl⟩
                have := hsmall (vu g H M hs - b) (M * s ^ 2 / 4 + M / 12 * (3 * s + 1)) (by
                  intro δ hδ hδ1
                  have h1 := hbound δ hδ
                  have h2 := hb' δ hδ
                  have hδ2 : δ ^ 2 ≤ δ := by
                    have := mul_le_mul_of_nonneg_left hδ1 hδ.le
                    have e : δ * δ = δ ^ 2 := by ring
                    linarith
                  have hδ3 : δ ^ 3 ≤ δ ^ 2 := by
                    have := mul_le_mul_of_nonneg_left hδ1 (sq_nonneg δ)
                    have e : δ ^ 2 * δ = δ ^ 3 := by ring
                    linarith
                  have h3 : δ ^ 2 * (3 * s + δ) ≤ δ * (3 * s + 1) := by
                    have := mul_le_mul_of_nonneg_left hδ2 (by linarith : (0:ℝ) ≤ 3 * s)
                    have e1 : δ ^ 2 * (3 * s + δ) = 3 * s * δ ^ 2 + δ ^ 3 := by ring
                    have e2 : δ * (3 * s + 1) = 3 * s * δ + δ := by ring
                    linarith
                  have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ M / 12)
                  have e3 : δ * (M * s ^ 2 / 4 + M / 12 * (3 * s + 1)) =
                      M * δ * s ^ 2 / 4 + M / 12 * (δ * (3 * s + 1)) := by ring
                  linarith)
                linarith
              · intro r hr
                have k := key r hr (hDir g H M r)
                rw [sub_self, map_zero, inner_zero_left, mul_zero, zero_add] at k
                have hr0 := hr.1
                have hn0 := norm_nonneg (hDir g H M r)
                have eq1 : vu g H M (hDir g H M r) - vl g H M r =
                    M / 12 * (r + 2 * ‖hDir g H M r‖) * (‖hDir g H M r‖ - r) ^ 2 := by
                  rw [k]; ring
                refine ⟨?_, eq1, ?_⟩
                · rw [eq1]
                  exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _)
                · rw [(hderiv r hr).deriv, eq1]
                  rcases eq_or_lt_of_le (add_nonneg hr0 hn0) with h0 | h0
                  · have hr' : r = 0 := by linarith
                    have hn' : ‖hDir g H M r‖ = 0 := by linarith
                    rw [hn', hr']; ring
                  · field_simp
                    ring
