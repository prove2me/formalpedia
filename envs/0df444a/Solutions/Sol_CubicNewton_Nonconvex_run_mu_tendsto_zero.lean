-- Prove2me | solution 1 for CubicNewton.Nonconvex.run_mu_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:15:31.959054+00:00
-- url     : https://prove2.me/submissions/4629d178-7abb-4b8b-98da-55c521589ead

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun
import Definitions.Def_CubicNewton_Nonconvex_muMeasure

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

theorem aux_rmt_mus_sym_int {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ interior F) (u w : EuclideanSpace ℝ (Fin n)) :
    ⟪H z u, w⟫ = ⟪H z w, u⟫ := by
  have h1 : ∀ᶠ y in nhds z, HasFDerivAt f (innerSL ℝ (g y)) y := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hz] with y hy
    have := hf y hy
    rw [hasGradientAt_iff_hasFDerivAt] at this
    have e : innerSL ℝ (g y) = (InnerProductSpace.toDual ℝ _ (g y) : _ →L[ℝ] ℝ) := by
      ext v; simp [InnerProductSpace.toDual_apply_apply]
    rw [e]; exact this
  have h2 : HasFDerivAt (fun y => innerSL ℝ (g y)) ((innerSL ℝ).comp (H z)) z :=
    (innerSL ℝ).hasFDerivAt.comp z (hg z (interior_subset hz))
  have := second_derivative_symmetric_of_eventually h1 h2 u w
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using this

theorem aux_rmt_mus_sym {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ F) (u w : EuclideanSpace ℝ (Fin n)) :
    ⟪H z u, w⟫ = ⟪H z w, u⟫ := by
  have hcont : ContinuousOn H F := by
    have : LipschitzOnWith (Real.toNNReal L) H F := LipschitzOnWith.of_dist_le_mul
      (fun x hx y hy => by
        rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL.le]; exact hLip x hx y hy)
    exact this.continuousOn
  have hsub : F ⊆ closure (interior F) := by
    rw [hF_convex.closure_interior_eq_closure_of_nonempty_interior hF_int, hF_closed.closure_eq]
  have key : Set.EqOn (fun y => ⟪H y u, w⟫) (fun y => ⟪H y w, u⟫) F :=
    Set.EqOn.of_subset_closure (fun y hy => aux_rmt_mus_sym_int F f g H hf hg y hy u w)
      ((hcont.clm_apply continuousOn_const).inner continuousOn_const)
      ((hcont.clm_apply continuousOn_const).inner continuousOn_const)
      interior_subset hsub
  exact key hz

theorem aux_rmt_mus_foc {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x T : EuclideanSpace ℝ (Fin n))
    (hT : CubicNewton.Shared.IsCubicStep g H M x T)
    (hsym : ∀ u w, ⟪H x u, w⟫ = ⟪H x w, u⟫) (w : EuclideanSpace ℝ (Fin n)) :
    ⟪g x, w⟫ + ⟪H x (T - x), w⟫ + M / 2 * ‖T - x‖ * ⟪T - x, w⟫ = 0 := by
  set h := T - x with hh
  let ψ : ℝ → ℝ := fun t => CubicNewton.Shared.cubicModel g H M x (T + t • w)
  have hmin : IsLocalMin ψ 0 := Filter.Eventually.of_forall (fun t => by
    simp only [ψ, zero_smul, add_zero]; exact hT _)
  have hlin : HasDerivAt (fun t : ℝ => h + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const w).const_add h
  have hlin2 : HasDerivAt (fun t : ℝ => H x h + t • H x w) (H x w) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (H x w)).const_add (H x h)
  have hnorm0 := (hasFDerivAt_norm_rpow (h + (0:ℝ) • w) (p := 3) (by norm_num)).comp_hasDerivAt
      (0:ℝ) hlin
  have hD := ((hasDerivAt_const (0:ℝ) (g x)).inner ℝ hlin).add
    (((hlin2.inner ℝ hlin).const_mul (1/2)).add (hnorm0.const_mul (M/6)))
  have hD' := hD.congr_of_eventuallyEq (f₁ := ψ) (Filter.Eventually.of_forall fun t => by
    simp only [ψ, CubicNewton.Shared.cubicModel, Pi.add_apply, Function.comp_apply]
    have : T + t • w - x = h + t • w := by rw [hh]; abel
    rw [this, map_add, map_smul, Real.rpow_ofNat]
    ring)
  have h0 := hmin.hasDerivAt_eq_zero hD'
  have e3 : ‖h‖ ^ ((3:ℝ) - 2) = ‖h‖ := by norm_num
  simp only [inner_zero_left, zero_smul, add_zero, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul, e3] at h0
  rw [hsym w h] at h0
  linarith

theorem aux_rmt_mus_ident {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x T : EuclideanSpace ℝ (Fin n))
    (hsym : ∀ u w, ⟪H x u, w⟫ = ⟪H x w, u⟫)
    (hfoc : ∀ w, ⟪g x, w⟫ + ⟪H x (T - x), w⟫ + M / 2 * ‖T - x‖ * ⟪T - x, w⟫ = 0)
    (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    CubicNewton.Shared.cubicModel g H M x (T + t • v) - CubicNewton.Shared.cubicModel g H M x T
      = 1 / 2 * t ^ 2 * (⟪H x v, v⟫ + M / 2 * ‖T - x‖ * ‖v‖ ^ 2)
        + M / 12 * (‖T - x + t • v‖ - ‖T - x‖) ^ 2 * (2 * ‖T - x + t • v‖ + ‖T - x‖) := by
  have hf := hfoc v
  have hs := hsym v (T - x)
  set h := T - x with hh
  have e1 : T + t • v - x = h + t • v := by rw [hh]; abel
  have e2 : T - x = h := rfl
  have hρ : ‖h + t • v‖ ^ 2 = ‖h‖ ^ 2 + 2 * t * ⟪h, v⟫ + t ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  simp only [CubicNewton.Shared.cubicModel, e1, e2]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  linear_combination t * hf + (M * ‖h‖ / 4) * hρ + (t / 2) * hs

theorem aux_rmt_mus_nonneg (a K : ℝ) (hK : 0 ≤ K) (h : ∀ ε > 0, -(ε * K) ≤ a) : 0 ≤ a := by
  by_contra ha
  push Not at ha
  have hK1 : 0 < K + 1 := by linarith
  have := h (-a / (K + 1)) (div_pos (by linarith) hK1)
  rw [div_mul_eq_mul_div, neg_mul, neg_div, neg_neg, div_le_iff₀ hK1] at this
  nlinarith

theorem aux_rmt_mus_soc {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n))
    (hT : CubicNewton.Shared.IsCubicStep g H M x T)
    (hsym : ∀ u w, ⟪H x u, w⟫ = ⟪H x w, u⟫)
    (hfoc : ∀ w, ⟪g x, w⟫ + ⟪H x (T - x), w⟫ + M / 2 * ‖T - x‖ * ⟪T - x, w⟫ = 0)
    (v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ ⟪H x v, v⟫ + M / 2 * ‖T - x‖ * ‖v‖ ^ 2 := by
  have key : ∀ t : ℝ, ∀ u, 0 ≤ 1 / 2 * t ^ 2 * (⟪H x u, u⟫ + M / 2 * ‖T - x‖ * ‖u‖ ^ 2)
        + M / 12 * (‖T - x + t • u‖ - ‖T - x‖) ^ 2 * (2 * ‖T - x + t • u‖ + ‖T - x‖) := by
    intro t u
    rw [← aux_rmt_mus_ident g H M x T hsym hfoc t u]
    exact sub_nonneg.mpr (hT _)
  set h := T - x with hh
  have caseR : ∀ u, ⟪h, u⟫ ≠ 0 → 0 ≤ ⟪H x u, u⟫ + M / 2 * ‖h‖ * ‖u‖ ^ 2 := by
    intro u hu
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    set t := -2 * ⟪h, u⟫ / ‖u‖ ^ 2 with ht_def
    have hρ : ‖h + t • u‖ = ‖h‖ := by
      have : ‖h + t • u‖ ^ 2 = ‖h‖ ^ 2 := by
        rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
          ht_def]
        field_simp
        ring
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this
    have ht : t ≠ 0 := by
      rw [ht_def]
      exact div_ne_zero (mul_ne_zero (by norm_num) hu) (by positivity)
    have := key t u
    rw [hρ, sub_self] at this
    have ht2 : 0 < t ^ 2 := by positivity
    nlinarith
  by_cases hh0 : h = 0
  · -- the step is zero
    have hK : 0 ≤ M / 3 * ‖v‖ ^ 3 := by positivity
    apply aux_rmt_mus_nonneg _ (M / 3 * ‖v‖ ^ 3) hK
    intro ε hε
    have := key ε v
    rw [hh0, zero_add, norm_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hε] at this
    rw [hh0, norm_zero]
    have hε2 : 0 < ε ^ 2 := by positivity
    nlinarith
  · by_cases hv : ⟪h, v⟫ = 0
    · have hhh : ⟪h, h⟫ ≠ 0 := by
        rw [real_inner_self_eq_norm_sq]
        exact pow_ne_zero _ (norm_ne_zero_iff.mpr hh0)
      have hQh := caseR h hhh
      apply aux_rmt_mus_nonneg _ (⟪H x h, h⟫ + M / 2 * ‖h‖ * ‖h‖ ^ 2) hQh
      intro ε hε
      set δ := Real.sqrt ε
      have hδ : 0 < δ := Real.sqrt_pos.mpr hε
      have hδ2 : δ ^ 2 = ε := Real.sq_sqrt hε.le
      have hr2 : ⟪h, h⟫ = ‖h‖ ^ 2 := real_inner_self_eq_norm_sq h
      have hnh : 0 < ‖h‖ := norm_pos_iff.mpr hh0
      have hp : ⟪h, v + δ • h⟫ ≠ 0 := by
        rw [inner_add_right, real_inner_smul_right, hv, hr2]; positivity
      have hm : ⟪h, v - δ • h⟫ ≠ 0 := by
        rw [inner_sub_right, real_inner_smul_right, hv, hr2]
        have : 0 < δ * ‖h‖ ^ 2 := by positivity
        linarith
      have h1 := caseR _ hp
      have h2 := caseR _ hm
      rw [norm_add_sq_real] at h1
      rw [norm_sub_sq_real] at h2
      simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right, real_inner_smul_left, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hδ] at h1 h2
      rw [← hδ2]
      nlinarith
    · exact caseR v hv

theorem aux_rmt_mus_taylor {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ) (hF_convex : Convex ℝ F)
    (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (hTF : T ∈ F) :
    ‖g T - g x - H x (T - x)‖ ≤ L / 2 * ‖T - x‖ ^ 2 := by
  set h := T - x with hh
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • h ∈ F := fun t ht =>
    hF_convex.add_smul_sub_mem hx hTF ht
  let ψ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => g (x + t • h) - g x - t • H x h
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (H (x + t • h) h - H x h) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have h2 := (hg _ (hmem t ht)).comp_hasDerivAt t h1
    have h3 := (h2.sub_const (g x)).sub ((hasDerivAt_id t).smul_const (H x h))
    exact (h3.congr_deriv (by simp)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => rfl)
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => L / 2 * ‖h‖ ^ 2 * t ^ 2) (L * ‖h‖ ^ 2 * t) t := by
    intro t
    have := (hasDerivAt_pow 2 t).const_mul (L / 2 * ‖h‖ ^ 2)
    exact this.congr_deriv (by norm_num <;> ring)
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := ψ) (a := 0) (b := 1)
    (f' := fun t => H (x + t • h) h - H x h)
    (B := fun t => L / 2 * ‖h‖ ^ 2 * t ^ 2) (B' := fun t => L * ‖h‖ ^ 2 * t)
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hderiv t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [ψ]) hB
    (fun t ht => by
       have hmt := hmem t (Set.Ico_subset_Icc_self ht)
       calc ‖H (x + t • h) h - H x h‖ = ‖(H (x + t • h) - H x) h‖ := by
              rw [ContinuousLinearMap.sub_apply]
         _ ≤ ‖H (x + t • h) - H x‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
         _ ≤ L * ‖x + t • h - x‖ * ‖h‖ := by gcongr; exact hLip _ hmt _ hx
         _ = L * ‖h‖ ^ 2 * t := by
              rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]; ring)
  have h1 := key (x := 1) ⟨zero_le_one, le_rfl⟩
  have e : x + h = T := by rw [hh]; abel
  simp only [ψ, one_smul, e, one_pow, mul_one] at h1
  exact h1

theorem aux_rmt_mu_step_le {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (hTF : T ∈ F)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    muMeasure L M g H T ≤ ‖x - T‖ := by
  have hsym := aux_rmt_mus_sym F f g H L hF_closed hF_convex hF_int hf hg hL hLip x hx
  have hfoc := aux_rmt_mus_foc g H M x T hT hsym
  have hsoc := aux_rmt_mus_soc g H M hM x T hT hsym hfoc
  have htay := aux_rmt_mus_taylor F g H L hF_convex hg hLip x T hx hTF
  rw [norm_sub_rev x T]
  set r := ‖T - x‖ with hr_def
  have hr0 : 0 ≤ r := norm_nonneg _
  unfold muMeasure
  apply max_le
  · have hvec : g x + H x (T - x) = -((M / 2 * r) • (T - x)) := by
      set w := g x + H x (T - x) + (M / 2 * r) • (T - x) with hw
      have h1 : ⟪w, w⟫ = 0 := by
        have := hfoc w
        conv_lhs => rw [hw]
        rw [inner_add_left, inner_add_left, real_inner_smul_left]
        linarith
      rw [inner_self_eq_zero] at h1
      rw [eq_neg_iff_add_eq_zero]
      exact h1
    have hgT : ‖g T‖ ≤ (L + M) / 2 * r ^ 2 := by
      have e : g T = (g T - g x - H x (T - x)) + (g x + H x (T - x)) := by abel
      rw [e, hvec]
      calc _ ≤ ‖g T - g x - H x (T - x)‖ + ‖-((M / 2 * r) • (T - x))‖ := norm_add_le _ _
        _ ≤ L / 2 * r ^ 2 + M / 2 * r * r := by
            gcongr
            rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        _ = _ := by ring
    rw [Real.sqrt_le_left hr0]
    have hLM : 0 < L + M := by linarith
    calc 2 / (L + M) * ‖g T‖ ≤ 2 / (L + M) * ((L + M) / 2 * r ^ 2) := by gcongr
      _ = r ^ 2 := by field_simp
  · have hlam : -(L + M / 2) * r ≤ CubicNewton.Shared.lamMin (H T) := by
      unfold CubicNewton.Shared.lamMin
      rcases isEmpty_or_nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) with hE | hE
      · rw [Real.iInf_of_isEmpty]; nlinarith
      · apply le_ciInf
        intro v
        have hv : ‖(v : EuclideanSpace ℝ (Fin n))‖ = 1 := by simpa using v.2
        have h1 := hsoc v
        have h2 : |⟪(H T - H x) v, v⟫| ≤ L * r := by
          calc |⟪(H T - H x) v, v⟫| ≤ ‖(H T - H x) v‖ * ‖(v : EuclideanSpace ℝ (Fin n))‖ :=
                abs_real_inner_le_norm _ _
            _ ≤ ‖H T - H x‖ * ‖(v : EuclideanSpace ℝ (Fin n))‖ *
                  ‖(v : EuclideanSpace ℝ (Fin n))‖ := by
                gcongr; exact ContinuousLinearMap.le_opNorm _ _
            _ ≤ L * r := by rw [hv, mul_one, mul_one]; exact hLip T hTF x hx
        have h3 : ⟪H T v, v⟫ = ⟪H x v, v⟫ + ⟪(H T - H x) v, v⟫ := by
          rw [ContinuousLinearMap.sub_apply, inner_sub_left]; ring
        rw [hv] at h1
        have := neg_abs_le ⟪(H T - H x) v, v⟫
        nlinarith
    have hpos : 0 < 2 * L + M := by linarith
    calc -(2 / (2 * L + M)) * CubicNewton.Shared.lamMin (H T)
          ≤ -(2 / (2 * L + M)) * (-(L + M / 2) * r) := by
            apply mul_le_mul_of_nonpos_left hlam
            have : 0 < 2 / (2 * L + M) := by positivity
            linarith
      _ = r := by field_simp

lemma aux_rmt_rsc_model_line {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x h : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    CubicNewton.Shared.cubicModel g H M x (x + t • h) =
      t * ⟪g x, h⟫ + (1 / 2) * (t ^ 2 * ⟪H x h, h⟫) + M / 6 * (|t| ^ 3 * ‖h‖ ^ 3) := by
  unfold CubicNewton.Shared.cubicModel
  simp only [add_sub_cancel_left, map_smul, real_inner_smul_left, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow]
  ring

lemma aux_rmt_rsc_model_decrease {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x T : EuclideanSpace ℝ (Fin n)) (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    CubicNewton.Shared.cubicModel g H M x T ≤ -(M / 12) * ‖T - x‖ ^ 3 := by
  set h := T - x with hh
  have hxT : T = x + (1 : ℝ) • h := by simp [h]
  set a := ⟪g x, h⟫ with ha_def
  set b := ⟪H x h, h⟫ with hb_def
  set c := M / 6 * ‖h‖ ^ 3 with hc_def
  have hφ : ∀ t : ℝ, CubicNewton.Shared.cubicModel g H M x (x + t • h) =
      t * a + (1 / 2) * (t ^ 2 * b) + M / 6 * (|t| ^ 3 * ‖h‖ ^ 3) :=
    fun t => aux_rmt_rsc_model_line g H M x h t
  have h1 : CubicNewton.Shared.cubicModel g H M x T = a + (1 / 2) * b + c := by
    rw [hxT, hφ]; simp only [abs_one, one_pow, one_mul, hc_def]
  have hmin : ∀ t : ℝ,
      a + (1 / 2) * b + c ≤ t * a + (1 / 2) * (t ^ 2 * b) + M / 6 * (|t| ^ 3 * ‖h‖ ^ 3) := by
    intro t; rw [← h1, ← hφ]; exact hT _
  have ha : a ≤ 0 := by
    have := hmin (-1)
    simp only [abs_neg, abs_one, one_pow, one_mul, neg_one_sq, neg_mul] at this
    linarith
  have hBt : ∀ t ∈ Set.Ioo (0 : ℝ) 1, a + b / 2 * (t + 1) + c * (t ^ 2 + t + 1) ≤ 0 := by
    intro t ht
    have := hmin t
    rw [abs_of_pos ht.1] at this
    have key : 0 ≤ (t - 1) * (a + b / 2 * (t + 1) + c * (t ^ 2 + t + 1)) := by
      rw [hc_def]; linear_combination this
    nlinarith [ht.2]
  have hB : a + b + 3 * c ≤ 0 := by
    have hcont : Continuous (fun t : ℝ => a + b / 2 * (t + 1) + c * (t ^ 2 + t + 1)) := by
      fun_prop
    have htend : Filter.Tendsto (fun t : ℝ => a + b / 2 * (t + 1) + c * (t ^ 2 + t + 1))
        (nhdsWithin 1 (Set.Iio 1)) (nhds (a + b / 2 * (1 + 1) + c * (1 ^ 2 + 1 + 1))) :=
      (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Iio 1),
        a + b / 2 * (t + 1) + c * (t ^ 2 + t + 1) ≤ 0 :=
      Filter.mem_of_superset (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)) hBt
    have := le_of_tendsto htend hev
    linarith
  rw [h1]
  have : -(M / 12) * ‖h‖ ^ 3 = -c / 2 := by rw [hc_def]; ring
  rw [this]
  linarith

theorem aux_rmt_sum_cubes {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (L₀ : ℝ) (hL₀ : 0 < L₀) (hL₀L : L₀ ≤ L)
    (fstar : ℝ) (hfstar : ∀ y ∈ F, fstar ≤ f y)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ) (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M) :
    Summable (fun i => ‖x i - x (i + 1)‖ ^ 3) ∧
      ∑' i, ‖x i - x (i + 1)‖ ^ 3 ≤ 12 / L₀ * (f x₀ - fstar) := by
  have hdec : ∀ k, f (x (k + 1)) ≤ f (x k) - L₀ / 12 * ‖x k - x (k + 1)‖ ^ 3 := by
    intro k
    have h1 := hrun.accept k
    have h2 := aux_rmt_rsc_model_decrease g H (M k) (x k) (x (k + 1)) (hrun.step k)
    have h3 := (hrun.param_mem k).1
    rw [norm_sub_rev] at h2
    have h4 : 0 ≤ ‖x k - x (k + 1)‖ ^ 3 := by positivity
    nlinarith
  have hmono : ∀ k, f (x k) ≤ f x₀ := by
    intro k
    induction k with
    | zero => rw [hrun.init]
    | succ k ih =>
      have := hdec k
      have : 0 ≤ ‖x k - x (k + 1)‖ ^ 3 := by positivity
      nlinarith
  have hlow : ∀ k, fstar ≤ f (x k) := fun k => hfstar _ (interior_subset (hlevel (hmono k)))
  have hsum : ∀ N, ∑ i ∈ Finset.range N, ‖x i - x (i + 1)‖ ^ 3 ≤ 12 / L₀ * (f x₀ - f (x N)) := by
    intro N
    induction N with
    | zero => simp [hrun.init]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hd := hdec N
      have hstep : ‖x N - x (N + 1)‖ ^ 3 ≤ 12 / L₀ * (f (x N) - f (x (N + 1))) := by
        calc ‖x N - x (N + 1)‖ ^ 3 = 12 / L₀ * (L₀ / 12 * ‖x N - x (N + 1)‖ ^ 3) := by
              field_simp
          _ ≤ 12 / L₀ * (f (x N) - f (x (N + 1))) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have : 12 / L₀ * (f x₀ - f (x N)) + 12 / L₀ * (f (x N) - f (x (N + 1))) =
          12 / L₀ * (f x₀ - f (x (N + 1))) := by ring
      linarith
  have hbound : ∀ N, ∑ i ∈ Finset.range N, ‖x i - x (i + 1)‖ ^ 3 ≤ 12 / L₀ * (f x₀ - fstar) := by
    intro N
    refine (hsum N).trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hlow N]) (by positivity)
  have hnn : ∀ i, 0 ≤ ‖x i - x (i + 1)‖ ^ 3 := fun i => by positivity
  exact ⟨summable_of_sum_range_le hnn hbound, Real.tsum_le_of_sum_range_le hnn hbound⟩


theorem aux_rmt_mu_compare {n : ℕ} (L M : ℝ) (hL : 0 < L) (hM0 : 0 < M) (hM : M ≤ 2 * L)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) :
    muMeasure L L g H y ≤ 4 / 3 * muMeasure L M g H y := by
  unfold muMeasure
  set a := ‖g y‖ with ha
  set l := CubicNewton.Shared.lamMin (H y) with hl
  have ha0 : 0 ≤ a := norm_nonneg _
  have hs0 : 0 ≤ Real.sqrt (2 / (L + M) * a) := Real.sqrt_nonneg _
  apply max_le
  · -- sqrt term
    have h1 : Real.sqrt (2 / (L + L) * a) ≤ Real.sqrt (16 / 9 * (2 / (L + M) * a)) := by
      apply Real.sqrt_le_sqrt
      have hLM : 0 < L + M := by linarith
      have : 2 / (L + L) ≤ 16 / 9 * (2 / (L + M)) := by
        rw [show 16 / 9 * (2 / (L + M)) = 32 / (9 * (L + M)) by field_simp; ring]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      nlinarith
    have h2 : Real.sqrt (16 / 9 * (2 / (L + M) * a)) ≤ 4 / 3 * Real.sqrt (2 / (L + M) * a) := by
      rw [Real.sqrt_mul (by norm_num)]
      gcongr
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · by_cases hl0 : 0 ≤ l
    · have : -(2 / (2 * L + L)) * l ≤ 0 := by
        have : 0 < 2 / (2 * L + L) := by positivity
        nlinarith
      have : 0 ≤ 4 / 3 * max (Real.sqrt (2 / (L + M) * a)) (-(2 / (2 * L + M)) * l) := by
        have := le_max_left (Real.sqrt (2 / (L + M) * a)) (-(2 / (2 * L + M)) * l)
        nlinarith
      linarith
    · push Not at hl0
      have hc : 2 / (2 * L + L) ≤ 4 / 3 * (2 / (2 * L + M)) := by
        rw [show 4 / 3 * (2 / (2 * L + M)) = 8 / (3 * (2 * L + M)) by field_simp; ring]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have : -(2 / (2 * L + L)) * l ≤ 4 / 3 * (-(2 / (2 * L + M)) * l) := by nlinarith
      calc _ ≤ _ := this
        _ ≤ _ := by gcongr; exact le_max_right _ _

theorem aux_rmt_mu_nonneg {n : ℕ} (L M : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) : 0 ≤ muMeasure L M g H y := by
  unfold muMeasure
  exact le_trans (Real.sqrt_nonneg _) (le_max_left _ _)

end CubicNewton.Nonconvex

open scoped RealInnerProductSpace
open CubicNewton.Nonconvex

theorem solution {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (L₀ : ℝ) (hL₀ : 0 < L₀) (hL₀L : L₀ ≤ L)
    (fstar : ℝ) (hfstar : ∀ y ∈ F, fstar ≤ f y)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ) (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M) :
    Filter.Tendsto (fun i => muMeasure L L g H (x i)) Filter.atTop (nhds 0) := by
  -- all iterates stay in the level set
  have hdec : ∀ k, f (x (k + 1)) ≤ f (x k) := by
    intro k
    have h1 := hrun.accept k
    have h2 := aux_rmt_rsc_model_decrease g H (M k) (x k) (x (k + 1)) (hrun.step k)
    have h3 := (hrun.param_mem k).1
    have h4 : 0 ≤ ‖x (k + 1) - x k‖ ^ 3 := by positivity
    have h5 : 0 ≤ M k / 12 * ‖x (k + 1) - x k‖ ^ 3 := by
      have : 0 < M k := by linarith
      positivity
    linarith
  have hmono : ∀ k, f (x k) ≤ f x₀ := by
    intro k
    induction k with
    | zero => rw [hrun.init]
    | succ k ih => exact (hdec k).trans ih
  have hmem : ∀ k, x k ∈ F := fun k => interior_subset (hlevel (hmono k))
  -- steps tend to zero
  have hsum := (aux_rmt_sum_cubes F f g H L hF_closed hF_convex hf hg hL hLip x₀ hx₀ hlevel L₀ hL₀
    hL₀L fstar hfstar x M hrun).1
  have hcube : Filter.Tendsto (fun i => ‖x i - x (i + 1)‖ ^ 3) Filter.atTop (nhds 0) :=
    hsum.tendsto_atTop_zero
  have hstep : Filter.Tendsto (fun i => ‖x i - x (i + 1)‖) Filter.atTop (nhds 0) := by
    have h := hcube.rpow_const (p := (3 : ℝ)⁻¹) (Or.inr (by norm_num))
    rw [Real.zero_rpow (by norm_num)] at h
    refine h.congr (fun i => ?_)
    exact Real.pow_rpow_inv_natCast (norm_nonneg _) (by norm_num)
  -- mu bound
  have hbound : ∀ i, muMeasure L L g H (x (i + 1)) ≤ 4 / 3 * ‖x i - x (i + 1)‖ := by
    intro i
    have hM0 : 0 < M i := lt_of_lt_of_le hL₀ (hrun.param_mem i).1
    have h1 := aux_rmt_mu_step_le F f g H L hF_closed hF_convex ⟨x₀, hx₀⟩ hf hg hL hLip (M i) hM0
      (x i) (x (i + 1)) (hmem i) (hmem (i + 1)) (hrun.step i)
    have h2 := aux_rmt_mu_compare L (M i) hL hM0 (hrun.param_mem i).2 g H (x (i + 1))
    linarith
  have hlim : Filter.Tendsto (fun i => muMeasure L L g H (x (i + 1))) Filter.atTop (nhds 0) := by
    have hup : Filter.Tendsto (fun i => 4 / 3 * ‖x i - x (i + 1)‖) Filter.atTop (nhds 0) := by
      simpa using hstep.const_mul (4 / 3 : ℝ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun i => aux_rmt_mu_nonneg L L g H _) hbound
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp hlim
