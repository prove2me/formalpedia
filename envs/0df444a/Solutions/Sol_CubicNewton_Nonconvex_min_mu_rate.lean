-- Prove2me | solution 1 for CubicNewton.Nonconvex.min_mu_rate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:13:10.680274+00:00
-- url     : https://prove2.me/submissions/ff0ae750-70df-441b-89bb-965840592fa5

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun
import Definitions.Def_CubicNewton_Nonconvex_muMeasure

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

section aux_mmr_section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma aux_mmr_normsq (h w : V) (t : ℝ) :
    ‖h + t • w‖ ^ 2 = ‖h‖ ^ 2 + 2 * t * ⟪h, w⟫ + t ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

lemma aux_mmr_quad (A : V →L[ℝ] V) (hA : ∀ v w, ⟪A v, w⟫ = ⟪A w, v⟫) (h w : V) (t : ℝ) :
    ⟪A (h + t • w), h + t • w⟫ = ⟪A h, h⟫ + 2 * t * ⟪A h, w⟫ + t ^ 2 * ⟪A w, w⟫ := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [hA w h]
  ring

lemma aux_mmr_cube (u : V) : ‖u‖ ^ 3 = (‖u‖ ^ 2) ^ (3 / 2 : ℝ) := by
  rw [← Real.rpow_natCast ‖u‖ 2, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast]
  norm_num

lemma aux_mmr_sqrt (r : ℝ) (hr : 0 ≤ r) : (r ^ 2) ^ (1 / 2 : ℝ) = r := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hr]

lemma aux_mmr_poly (a b c : ℝ) : HasDerivAt (fun t : ℝ => a + b * t + c * t ^ 2) b 0 := by
  have := (((hasDerivAt_const (0:ℝ) a).add ((hasDerivAt_id (0:ℝ)).const_mul b)).add
    ((hasDerivAt_pow 2 (0:ℝ)).const_mul c))
  exact this.congr_deriv (by simp)

lemma aux_mmr_nsq (a b c : ℝ) :
    HasDerivAt (fun t : ℝ => a + 2 * t * b + t ^ 2 * c) (2 * b) 0 := by
  have := aux_mmr_poly a (2 * b) c
  convert this using 1
  funext t; ring

lemma aux_mmr_first (g0 : V) (A : V →L[ℝ] V) (hA : ∀ v w, ⟪A v, w⟫ = ⟪A w, v⟫) (M : ℝ) (h : V)
    (hmin : ∀ u, ⟪g0, h⟫ + 1 / 2 * ⟪A h, h⟫ + M / 6 * ‖h‖ ^ 3 ≤
      ⟪g0, u⟫ + 1 / 2 * ⟪A u, u⟫ + M / 6 * ‖u‖ ^ 3) (w : V) :
    ⟪g0, w⟫ + ⟪A h, w⟫ + M / 2 * ‖h‖ * ⟪h, w⟫ = 0 := by
  let ψ : ℝ → ℝ := fun t => ((⟪g0, h⟫ + 1 / 2 * ⟪A h, h⟫) + (⟪g0, w⟫ + ⟪A h, w⟫) * t +
    (1 / 2 * ⟪A w, w⟫) * t ^ 2) +
    M / 6 * ((‖h‖ ^ 2 + 2 * t * ⟪h, w⟫ + t ^ 2 * ‖w‖ ^ 2) ^ (3 / 2 : ℝ))
  have hψ : ∀ t : ℝ, ψ t = ⟪g0, h + t • w⟫ + 1 / 2 * ⟪A (h + t • w), h + t • w⟫ +
      M / 6 * ‖h + t • w‖ ^ 3 := by
    intro t
    rw [aux_mmr_cube (h + t • w), aux_mmr_normsq, aux_mmr_quad A hA, inner_add_right,
      real_inner_smul_right]
    simp only [ψ]
    ring
  have hloc : IsLocalMin ψ 0 := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    show ψ 0 ≤ ψ t
    rw [hψ, hψ, zero_smul, add_zero]
    exact hmin (h + t • w)
  have hRr := (aux_mmr_nsq (‖h‖ ^ 2) ⟪h, w⟫ (‖w‖ ^ 2)).rpow_const (p := (3 / 2 : ℝ))
    (Or.inr (by norm_num))
  have hD := (aux_mmr_poly (⟪g0, h⟫ + 1 / 2 * ⟪A h, h⟫) (⟪g0, w⟫ + ⟪A h, w⟫)
    (1 / 2 * ⟪A w, w⟫)).add (hRr.const_mul (M / 6))
  have h0 := hloc.hasDerivAt_eq_zero hD
  have e : (‖h‖ ^ 2 + 2 * 0 * ⟪h, w⟫ + 0 ^ 2 * ‖w‖ ^ 2) ^ (3 / 2 - 1 : ℝ) = ‖h‖ := by
    norm_num
    exact aux_mmr_sqrt _ (norm_nonneg _)
  rw [e] at h0
  linear_combination h0

lemma aux_mmr_vec (g0 : V) (A : V →L[ℝ] V) (hA : ∀ v w, ⟪A v, w⟫ = ⟪A w, v⟫) (M : ℝ) (h : V)
    (hmin : ∀ u, ⟪g0, h⟫ + 1 / 2 * ⟪A h, h⟫ + M / 6 * ‖h‖ ^ 3 ≤
      ⟪g0, u⟫ + 1 / 2 * ⟪A u, u⟫ + M / 6 * ‖u‖ ^ 3) :
    g0 + A h + (M / 2 * ‖h‖) • h = 0 := by
  have := aux_mmr_first g0 A hA M h hmin (g0 + A h + (M / 2 * ‖h‖) • h)
  rw [← real_inner_smul_left, ← inner_add_left, ← inner_add_left] at this
  exact inner_self_eq_zero.mp this

lemma aux_mmr_second (g0 : V) (A : V →L[ℝ] V) (hA : ∀ v w, ⟪A v, w⟫ = ⟪A w, v⟫) (M : ℝ)
    (h : V)
    (hmin : ∀ u, ⟪g0, h⟫ + 1 / 2 * ⟪A h, h⟫ + M / 6 * ‖h‖ ^ 3 ≤
      ⟪g0, u⟫ + 1 / 2 * ⟪A u, u⟫ + M / 6 * ‖u‖ ^ 3) (v : V) :
    0 ≤ ⟪A v, v⟫ + M / 2 * ‖h‖ * ‖v‖ ^ 2 := by
  have hfo := aux_mmr_first g0 A hA M h hmin
  by_cases hh : h = 0
  · subst hh
    have hg0 : ∀ w, ⟪g0, w⟫ = 0 := by
      intro w; have := hfo w; simpa using this
    have hpos : ∀ t : ℝ, t ∈ Set.Ioi (0:ℝ) → -(M / 3 * ‖v‖ ^ 3) * t ≤ ⟪A v, v⟫ := by
      intro t ht
      have ht' : 0 < t := ht
      have h1 := hmin (t • v)
      simp only [inner_zero_right, map_zero, norm_zero, mul_zero,
        add_zero] at h1
      rw [hg0, map_smul, real_inner_smul_left, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht'] at h1
      have h2 : 0 ≤ t ^ 2 * (⟪A v, v⟫ + M / 3 * ‖v‖ ^ 3 * t) := by nlinarith
      have h3 := (mul_nonneg_iff_of_pos_left (by positivity : (0:ℝ) < t ^ 2)).mp h2
      linarith
    have hlim : Filter.Tendsto (fun t : ℝ => -(M / 3 * ‖v‖ ^ 3) * t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have : Filter.Tendsto (fun t : ℝ => -(M / 3 * ‖v‖ ^ 3) * t) (nhds 0)
          (nhds (-(M / 3 * ‖v‖ ^ 3) * 0)) :=
        ((continuous_const.mul continuous_id).tendsto (0:ℝ))
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := le_of_tendsto hlim (eventually_nhdsWithin_of_forall hpos)
    simpa using this
  · have key : ∀ w, ⟪h, w⟫ ≠ 0 → 0 ≤ ⟪A w, w⟫ + M / 2 * ‖h‖ * ‖w‖ ^ 2 := by
      intro w hb
      have hw : w ≠ 0 := by rintro rfl; simp at hb
      have hN : 0 < ‖w‖ ^ 2 := by have := norm_pos_iff.mpr hw; positivity
      set τ := -2 * ⟪h, w⟫ / ‖w‖ ^ 2 with hτdef
      have hτ : τ * ‖w‖ ^ 2 = -2 * ⟪h, w⟫ := by rw [hτdef]; field_simp
      have hτ0 : τ ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hτ; apply hb; linarith
      have hnsq : ‖h + τ • w‖ ^ 2 = ‖h‖ ^ 2 := by
        rw [aux_mmr_normsq]; linear_combination τ * hτ
      have hn : ‖h + τ • w‖ = ‖h‖ := by
        have := congrArg Real.sqrt hnsq
        rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
      have h1 := hmin (h + τ • w)
      rw [hn, aux_mmr_quad A hA, inner_add_right, real_inner_smul_right] at h1
      have hfow := hfo w
      have e : τ ^ 2 * (⟪A w, w⟫ + M / 2 * ‖h‖ * ‖w‖ ^ 2) =
          2 * ((⟪g0, h⟫ + τ * ⟪g0, w⟫ + 1 / 2 * (⟪A h, h⟫ + 2 * τ * ⟪A h, w⟫ +
            τ ^ 2 * ⟪A w, w⟫) + M / 6 * ‖h‖ ^ 3) -
            (⟪g0, h⟫ + 1 / 2 * ⟪A h, h⟫ + M / 6 * ‖h‖ ^ 3)) := by
        linear_combination (-2 * τ) * hfow + (τ * (M / 2 * ‖h‖)) * hτ
      have h2 : 0 ≤ τ ^ 2 * (⟪A w, w⟫ + M / 2 * ‖h‖ * ‖w‖ ^ 2) := by rw [e]; linarith
      exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h2
    by_cases hb : ⟪h, v⟫ = 0
    · have hcont : Continuous (fun ε : ℝ =>
          ⟪A (v + ε • h), v + ε • h⟫ + M / 2 * ‖h‖ * ‖v + ε • h‖ ^ 2) := by
        fun_prop
      have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
      simp only [zero_smul, add_zero] at hlim
      refine ge_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      apply key
      rw [inner_add_right, real_inner_smul_right, hb, real_inner_self_eq_norm_sq]
      have : 0 < ‖h‖ ^ 2 := by have := norm_pos_iff.mpr hh; positivity
      simp only [zero_add]
      exact mul_ne_zero hε (ne_of_gt this)
    · exact key v hb

lemma aux_mmr_descent (g0 : V) (A : V →L[ℝ] V) (hA : ∀ v w, ⟪A v, w⟫ = ⟪A w, v⟫) (M : ℝ)
    (h : V)
    (hmin : ∀ u, ⟪g0, h⟫ + 1 / 2 * ⟪A h, h⟫ + M / 6 * ‖h‖ ^ 3 ≤
      ⟪g0, u⟫ + 1 / 2 * ⟪A u, u⟫ + M / 6 * ‖u‖ ^ 3) :
    ⟪g0, h⟫ + 1 / 2 * ⟪A h, h⟫ + M / 6 * ‖h‖ ^ 3 ≤ -(M / 12) * ‖h‖ ^ 3 := by
  have h1 := aux_mmr_first g0 A hA M h hmin h
  have h2 := aux_mmr_second g0 A hA M h hmin h
  rw [real_inner_self_eq_norm_sq] at h1
  linarith

lemma aux_mmr_taylor (F : Set V) (g : V → V) (H : V → V →L[ℝ] V) (L : ℝ)
    (hF_convex : Convex ℝ F) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x y : V) (hx : x ∈ F) (hy : y ∈ F) :
    ‖g y - g x - H x (y - x)‖ ≤ L / 2 * ‖y - x‖ ^ 2 := by
  set h := y - x with hh
  have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • h ∈ F := by
    intro t ht
    have := hF_convex hx hy (sub_nonneg.2 ht.2) ht.1 (by ring : (1 - t) + t = 1)
    convert this using 1
    simp only [hh, smul_sub, sub_smul, one_smul]
    abel
  let ψ : ℝ → V := fun t => g (x + t • h) - g x - t • H x h
  have hψd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (H (x + t • h) h - H x h) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have h2 := (hg _ (hseg t ht)).comp_hasDerivAt t h1
    have h3 := (h2.sub_const (g x)).sub ((hasDerivAt_id t).smul_const (H x h))
    exact h3.congr_deriv (by simp)
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := ψ) (a := 0) (b := 1)
    (f' := fun t => H (x + t • h) h - H x h) (B := fun t => L / 2 * ‖h‖ ^ 2 * t ^ 2)
    (B' := fun t => L * ‖h‖ ^ 2 * t)
    (fun t ht => (hψd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hψd t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [ψ])
    (fun t => ((hasDerivAt_pow 2 t).const_mul (L / 2 * ‖h‖ ^ 2)).congr_deriv
      (by rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring))
    (fun t ht => by
      have ht' := Set.Ico_subset_Icc_self ht
      show ‖H (x + t • h) h - H x h‖ ≤ L * ‖h‖ ^ 2 * t
      rw [← ContinuousLinearMap.sub_apply]
      calc ‖(H (x + t • h) - H x) h‖ ≤ ‖H (x + t • h) - H x‖ * ‖h‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ L * ‖(x + t • h) - x‖ * ‖h‖ := by
            gcongr; exact hLip _ (hseg t ht') _ hx
        _ = L * ‖h‖ ^ 2 * t := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]; ring)
  have := key (Set.right_mem_Icc.2 zero_le_one)
  simp only [ψ, one_smul, one_pow, mul_one] at this
  rwa [hh, add_sub_cancel] at this

end aux_mmr_section

lemma aux_mmr_sym {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (F : Set (EuclideanSpace ℝ (Fin n)))
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior F) (v w : EuclideanSpace ℝ (Fin n)) :
    ⟪H x v, w⟫ = ⟪H x w, v⟫ := by
  have hF : F ∈ nhds x := mem_interior_iff_mem_nhds.mp hx
  let Φ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
  have h1 : ∀ᶠ y in nhds x, HasFDerivAt f (Φ (g y)) y := by
    filter_upwards [hF] with y hy
    have := (hf y hy)
    rw [hasGradientAt_iff_hasFDerivAt] at this
    exact this
  have h2 : HasFDerivAt (fun y => Φ (g y)) (Φ.comp (H x)) x :=
    Φ.hasFDerivAt.comp x (hg x (interior_subset hx))
  have := second_derivative_symmetric_of_eventually h1 h2 v w
  exact this

lemma aux_mmr_result {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (L₀ : ℝ) (hL₀ : 0 < L₀)
    (fstar : ℝ) (hfstar : ∀ y ∈ F, fstar ≤ f y)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ)
    (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ i, 1 ≤ i ∧ i ≤ k ∧
      muMeasure L L g H (x i) ≤ 8 / 3 * (3 * (f x₀ - fstar) / (2 * k * L₀)) ^ (1 / 3 : ℝ) := by
  have hmin : ∀ i u, ⟪g (x i), x (i+1) - x i⟫ +
      1 / 2 * ⟪H (x i) (x (i+1) - x i), x (i+1) - x i⟫ + M i / 6 * ‖x (i+1) - x i‖ ^ 3 ≤
      ⟪g (x i), u⟫ + 1 / 2 * ⟪H (x i) u, u⟫ + M i / 6 * ‖u‖ ^ 3 := by
    intro i u
    have := hrun.step i (x i + u)
    unfold CubicNewton.Shared.cubicModel at this
    rwa [add_sub_cancel_left] at this
  have hmono : ∀ i, f (x (i+1)) ≤ f (x i) := by
    intro i
    have h0 : CubicNewton.Shared.cubicModel g H (M i) (x i) (x i) = 0 := by
      simp [CubicNewton.Shared.cubicModel]
    linarith [hrun.accept i, hrun.step i (x i)]
  have hlev : ∀ i, f (x i) ≤ f x₀ := by
    intro i
    induction i with
    | zero => rw [hrun.init]
    | succ i ih => exact (hmono i).trans ih
  have hint : ∀ i, x i ∈ interior F := fun i => hlevel (hlev i)
  have hmemF : ∀ i, x i ∈ F := fun i => interior_subset (hint i)
  have hsym : ∀ i v w, ⟪H (x i) v, w⟫ = ⟪H (x i) w, v⟫ :=
    fun i => aux_mmr_sym f g H F hf hg (x i) (hint i)
  have hdesc : ∀ i, f (x (i+1)) ≤ f (x i) - L₀ / 12 * ‖x (i+1) - x i‖ ^ 3 := by
    intro i
    have h1 := hrun.accept i
    have h2 : CubicNewton.Shared.cubicModel g H (M i) (x i) (x (i+1)) ≤
        -(M i / 12) * ‖x (i+1) - x i‖ ^ 3 :=
      aux_mmr_descent (g (x i)) (H (x i)) (hsym i) (M i) (x (i+1) - x i) (hmin i)
    have hM := (hrun.param_mem i).1
    have h3 : 0 ≤ ‖x (i+1) - x i‖ ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hM h3]
  have hmu : ∀ i, muMeasure L L g H (x (i+1)) ≤ 4 / 3 * ‖x (i+1) - x i‖ := by
    intro i
    have hvec := aux_mmr_vec (g (x i)) (H (x i)) (hsym i) (M i) (x (i+1) - x i) (hmin i)
    have h2 := aux_mmr_second (g (x i)) (H (x i)) (hsym i) (M i) (x (i+1) - x i) (hmin i)
    have ht := aux_mmr_taylor F g H L hF_convex hg hLip (x i) (x (i+1)) (hmemF i)
      (hmemF (i+1))
    have hL2 := hLip (x (i+1)) (hmemF (i+1)) (x i) (hmemF i)
    set r := ‖x (i+1) - x i‖ with hr
    have hr0 : 0 ≤ r := norm_nonneg _
    have hM1 := (hrun.param_mem i).1
    have hM2 := (hrun.param_mem i).2
    have hMr : M i / 2 * r ≤ L * r := by nlinarith
    have hvec' : g (x i) + H (x i) (x (i+1) - x i) = -((M i / 2 * r) • (x (i+1) - x i)) := by
      rw [eq_neg_iff_add_eq_zero]; exact hvec
    have hgrad : ‖g (x (i+1))‖ ≤ L / 2 * r ^ 2 + M i / 2 * r ^ 2 := by
      have e : g (x (i+1)) = (g (x (i+1)) - g (x i) - H (x i) (x (i+1) - x i)) +
          (g (x i) + H (x i) (x (i+1) - x i)) := by abel
      rw [e]
      calc _ ≤ ‖g (x (i+1)) - g (x i) - H (x i) (x (i+1) - x i)‖ +
            ‖g (x i) + H (x i) (x (i+1) - x i)‖ := norm_add_le _ _
        _ ≤ L / 2 * r ^ 2 + M i / 2 * r ^ 2 := by
          rw [hvec', norm_neg, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (by linarith) hr0)]
          nlinarith
    have hlam : -(2 * L * r) ≤ CubicNewton.Shared.lamMin (H (x (i+1))) := by
      unfold CubicNewton.Shared.lamMin
      rcases isEmpty_or_nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) with hE | hE
      · rw [Real.iInf_of_isEmpty]; nlinarith
      · apply le_ciInf
        intro v
        have hv1 : ‖(v : EuclideanSpace ℝ (Fin n))‖ = 1 := by simpa using v.2
        have h2v := h2 v
        rw [hv1] at h2v
        have hdiff : ⟪H (x (i+1)) v, v⟫ =
            ⟪H (x i) v, v⟫ + ⟪(H (x (i+1)) - H (x i)) v, v⟫ := by
          rw [ContinuousLinearMap.sub_apply, inner_sub_left]; ring
        have hb : |⟪(H (x (i+1)) - H (x i)) v, v⟫| ≤ ‖H (x (i+1)) - H (x i)‖ := by
          calc _ ≤ ‖(H (x (i+1)) - H (x i)) v‖ * ‖(v : EuclideanSpace ℝ (Fin n))‖ :=
                abs_real_inner_le_norm _ _
            _ ≤ ‖H (x (i+1)) - H (x i)‖ * ‖(v : EuclideanSpace ℝ (Fin n))‖ *
                ‖(v : EuclideanSpace ℝ (Fin n))‖ := by
                gcongr; exact ContinuousLinearMap.le_opNorm _ _
            _ = _ := by rw [hv1]; ring
        have hab := neg_abs_le ⟪(H (x (i+1)) - H (x i)) v, v⟫
        rw [hdiff]
        nlinarith
    unfold muMeasure
    apply max_le
    · have hle : 2 / (L + L) * ‖g (x (i+1))‖ ≤ (4 / 3 * r) ^ 2 := by
        rw [show 2 / (L + L) * ‖g (x (i+1))‖ = ‖g (x (i+1))‖ / L by field_simp; ring]
        rw [div_le_iff₀ hL]
        nlinarith
      calc Real.sqrt _ ≤ Real.sqrt ((4 / 3 * r) ^ 2) := Real.sqrt_le_sqrt hle
        _ = 4 / 3 * r := Real.sqrt_sq (by positivity)
    · have hneg : -(2 / (2 * L + L)) ≤ 0 := by
        have : 0 < 2 / (2 * L + L) := by positivity
        linarith
      calc -(2 / (2 * L + L)) * CubicNewton.Shared.lamMin (H (x (i+1)))
          ≤ -(2 / (2 * L + L)) * (-(2 * L * r)) := mul_le_mul_of_nonpos_left hlam hneg
        _ = 4 / 3 * r := by field_simp; ring
  have htel : ∀ m, ∑ i ∈ Finset.range m, L₀ / 12 * ‖x (i+1) - x i‖ ^ 3 ≤ f x₀ - f (x m) := by
    intro m
    induction m with
    | zero => simp [hrun.init]
    | succ m ih => rw [Finset.sum_range_succ]; linarith [hdesc m]
  set Δ := f x₀ - fstar with hΔ
  have hΔ0 : 0 ≤ Δ := by have := hfstar x₀ (interior_subset hx₀); linarith
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have hsum : ∑ i ∈ Finset.range k, ‖x (i+1) - x i‖ ^ 3 ≤
      ∑ i ∈ Finset.range k, 12 * Δ / (k * L₀) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h1 := htel k
    have h2 := hfstar (x k) (hmemF k)
    rw [← Finset.mul_sum] at h1
    rw [show (k:ℝ) * (12 * Δ / (k * L₀)) = 12 * Δ / L₀ by field_simp]
    rw [le_div_iff₀ hL₀]
    linarith
  obtain ⟨i, hi, hile⟩ := Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.mpr (by omega)) hsum
  have hik : i < k := Finset.mem_range.mp hi
  refine ⟨i + 1, by omega, by omega, ?_⟩
  set X := 3 * Δ / (2 * k * L₀) with hX
  have hX0 : 0 ≤ X := by positivity
  set c := X ^ (1 / 3 : ℝ) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg hX0 _
  have hc3 : c ^ 3 = X := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hX0]; norm_num
  have hr3 : ‖x (i+1) - x i‖ ^ 3 ≤ (2 * c) ^ 3 := by
    rw [mul_pow, hc3, hX]
    calc _ ≤ 12 * Δ / (k * L₀) := hile
      _ = _ := by field_simp; ring
  have hr : ‖x (i+1) - x i‖ ≤ 2 * c := le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hr3
  calc muMeasure L L g H (x (i+1)) ≤ 4 / 3 * ‖x (i+1) - x i‖ := hmu i
    _ ≤ 4 / 3 * (2 * c) := by gcongr
    _ = 8 / 3 * c := by ring

end CubicNewton.Nonconvex

open CubicNewton.Nonconvex
open scoped RealInnerProductSpace

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
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ) (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ i, 1 ≤ i ∧ i ≤ k ∧
      muMeasure L L g H (x i) ≤ 8 / 3 * (3 * (f x₀ - fstar) / (2 * k * L₀)) ^ (1 / 3 : ℝ) :=
  aux_mmr_result F f g H L hF_convex hf hg hL hLip x₀ hx₀ hlevel L₀ hL₀ fstar hfstar x M hrun k hk
