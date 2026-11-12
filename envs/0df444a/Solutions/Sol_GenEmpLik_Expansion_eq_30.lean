-- Prove2me | solution 1 for GenEmpLik.Expansion.eq_30
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T03:52:57.566864+00:00
-- url     : https://prove2.me/submissions/dac114b8-bebb-40f1-af55-833356e8317b

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_AssumptionA
import Definitions.Def_GenEmpLik_Expansion_huber

open Filter Topology

private lemma subgradient_of_phiDiv {f : ℝ → EReal}
    (hphi : PhiDivRobust.Counterpart.IsPhiDivergenceFunction f)
    {x₀ x d : ℝ} (hx₀ : 0 < x₀) (hx : 0 < x)
    (hd : HasDerivAt (fun u => (f u).toReal) d x₀) :
    (f x₀).toReal + d * (x - x₀) ≤ (f x).toReal := by
  set g : ℝ → ℝ := fun u => (f u).toReal
  have hg_coe : ∀ u : ℝ, 0 < u → (g u : EReal) = f u := fun u hu =>
    EReal.coe_toReal (hphi.ne_top_of_pos u hu) (hphi.ne_bot u)
  have hconv : ∀ θ : ℝ, 0 < θ → θ < 1 →
      (g (x₀ + θ * (x - x₀)) - g x₀) / θ ≤ g x - g x₀ := by
    intro θ hθ0 hθ1
    have hy_pos : 0 < θ * x + (1 - θ) * x₀ := by nlinarith
    have h1 : f (θ * x + (1 - θ) * x₀) ≤
        (θ : EReal) * f x + ((1 - θ : ℝ) : EReal) * f x₀ :=
      hphi.convex x x₀ θ (le_of_lt hx) (le_of_lt hx₀) (le_of_lt hθ0) (le_of_lt hθ1)
    rw [← hg_coe x hx, ← hg_coe x₀ hx₀, ← hg_coe _ hy_pos,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    have heq : θ * x + (1 - θ) * x₀ = x₀ + θ * (x - x₀) := by ring
    rw [heq] at h1
    rw [div_le_iff₀ hθ0]
    linarith
  have hcomp : HasDerivAt (fun θ : ℝ => g (x₀ + θ * (x - x₀))) (d * (x - x₀)) 0 := by
    have hinner : HasDerivAt (fun θ : ℝ => x₀ + θ * (x - x₀)) (x - x₀) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (x - x₀)).const_add x₀
    have hd' : HasDerivAt g d (x₀ + (0 : ℝ) * (x - x₀)) := by
      have hx₀_eq : x₀ + (0 : ℝ) * (x - x₀) = x₀ := by ring
      rwa [hx₀_eq]
    have hc := hd'.comp (0 : ℝ) hinner
    simpa [Function.comp_def, mul_comm] using hc
  have hseq_tendsto : Tendsto (fun k : ℕ => ((k : ℝ) + 2)⁻¹) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have h1 : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      exact tendsto_inv_atTop_zero.comp h1
    · exact Set.mem_compl_singleton_iff.mpr (ne_of_gt (inv_pos.mpr (by positivity)))
  have hlim : Tendsto (fun k : ℕ =>
      (g (x₀ + ((k : ℝ) + 2)⁻¹ * (x - x₀)) - g x₀) / ((k : ℝ) + 2)⁻¹)
      atTop (𝓝 (d * (x - x₀))) := by
    have hslope := hcomp.tendsto_slope_zero.comp hseq_tendsto
    refine hslope.congr fun k => ?_
    dsimp [Function.comp_def]
    change (((k : ℝ) + 2)⁻¹)⁻¹ * (g (x₀ + (0 + ((k : ℝ) + 2)⁻¹) * (x - x₀)) -
      g (x₀ + 0 * (x - x₀))) = (g (x₀ + ((k : ℝ) + 2)⁻¹ * (x - x₀)) - g x₀) / ((k : ℝ) + 2)⁻¹
    rw [zero_add, zero_mul, add_zero, div_eq_inv_mul]
  have hle : d * (x - x₀) ≤ g x - g x₀ := by
    refine le_of_tendsto hlim (Eventually.of_forall fun k => ?_)
    have hk_pos : (0 : ℝ) < ((k : ℝ) + 2)⁻¹ := by positivity
    have hk_lt : ((k : ℝ) + 2)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
    exact hconv _ hk_pos hk_lt
  linarith

private lemma abs_le_of_deriv_abs_le {F F' : ℝ → ℝ} {δ B : ℝ} (hF0 : F 0 = 0)
    (hder : ∀ s : ℝ, |s| ≤ δ → HasDerivAt F (F' s) s) {t : ℝ} (ht : |t| ≤ δ)
    (hF'_le : ∀ ξ : ℝ, |ξ| ≤ |t| → |F' ξ| ≤ B) :
    |F t| ≤ B * |t| := by
  rcases lt_trichotomy t 0 with hlt | rfl | hgt
  · have hsub : ∀ u ∈ Set.Icc t 0, |u| ≤ δ := by
      intro u hu
      rw [abs_le] at ht ⊢
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hcont : ContinuousOn F (Set.Icc t 0) :=
      fun u hu => (hder u (hsub u hu)).continuousAt.continuousWithinAt
    rcases exists_hasDerivAt_eq_slope F F' hlt hcont
      (fun u hu => hder u (hsub u ⟨le_of_lt hu.1, le_of_lt hu.2⟩)) with ⟨ξ, hξ, hξ_eq⟩
    have hξ_abs : |ξ| ≤ |t| := by
      rw [abs_of_neg hlt, abs_of_neg hξ.2]
      linarith [hξ.1]
    rw [hF0, zero_sub, zero_sub, neg_div_neg_eq] at hξ_eq
    have heq : F t = F' ξ * t := (eq_div_iff (ne_of_lt hlt)).mp hξ_eq |>.symm
    rw [heq, abs_mul]
    exact mul_le_mul_of_nonneg_right (hF'_le ξ hξ_abs) (abs_nonneg t)
  · rw [hF0, abs_zero, mul_zero]
  · have hsub : ∀ u ∈ Set.Icc 0 t, |u| ≤ δ := by
      intro u hu
      rw [abs_le] at ht ⊢
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hcont : ContinuousOn F (Set.Icc 0 t) :=
      fun u hu => (hder u (hsub u hu)).continuousAt.continuousWithinAt
    rcases exists_hasDerivAt_eq_slope F F' hgt hcont
      (fun u hu => hder u (hsub u ⟨le_of_lt hu.1, le_of_lt hu.2⟩)) with ⟨ξ, hξ, hξ_eq⟩
    have hξ_abs : |ξ| ≤ |t| := by
      rw [abs_of_pos hgt, abs_of_pos hξ.1]
      linarith [hξ.2]
    rw [hF0, sub_zero, sub_zero] at hξ_eq
    have heq : F t = F' ξ * t := (eq_div_iff (ne_of_gt hgt)).mp hξ_eq |>.symm
    rw [heq, abs_mul]
    exact mul_le_mul_of_nonneg_right (hF'_le ξ hξ_abs) (abs_nonneg t)

private lemma continuous_huber (ε : ℝ) : Continuous (GenEmpLik.Expansion.huber ε) := by
  unfold GenEmpLik.Expansion.huber
  refine continuous_if_le continuous_abs continuous_const
    ((continuous_pow 2).div_const 2).continuousOn
    ((continuous_const.mul continuous_abs).sub continuous_const).continuousOn ?_
  intro x hx
  have hx' : |x| = ε := hx
  rw [← sq_abs, hx']
  ring

open GenEmpLik.Expansion in
theorem solution (f : ℝ → EReal) (hA : AssumptionA f) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ c →
      (∀ t : ℝ, -1 ≤ t → ((2 * (1 - C * ε) * huber ε t : ℝ) : EReal) ≤ f (t + 1)) ∧
      (∀ t : ℝ, |t| ≤ ε → f (t + 1) ≤ (((1 + C * ε) * t ^ 2 : ℝ) : EReal)) := by
  rcases hA with ⟨hphi, _hlsc, a, b, ha0, ha1, hb1, hdiff0, hdiff1, hdiff2, hd1, hd2⟩
  set g : ℝ → ℝ := fun t => (f t).toReal
  have hg_coe : ∀ u : ℝ, 0 < u → (g u : EReal) = f u := fun u hu =>
    EReal.coe_toReal (hphi.ne_top_of_pos u hu) (hphi.ne_bot u)
  have hg1 : g 1 = 0 := by simp [g, hphi.map_one]
  have h1_mem : (1 : ℝ) ∈ Set.Ioo a b := ⟨ha1, hb1⟩
  have hd2_at : HasDerivAt (deriv (deriv g)) (deriv (deriv (deriv g)) 1) 1 :=
    (hdiff2.differentiableAt (isOpen_Ioo.mem_nhds h1_mem)).hasDerivAt
  let M : ℝ := deriv (deriv (deriv g)) 1
  have hslope_lim := Metric.tendsto_nhdsWithin_nhds.mp hd2_at.tendsto_slope_zero 1 one_pos
  rcases hslope_lim with ⟨δ₁, hδ₁_pos, hδ₁⟩
  let K : ℝ := |M| + 1
  have hK_pos : 0 < K := by positivity
  let δ : ℝ := min (δ₁ / 2) (min ((1 - a) / 2) ((b - 1) / 2))
  have hδ_pos : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδ_mem : ∀ s : ℝ, |s| ≤ δ → 1 + s ∈ Set.Ioo a b := by
    intro s hs
    have hs_le : |s| ≤ min ((1 - a) / 2) ((b - 1) / 2) := le_trans hs (min_le_right _ _)
    have hs1 := abs_le.mp (le_trans hs_le (min_le_left _ _))
    have hs2 := abs_le.mp (le_trans hs_le (min_le_right _ _))
    exact ⟨by linarith, by linarith⟩
  have hg2_bound : ∀ s : ℝ, |s| ≤ δ → |deriv (deriv g) (1 + s) - 2| ≤ K * |s| := by
    intro s hs
    by_cases hs0 : s = 0
    · subst hs0
      rw [add_zero, hd2, sub_self, abs_zero, mul_zero]
    · have hs_lt : dist s 0 < δ₁ := by
        rw [Real.dist_eq, sub_zero]
        have : |s| ≤ δ₁ / 2 := le_trans hs (min_le_left _ _)
        linarith
      have hdist := hδ₁ (Set.mem_compl_singleton_iff.mpr hs0) hs_lt
      rw [Real.dist_eq, hd2, smul_eq_mul] at hdist
      have hmul : |s| * |s⁻¹ * (deriv (deriv g) (1 + s) - 2) - M| ≤ |s| * 1 :=
        mul_le_mul_of_nonneg_left (le_of_lt hdist) (abs_nonneg s)
      have heq : s * (s⁻¹ * (deriv (deriv g) (1 + s) - 2) - M) =
          (deriv (deriv g) (1 + s) - 2) - s * M := by field_simp [hs0]
      rw [← abs_mul, heq] at hmul
      have htri := abs_sub_abs_le_abs_sub (deriv (deriv g) (1 + s) - 2) (s * M)
      rw [abs_mul] at htri
      have : |deriv (deriv g) (1 + s) - 2| ≤ |s| * |M| + |s| * 1 := by linarith
      dsimp [K]
      linarith
  have hg1_hasDeriv : ∀ s : ℝ, |s| ≤ δ →
      HasDerivAt (fun u => deriv g (1 + u) - 2 * u) (deriv (deriv g) (1 + s) - 2) s := by
    intro s hs
    have hd_g1 : HasDerivAt (deriv g) (deriv (deriv g) (1 + s)) (1 + s) :=
      (hdiff1.differentiableAt (isOpen_Ioo.mem_nhds (hδ_mem s hs))).hasDerivAt
    have hinner : HasDerivAt (fun u : ℝ => 1 + u) 1 s := by
      simpa using (hasDerivAt_id s).const_add 1
    have h1 : HasDerivAt (fun u : ℝ => deriv g (1 + u)) (deriv (deriv g) (1 + s)) s := by
      simpa [Function.comp_def] using hd_g1.comp s hinner
    have h2 : HasDerivAt (fun u : ℝ => 2 * u) 2 s := by
      simpa using (hasDerivAt_id s).const_mul 2
    exact h1.sub h2
  have hg0_hasDeriv : ∀ s : ℝ, |s| ≤ δ →
      HasDerivAt (fun u => g (1 + u) - u ^ 2) (deriv g (1 + s) - 2 * s) s := by
    intro s hs
    have hd_g0 : HasDerivAt g (deriv g (1 + s)) (1 + s) :=
      (hdiff0.differentiableAt (isOpen_Ioo.mem_nhds (hδ_mem s hs))).hasDerivAt
    have hinner : HasDerivAt (fun u : ℝ => 1 + u) 1 s := by
      simpa using (hasDerivAt_id s).const_add 1
    have h1 : HasDerivAt (fun u : ℝ => g (1 + u)) (deriv g (1 + s)) s := by
      simpa [Function.comp_def] using hd_g0.comp s hinner
    have h2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * s) s := by
      simpa using hasDerivAt_pow 2 s
    exact h1.sub h2
  have hg1_bound : ∀ t : ℝ, |t| ≤ δ → |deriv g (1 + t) - 2 * t| ≤ K * t ^ 2 := by
    intro t ht
    have h0 : deriv g (1 + 0) - 2 * (0 : ℝ) = 0 := by rw [add_zero, hd1, mul_zero, sub_self]
    have hb := abs_le_of_deriv_abs_le h0 hg1_hasDeriv ht fun ξ hξ =>
      le_trans (hg2_bound ξ (le_trans hξ ht)) (mul_le_mul_of_nonneg_left hξ (le_of_lt hK_pos))
    have heq : K * |t| * |t| = K * t ^ 2 := by
      calc K * |t| * |t| = K * |t| ^ 2 := by ring
        _ = K * t ^ 2 := by rw [sq_abs]
    rwa [heq] at hb
  have hg0_bound : ∀ t : ℝ, |t| ≤ δ → |g (1 + t) - t ^ 2| ≤ K * |t| ^ 3 := by
    intro t ht
    have h0 : g (1 + 0) - (0 : ℝ) ^ 2 = 0 := by rw [add_zero, hg1]; norm_num
    have hb := abs_le_of_deriv_abs_le h0 hg0_hasDeriv ht fun ξ hξ => by
      calc |deriv g (1 + ξ) - 2 * ξ|
          ≤ K * ξ ^ 2 := hg1_bound ξ (le_trans hξ ht)
        _ = K * |ξ| ^ 2 := by rw [sq_abs]
        _ ≤ K * |t| ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg ξ) hξ 2)
            (le_of_lt hK_pos)
    have heq : K * |t| ^ 2 * |t| = K * |t| ^ 3 := by ring
    rwa [heq] at hb
  let c : ℝ := min δ (1 / (2 * K))
  have hc_pos : 0 < c := lt_min hδ_pos (by positivity)
  refine ⟨c, K, hc_pos, hK_pos, ?_⟩
  intro ε hε_pos hε_le
  have hε_δ : ε ≤ δ := le_trans hε_le (min_le_left _ _)
  have hε_K : K * ε ≤ 1 / 2 := by
    have h1 : ε ≤ 1 / (2 * K) := le_trans hε_le (min_le_right _ _)
    have h2 : ε * (2 * K) ≤ 1 := (le_div_iff₀ (by positivity)).mp h1
    linarith
  have hε_lt_one : ε < 1 := by
    have : δ ≤ (1 - a) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hlow_gt_neg_one : ∀ t : ℝ, -1 < t →
      ((2 * (1 - K * ε) * huber ε t : ℝ) : EReal) ≤ f (t + 1) := by
    intro t ht
    have ht1_pos : 0 < t + 1 := by linarith
    rw [← hg_coe (t + 1) ht1_pos, EReal.coe_le_coe_iff]
    by_cases h_abs : |t| ≤ ε
    · have ht_δ : |t| ≤ δ := le_trans h_abs hε_δ
      have hb := (abs_le.mp (hg0_bound t ht_δ)).1
      have hcube : |t| ^ 3 ≤ ε * t ^ 2 := by
        calc |t| ^ 3 = |t| * |t| ^ 2 := by ring
          _ = |t| * t ^ 2 := by rw [sq_abs]
          _ ≤ ε * t ^ 2 := mul_le_mul_of_nonneg_right h_abs (sq_nonneg t)
      rw [show huber ε t = t ^ 2 / 2 from if_pos h_abs, show t + 1 = 1 + t by ring]
      nlinarith
    · have h_gt : ε < |t| := not_le.mp h_abs
      rw [show huber ε t = ε * |t| - ε ^ 2 / 2 from if_neg h_abs]
      rcases lt_abs.mp h_gt with ht_gt | ht_lt
      · have hε_abs : |ε| ≤ δ := by rwa [abs_of_pos hε_pos]
        have hd_pos : HasDerivAt g (deriv g (1 + ε)) (1 + ε) :=
          (hdiff0.differentiableAt (isOpen_Ioo.mem_nhds (hδ_mem ε hε_abs))).hasDerivAt
        have hsub := subgradient_of_phiDiv hphi (by linarith : 0 < 1 + ε) ht1_pos hd_pos
        have hg_val : (1 - K * ε) * ε ^ 2 ≤ g (1 + ε) := by
          have hb := (abs_le.mp (hg0_bound ε hε_abs)).1
          rw [abs_of_pos hε_pos] at hb
          nlinarith
        have hg_der : 2 * (1 - K * ε) * ε ≤ deriv g (1 + ε) := by
          have hb := (abs_le.mp (hg1_bound ε hε_abs)).1
          nlinarith
        rw [abs_of_pos (lt_trans hε_pos ht_gt)]
        have hmul : 2 * (1 - K * ε) * ε * (t - ε) ≤ deriv g (1 + ε) * ((t + 1) - (1 + ε)) := by
          rw [show (t + 1) - (1 + ε) = t - ε by ring]
          exact mul_le_mul_of_nonneg_right hg_der (by linarith)
        change g (1 + ε) + deriv g (1 + ε) * ((t + 1) - (1 + ε)) ≤ g (t + 1) at hsub
        nlinarith
      · have hneg_ε_abs : |-ε| ≤ δ := by rwa [abs_neg, abs_of_pos hε_pos]
        have hd_neg : HasDerivAt g (deriv g (1 + (-ε))) (1 + (-ε)) :=
          (hdiff0.differentiableAt (isOpen_Ioo.mem_nhds (hδ_mem (-ε) hneg_ε_abs))).hasDerivAt
        have hsub := subgradient_of_phiDiv hphi (by linarith : 0 < 1 + (-ε)) ht1_pos hd_neg
        have hg_val : (1 - K * ε) * ε ^ 2 ≤ g (1 + (-ε)) := by
          have hb := (abs_le.mp (hg0_bound (-ε) hneg_ε_abs)).1
          rw [abs_neg, abs_of_pos hε_pos] at hb
          nlinarith
        have hg_der : deriv g (1 + (-ε)) ≤ -2 * (1 - K * ε) * ε := by
          have hb := (abs_le.mp (hg1_bound (-ε) hneg_ε_abs)).2
          nlinarith
        rw [abs_of_neg (by linarith)]
        have hmul : -2 * (1 - K * ε) * ε * (t + ε) ≤
            deriv g (1 + (-ε)) * ((t + 1) - (1 + (-ε))) := by
          rw [show (t + 1) - (1 + (-ε)) = t + ε by ring]
          exact mul_le_mul_of_nonpos_right hg_der (by linarith)
        change g (1 + (-ε)) + deriv g (1 + (-ε)) * ((t + 1) - (1 + (-ε))) ≤ g (t + 1) at hsub
        nlinarith
  refine ⟨?_, ?_⟩
  · intro t ht
    rcases lt_or_eq_of_le ht with hgt | rfl
    · exact hlow_gt_neg_one t hgt
    · rw [neg_add_cancel]
      by_cases hf0_top : f 0 = ⊤
      · rw [hf0_top]
        exact le_top
      · let v : ℝ := (f 0).toReal
        have hf0_coe : (v : EReal) = f 0 := EReal.coe_toReal hf0_top (hphi.ne_bot 0)
        rw [← hf0_coe, EReal.coe_le_coe_iff]
        have hseq_ineq : ∀ k : ℕ,
            2 * (1 - K * ε) * huber ε (-1 + ((k : ℝ) + 2)⁻¹) ≤
              (1 - ((k : ℝ) + 2)⁻¹) * v := by
          intro k
          let α : ℝ := ((k : ℝ) + 2)⁻¹
          have hα0 : 0 < α := by positivity
          have hα1 : α < 1 := inv_lt_one_of_one_lt₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
          have hlow_k := hlow_gt_neg_one (-1 + α) (by linarith)
          have hconv_k := hphi.convex 0 1 (1 - α) le_rfl zero_le_one (by linarith) (by linarith)
          rw [show (1 - α) * 0 + (1 - (1 - α)) * 1 = -1 + α + 1 by ring,
            hphi.map_one, ← hf0_coe] at hconv_k
          have hzero : ((1 - (1 - α) : ℝ) : EReal) * (0 : EReal) = 0 := by simp
          rw [hzero, add_zero, ← EReal.coe_mul] at hconv_k
          exact EReal.coe_le_coe_iff.mp (le_trans hlow_k hconv_k)
        have hinv_zero : Tendsto (fun k : ℕ => ((k : ℝ) + 2)⁻¹) atTop (𝓝 (0 : ℝ)) :=
          tendsto_inv_atTop_zero.comp
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        have hlim_lhs : Tendsto (fun k : ℕ =>
            2 * (1 - K * ε) * huber ε (-1 + ((k : ℝ) + 2)⁻¹)) atTop
            (𝓝 (2 * (1 - K * ε) * huber ε (-1))) := by
          have hα_lim : Tendsto (fun k : ℕ => -1 + ((k : ℝ) + 2)⁻¹) atTop (𝓝 (-1)) := by
            simpa using (tendsto_const_nhds (x := (-1 : ℝ))).add hinv_zero
          exact tendsto_const_nhds.mul
            ((continuous_huber ε).continuousAt.tendsto.comp hα_lim)
        have hlim_rhs : Tendsto (fun k : ℕ => (1 - ((k : ℝ) + 2)⁻¹) * v) atTop (𝓝 v) := by
          have h1 : Tendsto (fun k : ℕ => 1 - ((k : ℝ) + 2)⁻¹) atTop (𝓝 (1 - 0)) :=
            (tendsto_const_nhds (x := (1 : ℝ))).sub hinv_zero
          simpa using h1.mul (tendsto_const_nhds (x := v))
        exact le_of_tendsto_of_tendsto hlim_lhs hlim_rhs (Eventually.of_forall hseq_ineq)
  · intro t ht
    have ht_δ : |t| ≤ δ := le_trans ht hε_δ
    have ht1_pos : 0 < t + 1 := by linarith [(hδ_mem t ht_δ).1]
    rw [← hg_coe (t + 1) ht1_pos, EReal.coe_le_coe_iff]
    have hb := (abs_le.mp (hg0_bound t ht_δ)).2
    have hcube : |t| ^ 3 ≤ ε * t ^ 2 := by
      calc |t| ^ 3 = |t| * |t| ^ 2 := by ring
        _ = |t| * t ^ 2 := by rw [sq_abs]
        _ ≤ ε * t ^ 2 := mul_le_mul_of_nonneg_right ht (sq_nonneg t)
    rw [show t + 1 = 1 + t by ring]
    nlinarith
