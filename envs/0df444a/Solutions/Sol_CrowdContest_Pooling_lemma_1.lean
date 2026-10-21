-- Prove2me | solution 1 for CrowdContest.Pooling.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:32:24.694815+00:00
-- url     : https://prove2.me/submissions/87102b18-75d9-4a8f-9d0c-3b87590a33ff

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density
import Definitions.Def_CrowdContest_Pooling_Setting

set_option autoImplicit false
open MeasureTheory CrowdContest.Pooling Asymptotics

theorem cc_hd (C : ℝ → ℝ) (hC : IsCost C) (x : ℝ) (hx : 0 < x) : HasDerivAt C (deriv C x) x :=
  ((hC.2.1.contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt

theorem cc_sm (C : ℝ → ℝ) (hC : IsCost C) : StrictMonoOn C (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) hC.1
  intro x hx
  rw [interior_Ici] at hx
  exact (hC.2.2 x hx).1

theorem cc_sc (C : ℝ → ℝ) (hC : IsCost C) : StrictConvexOn ℝ (Set.Ici 0) C := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici 0) hC.1
  intro x hx
  rw [interior_Ici] at hx
  simpa using (hC.2.2 x hx).2

theorem cc_tangent (C : ℝ → ℝ) (hC : IsCost C) (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) :
    C x + deriv C x * (y - x) ≤ C y := by
  have hcv : ConvexOn ℝ (Set.Ici 0) C := (cc_sc C hC).convexOn
  have hxm : x ∈ Set.Ici (0:ℝ) := le_of_lt hx
  rcases lt_trichotomy x y with h | h | h
  · have := hcv.le_slope_of_hasDerivAt hxm hy h (cc_hd C hC x hx)
    rw [slope_def_field] at this
    rw [le_div_iff₀ (by linarith)] at this
    linarith
  · subst h; simp
  · have := hcv.slope_le_of_hasDerivAt hy hxm h (cc_hd C hC x hx)
    rw [slope_def_field] at this
    rw [div_le_iff₀ (by linarith)] at this
    linarith

theorem cc_attain (C₁ C₂ : ℝ → ℝ) (h1 : ContinuousOn C₁ (Set.Ici 0))
    (h2 : ContinuousOn C₂ (Set.Ici 0)) (e : ℝ) (he : 0 ≤ e) :
    ∃ t, t ∈ Set.Icc 0 e ∧ aggCost C₁ C₂ e = C₁ t + C₂ (e - t) ∧
      ∀ u ∈ Set.Icc 0 e, C₁ t + C₂ (e - t) ≤ C₁ u + C₂ (e - u) := by
  have hcont : ContinuousOn (fun u => C₁ u + C₂ (e - u)) (Set.Icc 0 e) := by
    apply ContinuousOn.add (h1.mono (fun u hu => hu.1))
    refine h2.comp (continuousOn_const.sub continuousOn_id) ?_
    intro u hu
    simp only [Set.mem_Ici]
    linarith [hu.2]
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 he) hcont
  refine ⟨t, ht, ?_, fun u hu => hmin hu⟩
  apply IsLeast.csInf_eq
  refine ⟨⟨t, e - t, ht.1, by linarith [ht.2], by ring, rfl⟩, ?_⟩
  rintro c ⟨a, b, ha, hb, hab, rfl⟩
  have hb' : b = e - a := by linarith
  subst hb'
  exact hmin ⟨ha, by linarith⟩

theorem cc_dens_int {φ : ℝ → ℝ} (hφ : IsDensity φ) : Integrable φ := by
  by_contra h
  have := hφ.2.2
  rw [integral_undef h] at this
  norm_num at this

theorem cc_cdf_nonneg {φ : ℝ → ℝ} (hφ : IsDensity φ) (y : ℝ) : 0 ≤ cdf φ y :=
  setIntegral_nonneg measurableSet_Iic (fun t _ => hφ.2.1 t)

theorem cc_cdf_le_one {φ : ℝ → ℝ} (hφ : IsDensity φ) (y : ℝ) : cdf φ y ≤ 1 := by
  unfold cdf
  calc ∫ t in Set.Iic y, φ t ≤ ∫ t, φ t :=
        setIntegral_le_integral (cc_dens_int hφ) (Filter.Eventually.of_forall hφ.2.1)
    _ = 1 := hφ.2.2

theorem cc_cdf_sub {φ : ℝ → ℝ} (hφ : IsDensity φ) (a b : ℝ) :
    cdf φ b - cdf φ a = ∫ x in a..b, φ x :=
  intervalIntegral.integral_Iic_sub_Iic (cc_dens_int hφ).integrableOn (cc_dens_int hφ).integrableOn

theorem cc_cdf_lip {φ : ℝ → ℝ} (hφ : IsDensity φ) (M : ℝ) (hM : ∀ x, φ x ≤ M) (a b : ℝ) :
    |cdf φ b - cdf φ a| ≤ M * |b - a| := by
  rw [cc_cdf_sub hφ a b]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (f := φ) (C := M)
    (fun x _ => by rw [Real.norm_eq_abs, abs_of_nonneg (hφ.2.1 x)]; exact hM x)
  simpa using this

theorem cc_cdf_cont {φ : ℝ → ℝ} (hφ : IsDensity φ) (M : ℝ) (hM : ∀ x, φ x ≤ M) :
    Continuous (cdf φ) := by
  have hM0 : 0 ≤ M := le_trans (hφ.2.1 0) (hM 0)
  have : LipschitzWith M.toNNReal (cdf φ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.coe_toNNReal M hM0, Real.dist_eq, Real.dist_eq]
    exact cc_cdf_lip hφ M hM y x
  exact this.continuous

theorem cc_cdf_ae {φ : ℝ → ℝ} (hφ : IsDensity φ) : ∀ᵐ y, HasDerivAt (cdf φ) (φ y) y := by
  have hloc : LocallyIntegrable φ volume := (cc_dens_int hφ).locallyIntegrable
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hloc] with y hy
  have h1 := (hy 0).const_add (cdf φ 0)
  have e : cdf φ = fun z => cdf φ 0 + ∫ t in (0:ℝ)..z, φ t := by
    funext z; linarith [cc_cdf_sub hφ 0 z]
  rw [e]; exact h1

theorem cc_pow_lip (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (k : ℕ) :
    |a ^ k - b ^ k| ≤ k * |a - b| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : a ^ (k + 1) - b ^ (k + 1) = a ^ k * (a - b) + b * (a ^ k - b ^ k) := by ring
    rw [e]
    have h1 : a ^ k ≤ 1 := pow_le_one₀ ha0 ha1
    have h2 : 0 ≤ a ^ k := pow_nonneg ha0 k
    calc |a ^ k * (a - b) + b * (a ^ k - b ^ k)|
        ≤ |a ^ k * (a - b)| + |b * (a ^ k - b ^ k)| := abs_add_le _ _
      _ = a ^ k * |a - b| + b * |a ^ k - b ^ k| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h2, abs_of_nonneg hb0]
      _ ≤ 1 * |a - b| + 1 * (k * |a - b|) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          · exact mul_le_mul hb1 ih (abs_nonneg _) zero_le_one
      _ = ((k + 1 : ℕ) : ℝ) * |a - b| := by push_cast; ring

theorem cc_winProb_deriv (φ : ℝ → ℝ) (hφ : IsDensity φ) (M : ℝ) (hM : ∀ x, φ x ≤ M)
    (n : ℕ) (hn : 2 ≤ n) (x₀ : ℝ) :
    HasDerivAt (winProb φ n)
      (∫ ξ, ((n : ℝ) - 1) * cdf φ (x₀ + ξ) ^ (n - 2) * φ (x₀ + ξ) * φ ξ) x₀ := by
  have hM0 : 0 ≤ M := le_trans (hφ.2.1 0) (hM 0)
  have hcc := cc_cdf_cont hφ M hM
  have hk : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hk0 : (0:ℝ) ≤ (n : ℝ) - 1 := by rw [← hk]; exact Nat.cast_nonneg _
  have hFm : ∀ x, Measurable (fun ξ => cdf φ (x + ξ) ^ (n - 1) * φ ξ) := fun x =>
    ((hcc.comp (continuous_const.add continuous_id)).pow (n - 1)).measurable.mul hφ.1
  have key := hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume)
    (F := fun x ξ => cdf φ (x + ξ) ^ (n - 1) * φ ξ)
    (F' := fun ξ => ((n : ℝ) - 1) * cdf φ (x₀ + ξ) ^ (n - 2) * φ (x₀ + ξ) * φ ξ)
    (x₀ := x₀) (bound := fun ξ => ((n : ℝ) - 1) * M * φ ξ) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall (fun x => (hFm x).aestronglyMeasurable))
    ?_ ?_ ?_ ?_ ?_
  · exact key.2
  · refine (cc_dens_int hφ).mono' (hFm x₀).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro ξ
    have h0 := cc_cdf_nonneg hφ (x₀ + ξ)
    have h1 := cc_cdf_le_one hφ (x₀ + ξ)
    have h2 : cdf φ (x₀ + ξ) ^ (n - 1) ≤ 1 := pow_le_one₀ h0 h1
    have h3 : 0 ≤ cdf φ (x₀ + ξ) ^ (n - 1) := pow_nonneg h0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h3 (hφ.2.1 ξ))]
    nlinarith [hφ.2.1 ξ]
  · have : Measurable (fun ξ => ((n : ℝ) - 1) * cdf φ (x₀ + ξ) ^ (n - 2) * φ (x₀ + ξ) * φ ξ) := by
      have h1 : Measurable (fun ξ => cdf φ (x₀ + ξ) ^ (n - 2)) :=
        ((hcc.comp (continuous_const.add continuous_id)).pow (n - 2)).measurable
      have h2 : Measurable (fun ξ => φ (x₀ + ξ)) := hφ.1.comp (measurable_id.const_add x₀)
      exact (((h1.const_mul _).mul h2).mul hφ.1)
    exact this.aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun ξ => ?_)
    have hL : LipschitzWith (Real.nnabs (((n : ℝ) - 1) * M * φ ξ))
        (fun x => cdf φ (x + ξ) ^ (n - 1) * φ ξ) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs,
        abs_of_nonneg (mul_nonneg (mul_nonneg hk0 hM0) (hφ.2.1 ξ)), ← sub_mul,
        abs_mul, abs_of_nonneg (hφ.2.1 ξ)]
      have h1 := cc_pow_lip (cdf φ (x + ξ)) (cdf φ (y + ξ)) (cc_cdf_nonneg hφ _)
        (cc_cdf_le_one hφ _) (cc_cdf_nonneg hφ _) (cc_cdf_le_one hφ _) (n - 1)
      have h2 := cc_cdf_lip hφ M hM (y + ξ) (x + ξ)
      rw [hk] at h1
      have h3 : |x + ξ - (y + ξ)| = |x - y| := by ring_nf
      have h4 : |cdf φ (x + ξ) - cdf φ (y + ξ)| ≤ M * |x - y| := by
        rw [abs_sub_comm]; rw [← h3, abs_sub_comm (x + ξ)]; simpa [abs_sub_comm] using h2
      have h5 : |cdf φ (x + ξ) ^ (n - 1) - cdf φ (y + ξ) ^ (n - 1)| ≤
          ((n : ℝ) - 1) * (M * |x - y|) :=
        h1.trans (mul_le_mul_of_nonneg_left h4 hk0)
      have := mul_le_mul_of_nonneg_right h5 (hφ.2.1 ξ)
      nlinarith [this, hφ.2.1 ξ]
    exact hL.lipschitzOnWith
  · exact (cc_dens_int hφ).const_mul _
  · have hae : ∀ᵐ ξ ∂volume, HasDerivAt (cdf φ) (φ (x₀ + ξ)) (x₀ + ξ) :=
      (measurePreserving_add_left volume x₀).quasiMeasurePreserving.ae (cc_cdf_ae hφ)
    filter_upwards [hae] with ξ hξ
    have h1 : HasDerivAt (fun x => cdf φ (x + ξ)) (φ (x₀ + ξ)) x₀ := hξ.comp_add_const x₀ ξ
    have h2 := (h1.pow (n - 1)).mul_const (φ ξ)
    have e2 : n - 1 - 1 = n - 2 := by omega
    rw [e2, hk] at h2
    exact h2
theorem cc_winProb_deriv0 (φ : ℝ → ℝ) (hφ : IsDensity φ) (M : ℝ) (hM : ∀ x, φ x ≤ M)
    (n : ℕ) (hn : 2 ≤ n) : HasDerivAt (winProb φ n) (hFun φ n) 0 := by
  have h0 := cc_winProb_deriv φ hφ M hM n hn 0
  have e : hFun φ n = ∫ ξ, ((n : ℝ) - 1) * cdf φ (0 + ξ) ^ (n - 2) * φ (0 + ξ) * φ ξ := by
    unfold hFun
    congr 1
    funext ξ
    simp only [zero_add]
    ring
  rw [e]; exact h0

theorem cc_sym_le {ψ : ℝ → ℝ} (hψ : IsSymLogConcaveDensity ψ) (x : ℝ) : ψ x ≤ ψ 0 := by
  have h := hψ.2.2.2 x (Set.mem_univ x) (-x) (Set.mem_univ _) (1/2) (1/2) (by norm_num)
    (by norm_num) (by norm_num)
  have e1 : ((1/2 : ℝ) • x + (1/2 : ℝ) • (-x)) = 0 := by simp
  rw [e1, hψ.2.1 x] at h
  have hn : 0 ≤ ψ x := hψ.1.2.1 x
  rw [← Real.rpow_add' hn (by norm_num)] at h
  norm_num at h
  exact h

theorem cc_dens_bdd {ψ : ℝ → ℝ} (hψ : IsSymLogConcaveDensity ψ) : ∃ M, ∀ x, ψ x ≤ M :=
  ⟨ψ 0, cc_sym_le hψ⟩

/-- the first-order condition for a maximiser of `B * W(e - s) - C e` at an interior effort -/
theorem cc_foc_sub {ψ : ℝ → ℝ} (hψ : IsSymLogConcaveDensity ψ) (n : ℕ) (hn : 2 ≤ n)
    (B : ℝ) (C : ℝ → ℝ) (hC : IsCost C) (s : ℝ) (hs : IsSymEqSub ψ n B C s) (hs0 : 0 < s) :
    deriv C s = B * hFun ψ n := by
  have hW := cc_winProb_deriv0 ψ hψ.1 (ψ 0) (cc_sym_le hψ) n hn
  have hW' : HasDerivAt (fun e => winProb ψ n (e - s)) (hFun ψ n) s := by
    have h1 : HasDerivAt (fun e : ℝ => e - s) 1 s := (hasDerivAt_id s).sub_const s
    have h2 : HasDerivAt (winProb ψ n) (hFun ψ n) ((fun e : ℝ => e - s) s) := by
      show HasDerivAt (winProb ψ n) (hFun ψ n) (s - s)
      rw [sub_self]; exact hW
    exact (HasDerivAt.comp (h := fun e : ℝ => e - s) s h2 h1).congr_deriv (mul_one _)
  have hg : HasDerivAt (fun e => B * winProb ψ n (e - s) - C e) (B * hFun ψ n - deriv C s) s :=
    (hW'.const_mul B).sub (cc_hd C hC s hs0)
  have hlm : IsLocalMax (fun e => B * winProb ψ n (e - s) - C e) s := by
    filter_upwards [Ioi_mem_nhds hs0] with e he
    exact hs.2 e (le_of_lt he)
  have := hlm.hasDerivAt_eq_zero hg
  linarith

theorem solution (n : ℕ) (hn : 2 ≤ n) (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ)
    (B : ℝ) (C : ℝ → ℝ) (hC : IsCost C) (s : ℝ) (hs : IsSymEqSub ψ n B C s) (hs0 : 0 < s) :
    deriv C s = B * hFun ψ n ∧
      ∀ e, 0 < e → deriv C e = B * hFun ψ n → e = s := by
  have hfoc := cc_foc_sub hψ n hn B C hC s hs hs0
  refine ⟨hfoc, fun e he hde => ?_⟩
  have hcd : ContDiffOn ℝ 1 (deriv C) (Set.Ioi 0) :=
    hC.2.1.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hmono : StrictMonoOn (deriv C) (Set.Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0) hcd.continuousOn
    intro x hx
    rw [interior_Ioi] at hx
    exact (hC.2.2 x hx).2
  exact hmono.injOn (Set.mem_Ioi.2 he) (Set.mem_Ioi.2 hs0) (by rw [hde, hfoc])
