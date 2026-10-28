-- Prove2me | solution 1 for ChanceStateCtrl.General.theorem_2_2_e_lipschitz_bounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T07:00:39.830526+00:00
-- url     : https://prove2.me/submissions/fa11cb20-3c6c-4416-b8f4-aed7a5969e38

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_General_Radial
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

namespace S163

open ChanceStateCtrl.General

lemma sqrtCov_inj {m : ℕ} (Sigma : Matrix (Fin m) (Fin m) ℝ) (hS : Sigma.PosDef)
    (x : EuclideanSpace ℝ (Fin m)) (hx : sqrtCov Sigma x = 0) : x = 0 := by
  have h0 : (0 : Matrix (Fin m) (Fin m) ℝ) ≤ Sigma := hS.posSemidef.nonneg
  have hmul : CFC.sqrt Sigma * CFC.sqrt Sigma = Sigma := CFC.sqrt_mul_sqrt_self Sigma h0
  have h2 : Matrix.toEuclideanCLM (𝕜 := ℝ) Sigma x = 0 := by
    rw [← hmul, map_mul]
    change sqrtCov Sigma (sqrtCov Sigma x) = 0
    rw [hx, map_zero]
  by_contra hne
  have hne' : WithLp.ofLp x ≠ 0 := by
    intro h; apply hne; exact (WithLp.ofLp_eq_zero 2).mp h
  have := hS.dotProduct_mulVec_pos hne'
  have h3 : Sigma.mulVec (WithLp.ofLp x) = 0 := by
    rw [← Matrix.ofLp_toEuclideanCLM, h2]; rfl
  rw [h3] at this; simp at this

lemma sqrtCov_lower {m : ℕ} (Sigma : Matrix (Fin m) (Fin m) ℝ) (hS : Sigma.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      c ≤ ‖sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))‖ := by
  rcases (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1).eq_empty_or_nonempty with h | h
  · refine ⟨1, one_pos, fun v => ?_⟩
    obtain ⟨x, hx⟩ := v; rw [h] at hx; exact hx.elim
  obtain ⟨x0, hx0, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin m)) 1).exists_isMinOn h
    ((sqrtCov Sigma).continuous.norm.continuousOn)
  refine ⟨‖sqrtCov Sigma x0‖, ?_, fun v => hmin v.2⟩
  rw [norm_pos_iff]
  intro h0
  have := sqrtCov_inj Sigma hS x0 h0
  rw [this] at hx0; simp at hx0

end S163

namespace S163

lemma fin_pos_lb {ι : Type*} (t : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ t, 0 < f i) :
    ∃ ε > 0, ∀ i ∈ t, ε ≤ f i := by
  rcases t.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · refine ⟨t.inf' h f, (Finset.lt_inf'_iff h).2 hf, fun i hi => Finset.inf'_le f hi⟩

lemma unif_lip {U E : Type*} [PseudoMetricSpace U] [PseudoMetricSpace E] (F : U × E → ℝ)
    (hF : LocallyLipschitz F) (u0 : U) (K : Set E) (hK : IsCompact K) :
    ∃ ε > 0, ∃ L : ℝ, 0 ≤ L ∧ ∀ u ∈ Metric.ball u0 ε, ∀ u' ∈ Metric.ball u0 ε, ∀ z ∈ K,
      |F (u, z) - F (u', z)| ≤ L * dist u u' := by
  have key : ∀ z ∈ K, ∃ r > 0, ∃ L : NNReal, ∀ p ∈ Metric.ball u0 r ×ˢ Metric.ball z r,
      ∀ q ∈ Metric.ball u0 r ×ˢ Metric.ball z r, dist (F p) (F q) ≤ L * dist p q := by
    intro z _
    obtain ⟨L, t, ht, hlip⟩ := hF (u0, z)
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 ht
    refine ⟨r, hr, L, fun p hp q hq => ?_⟩
    rw [← ball_prod_same] at hsub
    exact hlip.dist_le_mul p (hsub hp) q (hsub hq)
  choose r hr L hL using key
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun z hz => Metric.ball z (r z hz))
    (fun z hz => Metric.ball_mem_nhds z (hr z hz))
  obtain ⟨ε, hε, hεle⟩ := fin_pos_lb t (fun x => r x.1 x.2) (fun x _ => hr x.1 x.2)
  refine ⟨ε, hε, ∑ x ∈ t, (L x.1 x.2 : ℝ), Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _),
    fun u hu u' hu' z hz => ?_⟩
  have hz' := ht hz
  simp only [Set.mem_iUnion] at hz'
  obtain ⟨x, hxt, hzx⟩ := hz'
  have hrx := hεle x hxt
  have hu1 : u ∈ Metric.ball u0 (r x.1 x.2) := Metric.ball_subset_ball hrx hu
  have hu2 : u' ∈ Metric.ball u0 (r x.1 x.2) := Metric.ball_subset_ball hrx hu'
  have := hL x.1 x.2 (u, z) ⟨hu1, hzx⟩ (u', z) ⟨hu2, hzx⟩
  rw [Real.dist_eq, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] at this
  refine this.trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
  exact Finset.single_le_sum (f := fun x : K => (L x.1 x.2 : ℝ))
    (fun _ _ => NNReal.coe_nonneg _) hxt

end S163

namespace S163
open ChanceStateCtrl.General

lemma chi_interval {m : ℕ} (R : ℝ) (hR : 0 ≤ R) (a b : ℝ) (hab : a ≤ b) :
    chiLaw m (Set.Icc 0 R ∩ Set.Icc a b) ≤
      ENNReal.ofReal ((|chiConst m| * R ^ (m - 1)) * (b - a)) := by
  have hmeas : MeasurableSet (Set.Icc 0 R ∩ Set.Icc a b) := measurableSet_Icc.inter measurableSet_Icc
  unfold chiLaw
  rw [withDensity_apply _ hmeas]
  calc ∫⁻ t in Set.Icc 0 R ∩ Set.Icc a b, ENNReal.ofReal (chiDensity m t)
      ≤ ∫⁻ _t in Set.Icc 0 R ∩ Set.Icc a b, ENNReal.ofReal (|chiConst m| * R ^ (m - 1)) := by
        apply setLIntegral_mono measurable_const
        intro t ht
        apply ENNReal.ofReal_le_ofReal
        unfold chiDensity
        rw [if_pos ht.1.1]
        have h1 : Real.exp (-t ^ 2 / 2) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg t]
        have h2 : t ^ (m - 1) ≤ R ^ (m - 1) := pow_le_pow_left₀ ht.1.1 ht.1.2 _
        have h3 : 0 ≤ t ^ (m - 1) := pow_nonneg ht.1.1 _
        calc chiConst m * t ^ (m - 1) * Real.exp (-t ^ 2 / 2)
            ≤ |chiConst m| * t ^ (m - 1) * 1 := by
              apply mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) h3) h1
                (Real.exp_pos _).le (mul_nonneg (abs_nonneg _) h3)
          _ ≤ |chiConst m| * R ^ (m - 1) := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = ENNReal.ofReal (|chiConst m| * R ^ (m - 1)) * volume (Set.Icc 0 R ∩ Set.Icc a b) :=
        setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (|chiConst m| * R ^ (m - 1)) * volume (Set.Icc a b) :=
        by gcongr; exact Set.inter_subset_right
    _ = _ := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (pow_nonneg hR _))]

/-- Abstract comparison of measures of down-closed bounded sets. -/
lemma meas_diff (μ : Measure ℝ) (R D : ℝ) (hD : 0 ≤ D)
    (hμ : ∀ a b, a ≤ b → μ (Set.Icc 0 R ∩ Set.Icc a b) ≤ ENNReal.ofReal (D * (b - a)))
    (S T : Set ℝ) (e : ℝ) (he : 0 ≤ e)
    (hS : S ⊆ Set.Icc 0 R) (hT : T ⊆ Set.Icc 0 R) (h0T : 0 ∈ T)
    (hdown : ∀ s ∈ T, ∀ r, 0 ≤ r → r ≤ s → r ∈ T)
    (hshift : ∀ r ∈ S, 0 ≤ r - e → r - e ∈ T) :
    μ S ≤ μ T + ENNReal.ofReal (D * e) := by
  have hbdd : BddAbove T := ⟨R, fun x hx => (hT hx).2⟩
  set x := sSup T
  have hx0 : 0 ≤ x := le_csSup hbdd h0T
  have hsub : S ⊆ T ∪ (Set.Icc 0 R ∩ Set.Icc x (x + e)) := by
    intro r hr
    by_cases hrT : r ∈ T
    · exact Or.inl hrT
    right
    refine ⟨hS hr, ?_, ?_⟩
    · by_contra hlt
      push Not at hlt
      obtain ⟨s, hs, hrs⟩ := exists_lt_of_lt_csSup ⟨0, h0T⟩ hlt
      exact hrT (hdown s hs r (hS hr).1 hrs.le)
    · by_cases hre : 0 ≤ r - e
      · have := le_csSup hbdd (hshift r hr hre); linarith
      · linarith
  calc μ S ≤ μ (T ∪ (Set.Icc 0 R ∩ Set.Icc x (x + e))) := measure_mono hsub
    _ ≤ μ T + μ (Set.Icc 0 R ∩ Set.Icc x (x + e)) := measure_union_le _ _
    _ ≤ μ T + ENNReal.ofReal (D * e) := by
        gcongr
        have := hμ x (x + e) (by linarith)
        simpa using this

lemma toReal_lip (μ : Measure ℝ) (R D : ℝ) (hD : 0 ≤ D)
    (hμ : ∀ a b, a ≤ b → μ (Set.Icc 0 R ∩ Set.Icc a b) ≤ ENNReal.ofReal (D * (b - a)))
    (hR : 0 ≤ R)
    (S T : Set ℝ) (e : ℝ) (he : 0 ≤ e)
    (hS : S ⊆ Set.Icc 0 R) (hT : T ⊆ Set.Icc 0 R) (h0S : 0 ∈ S) (h0T : 0 ∈ T)
    (hdownS : ∀ s ∈ S, ∀ r, 0 ≤ r → r ≤ s → r ∈ S)
    (hdownT : ∀ s ∈ T, ∀ r, 0 ≤ r → r ≤ s → r ∈ T)
    (hST : ∀ r ∈ S, 0 ≤ r - e → r - e ∈ T) (hTS : ∀ r ∈ T, 0 ≤ r - e → r - e ∈ S) :
    |(μ S).toReal - (μ T).toReal| ≤ D * e := by
  have hfin : ∀ A ⊆ Set.Icc 0 R, μ A ≠ ⊤ := by
    intro A hA
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    calc μ A ≤ μ (Set.Icc 0 R ∩ Set.Icc 0 R) := measure_mono (by simpa using hA)
      _ ≤ _ := hμ 0 R hR
  have h1 := meas_diff μ R D hD hμ S T e he hS hT h0T hdownT hST
  have h2 := meas_diff μ R D hD hμ T S e he hT hS h0S hdownS hTS
  have hDe : 0 ≤ D * e := mul_nonneg hD he
  have k1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin T hT, ENNReal.ofReal_ne_top⟩) h1
  have k2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin S hS, ENNReal.ofReal_ne_top⟩) h2
  rw [ENNReal.toReal_add (hfin T hT) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hDe] at k1
  rw [ENNReal.toReal_add (hfin S hS) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hDe] at k2
  rw [abs_sub_le_iff]; constructor <;> linarith

end S163

namespace S163
open ChanceStateCtrl.General

lemma conv_aux {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (z : E) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    f (t • z) ≤ t * f z + (1 - t) * f 0 := by
  have := hf.2 (Set.mem_univ z) (Set.mem_univ 0) h0 (by linarith : 0 ≤ 1 - t) (by ring)
  simpa using this

theorem main {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U]
    [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g)
    (ub : U) (h10 : g ub 0 < 0) (hM : Bornology.IsBounded {z | g ub z ≤ 0}) :
    ∃ K : NNReal, ∃ t ∈ 𝓝 ub, ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      LipschitzOnWith K (fun u => radialProb Sigma g u v) t := by
  obtain ⟨r0, hr0⟩ := (Metric.isBounded_iff_subset_ball (0 : EuclideanSpace ℝ (Fin m))).1 hM
  set R₁ := max r0 1 with hR₁def
  have hR₁ : 0 < R₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMR : ∀ z, g ub z ≤ 0 → ‖z‖ < R₁ := by
    intro z hz
    have := hr0 hz
    rw [Metric.mem_ball, dist_zero_right] at this
    exact lt_of_lt_of_le this (le_max_left _ _)
  obtain ⟨ε₀, hε₀, L, hL0, hL⟩ := unif_lip (Function.uncurry g) hA.locLip ub
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) R₁) (isCompact_closedBall _ _)
  simp only [Function.uncurry_apply_pair] at hL
  -- positive lower bound on the sphere of radius R₁
  obtain ⟨η, hη, hηle⟩ : ∃ η > 0, ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) R₁,
      η ≤ g ub z := by
    rcases (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) R₁).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    have hcont : Continuous (g ub) :=
      hA.locLip.continuous.comp (Continuous.prodMk continuous_const continuous_id)
    obtain ⟨z0, hz0, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin m)) R₁).exists_isMinOn
      h hcont.continuousOn
    refine ⟨g ub z0, ?_, fun z hz => hmin hz⟩
    by_contra hle
    push Not at hle
    have := hMR z0 hle
    rw [mem_sphere_zero_iff_norm] at hz0
    linarith
  set δ₀ := -g ub 0 with hδ₀
  have hδ₀pos : 0 < δ₀ := by linarith
  set ε := min ε₀ (min (δ₀ / (2 * (L + 1))) (η / (2 * (L + 1)))) with hεdef
  have hεpos : 0 < ε := lt_min hε₀ (lt_min (by positivity) (by positivity))
  have hLε : ∀ u ∈ Metric.ball ub ε, L * dist u ub ≤ δ₀ / 2 ∧ L * dist u ub ≤ η / 2 := by
    intro u hu
    rw [Metric.mem_ball] at hu
    have h1 : dist u ub ≤ δ₀ / (2 * (L + 1)) := hu.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    have h2 : dist u ub ≤ η / (2 * (L + 1)) := hu.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hd := dist_nonneg (x := u) (y := ub)
    rw [le_div_iff₀ (by positivity)] at h1 h2
    constructor <;> nlinarith
  have hball : ∀ u ∈ Metric.ball ub ε, u ∈ Metric.ball ub ε₀ :=
    fun u hu => Metric.ball_subset_ball (min_le_left _ _) hu
  have hub : ub ∈ Metric.ball ub ε₀ := Metric.mem_ball_self hε₀
  set δ := δ₀ / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  have hg0 : ∀ u ∈ Metric.ball ub ε, g u 0 ≤ -δ := by
    intro u hu
    have := hL u (hball u hu) ub hub 0 (Metric.mem_closedBall_self hR₁.le)
    have := (hLε u hu).1
    rw [abs_le] at *
    linarith
  have hRb : ∀ u ∈ Metric.ball ub ε, ∀ z, g u z ≤ 0 → ‖z‖ ≤ R₁ := by
    intro u hu z hz
    by_contra hlt
    push Not at hlt
    have hzpos : 0 < ‖z‖ := hR₁.trans hlt
    set t := R₁ / ‖z‖
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 := by rw [div_le_one hzpos]; exact hlt.le
    have hsph : t • z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) R₁ := by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg ht0, div_mul_cancel₀ _ hzpos.ne']
    have h1 := hηle _ hsph
    have h2 := hL u (hball u hu) ub hub (t • z) (Metric.sphere_subset_closedBall hsph)
    have h3 := (hLε u hu).2
    have h4 := conv_aux (g u) (hA.convex_snd u) z t ht0 ht1
    have h5 := hg0 u hu
    rw [abs_le] at h2
    nlinarith
  obtain ⟨c, hc, hcle⟩ := sqrtCov_lower Sigma hA.posDef
  set R' := R₁ / c with hR'def
  have hR' : 0 < R' := by positivity
  set C := R' * L / δ with hCdef
  have hC : 0 ≤ C := by positivity
  set D := |chiConst m| * R' ^ (m - 1) with hDdef
  have hD : 0 ≤ D := by positivity
  refine ⟨(D * C).toNNReal, Metric.ball ub ε, Metric.ball_mem_nhds _ hεpos, fun v => ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu u' hu'
  rw [Real.coe_toNNReal _ (mul_nonneg hD hC)]
  set w := sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))
  have hw := hcle v
  set S : U → Set ℝ := fun u => {r : ℝ | 0 ≤ r ∧ g u (r • w) ≤ 0} with hSdef
  have hrad : ∀ u, radialProb Sigma g u v = (chiLaw m (S u)).toReal := fun u => rfl
  rw [hrad, hrad, Real.dist_eq]
  have hSsub : ∀ u ∈ Metric.ball ub ε, S u ⊆ Set.Icc 0 R' := by
    intro u hu r ⟨hr0, hr⟩
    refine ⟨hr0, ?_⟩
    have := hRb u hu _ hr
    rw [norm_smul, Real.norm_of_nonneg hr0] at this
    rw [hR'def, le_div_iff₀ hc]
    nlinarith
  have h0S : ∀ u ∈ Metric.ball ub ε, (0 : ℝ) ∈ S u := by
    intro u hu
    refine ⟨le_rfl, ?_⟩
    rw [zero_smul]; linarith [hg0 u hu]
  have hdown : ∀ u ∈ Metric.ball ub ε, ∀ s ∈ S u, ∀ r, 0 ≤ r → r ≤ s → r ∈ S u := by
    intro u hu s ⟨hs0, hs⟩ r hr0 hrs
    refine ⟨hr0, ?_⟩
    rcases hs0.eq_or_lt with h | h
    · subst h
      have : r = 0 := le_antisymm hrs hr0
      subst this; rw [zero_smul]; linarith [hg0 u hu]
    have := conv_aux (g u) (hA.convex_snd u) (s • w) (r / s) (by positivity)
      ((div_le_one h).2 hrs)
    rw [smul_smul, div_mul_cancel₀ _ h.ne'] at this
    have h5 := hg0 u hu
    have ht1 : r / s ≤ 1 := (div_le_one h).2 hrs
    have ht0 : 0 ≤ r / s := by positivity
    nlinarith
  have hshift : ∀ u ∈ Metric.ball ub ε, ∀ u' ∈ Metric.ball ub ε, ∀ r ∈ S u,
      0 ≤ r - C * dist u u' → r - C * dist u u' ∈ S u' := by
    intro u hu u' hu' r ⟨hr0, hr⟩ hre
    refine ⟨hre, ?_⟩
    set e := C * dist u u'
    have he : 0 ≤ e := mul_nonneg hC dist_nonneg
    have hrR : r ≤ R' := (hSsub u hu ⟨hr0, hr⟩).2
    rcases hr0.eq_or_lt with h | h
    · have : r - e = 0 := by rw [← h] at hre ⊢; linarith
      rw [this, zero_smul]; linarith [hg0 u' hu']
    set t := (r - e) / r
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 := by rw [div_le_one h]; linarith
    have hconv := conv_aux (g u) (hA.convex_snd u) (r • w) t ht0 ht1
    rw [smul_smul, div_mul_cancel₀ _ h.ne'] at hconv
    have hnorm : ‖(r - e) • w‖ ≤ R₁ := by
      have := hRb u hu _ hr
      rw [norm_smul, Real.norm_of_nonneg hr0] at this
      rw [norm_smul, Real.norm_of_nonneg hre]
      nlinarith [norm_nonneg w]
    have hlip := hL u (hball u hu) u' (hball u' hu') ((r - e) • w)
      (mem_closedBall_zero_iff.2 hnorm)
    rw [abs_le] at hlip
    have h5 := hg0 u hu
    -- (1 - t) * δ = e * δ / r ≥ e * δ / R' = L * dist u u'
    have h1t : 1 - t = e / r := by
      simp only [t]; field_simp; ring
    have hkey : L * dist u u' ≤ (1 - t) * δ := by
      rw [h1t]
      have : e * δ / R' = L * dist u u' := by
        simp only [e, hCdef]; field_simp
      rw [← this, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left (mul_nonneg he hδpos.le) h hrR
    have : t * g u (r • w) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hr
    nlinarith
  have hμ := fun a b (hab : a ≤ b) => chi_interval (m := m) R' hR'.le a b hab
  have := toReal_lip (chiLaw m) R' D hD hμ hR'.le (S u) (S u') (C * dist u u')
    (mul_nonneg hC dist_nonneg) (hSsub u hu) (hSsub u' hu') (h0S u hu) (h0S u' hu')
    (hdown u hu) (hdown u' hu') (hshift u hu u' hu')
    (by rw [dist_comm]; exact hshift u' hu' u hu)
  calc _ ≤ D * (C * dist u u') := this
    _ = D * C * dist u u' := by ring

end S163

theorem solution {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U]
    [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : ChanceStateCtrl.General.Assumption21 P ξ Sigma g)
    (ub : U) (h10 : g ub 0 < 0) (hM : Bornology.IsBounded {z | g ub z ≤ 0}) :
    ∃ K : NNReal, ∃ t ∈ 𝓝 ub, ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      LipschitzOnWith K (fun u => ChanceStateCtrl.General.radialProb Sigma g u v) t :=
  S163.main P ξ Sigma g hA ub h10 hM

