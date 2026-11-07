-- Prove2me | solution 1 for GenEmpLik.Coverage.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:18:22.938685+00:00
-- url     : https://prove2.me/submissions/6ac6f992-91f7-4156-87f9-d5bf7a707ca6

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_AssumptionA
import Definitions.Def_GenEmpLik_Coverage_divergenceBall

open Filter Topology

namespace GEL13
open GenEmpLik.Coverage

lemma ereal_coe_sum {ι : Type*} (s : Finset ι) (r : ι → ℝ) :
    ((∑ i ∈ s, r i : ℝ) : EReal) = ∑ i ∈ s, (r i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

lemma f_nonneg (f : ℝ → EReal) (hA : AssumptionA f) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ f t := by
  obtain ⟨hφ, _, a, b, ha0, ha1, hb1, hcd, hd1, _⟩ := hA
  by_contra hneg0
  have hneg := not_le.mp hneg0
  set g : ℝ → ℝ := fun s => (f s).toReal with hg
  have hft_ne_bot := hφ.ne_bot t
  have hft_ne_top : f t ≠ ⊤ := fun h => by rw [h] at hneg; exact absurd hneg (not_lt.2 le_top)
  set c := (f t).toReal with hc_def
  have hfc : f t = (c : EReal) := (EReal.coe_toReal hft_ne_top hft_ne_bot).symm
  have hc : c < 0 := by rw [hfc] at hneg; exact_mod_cast hneg
  have hdiff : DifferentiableAt ℝ g 1 := by
    have := hcd.differentiableOn (by norm_num)
    exact (this 1 ⟨ha1, hb1⟩).differentiableAt (Ioo_mem_nhds ha1 hb1)
  have hder : HasDerivAt g 0 (1 + 0 * (t - 1)) := by
    have : HasDerivAt g (deriv g 1) 1 := hdiff.hasDerivAt
    rw [hd1] at this
    simpa using this
  have h1 : HasDerivAt (fun θ : ℝ => 1 + θ * (t - 1)) (t - 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (t - 1)).const_add 1
  have hcomp := hder.comp (0:ℝ) h1
  rw [zero_mul, hasDerivAt_iff_tendsto_slope] at hcomp
  have hlim : Tendsto (slope (g ∘ fun θ : ℝ => 1 + θ * (t - 1)) 0) (𝓝[>] 0) (𝓝 0) :=
    hcomp.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
  have hle : ∀ᶠ θ in 𝓝[>] (0:ℝ), slope (g ∘ fun θ : ℝ => 1 + θ * (t - 1)) 0 θ ≤ c := by
    have : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [this] with θ hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hconv := hφ.convex t 1 θ ht zero_le_one hθ0.le hθ1.le
    rw [hφ.map_one, hfc, mul_zero, add_zero] at hconv
    have hs : θ * t + (1 - θ) * 1 = 1 + θ * (t - 1) := by ring
    rw [hs] at hconv
    have hpos : 0 < 1 + θ * (t - 1) := by nlinarith
    have hfs_bot := hφ.ne_bot (1 + θ * (t - 1))
    have hgle : g (1 + θ * (t - 1)) ≤ θ * c := by
      have := EReal.toReal_le_toReal hconv hfs_bot (by
        rw [← EReal.coe_mul]; exact EReal.coe_ne_top _)
      rw [← EReal.coe_mul, EReal.toReal_coe] at this
      exact this
    have hg1 : g (1 + 0 * (t - 1)) = 0 := by simp [hg, hφ.map_one]
    rw [slope_def_field]
    simp only [Function.comp, sub_zero]
    rw [hg1, sub_zero, div_le_iff₀ hθ0]
    linarith
  have := le_of_tendsto hlim hle
  linarith


lemma ball_iff (f : ℝ → EReal) (hA : AssumptionA f) (ρ : ℝ) (n : ℕ) (hn : 0 < n)
    (p : Fin n → ℝ) :
    p ∈ divergenceBall f ρ n ↔ 0 ≤ p ∧ ∑ i, p i = 1 ∧ (∀ i, f (n * p i) ≠ ⊤) ∧
      ∑ i, (f (n * p i)).toReal ≤ ρ := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hdiv : ∀ i, p i / (1 / (n:ℝ)) = n * p i := fun i => by field_simp
  simp only [divergenceBall, PhiDivRobust.Counterpart.probUncertaintySet,
    PhiDivRobust.Counterpart.phiDiv, Set.mem_setOf_eq, hdiv]
  constructor
  · rintro ⟨hp0, hp1, hD⟩
    have hterm : ∀ i, 0 ≤ ((1 / (n:ℝ) : ℝ) : EReal) * f (n * p i) := fun i =>
      EReal.mul_nonneg (by exact_mod_cast (by positivity : (0:ℝ) ≤ 1 / n))
        (f_nonneg f hA _ (mul_nonneg hnR.le (hp0 i)))
    have htop : ∀ i, f (n * p i) ≠ ⊤ := by
      intro j hj
      have h1 := Finset.single_le_sum (fun i _ => hterm i) (Finset.mem_univ j)
      rw [hj, EReal.coe_mul_top_of_pos (by positivity)] at h1
      have := h1.trans hD
      exact EReal.coe_ne_top _ (top_le_iff.mp this)
    refine ⟨hp0, hp1, htop, ?_⟩
    have hfin : ∀ i, f (n * p i) = ((f (n * p i)).toReal : EReal) := fun i =>
      (EReal.coe_toReal (htop i) (hA.1.ne_bot _)).symm
    have : ∑ i, ((1 / (n:ℝ) : ℝ) : EReal) * f (n * p i) =
        ((∑ i, 1 / (n:ℝ) * (f (n * p i)).toReal : ℝ) : EReal) := by
      rw [ereal_coe_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hfin i, EReal.toReal_coe, ← EReal.coe_mul]
    rw [this] at hD
    have hD' : ∑ i, 1 / (n:ℝ) * (f (n * p i)).toReal ≤ ρ / n := by exact_mod_cast hD
    rw [← Finset.mul_sum] at hD'
    rw [div_eq_mul_inv, one_mul, div_eq_mul_inv, mul_comm ρ] at hD'
    exact le_of_mul_le_mul_left hD' (by positivity)
  · rintro ⟨hp0, hp1, htop, hsum⟩
    refine ⟨hp0, hp1, ?_⟩
    have hfin : ∀ i, f (n * p i) = ((f (n * p i)).toReal : EReal) := fun i =>
      (EReal.coe_toReal (htop i) (hA.1.ne_bot _)).symm
    have : ∑ i, ((1 / (n:ℝ) : ℝ) : EReal) * f (n * p i) =
        ((∑ i, 1 / (n:ℝ) * (f (n * p i)).toReal : ℝ) : EReal) := by
      rw [ereal_coe_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hfin i, EReal.toReal_coe, ← EReal.coe_mul]
    rw [this]
    have : ∑ i, 1 / (n:ℝ) * (f (n * p i)).toReal ≤ ρ / n := by
      rw [← Finset.mul_sum, div_eq_mul_inv ρ, one_div, mul_comm ρ]
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    exact_mod_cast this



lemma g_conv (f : ℝ → EReal) (hA : AssumptionA f) (t u θ : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hft : f t ≠ ⊤) (hfu : f u ≠ ⊤) :
    f (θ * t + (1 - θ) * u) ≠ ⊤ ∧
      (f (θ * t + (1 - θ) * u)).toReal ≤ θ * (f t).toReal + (1 - θ) * (f u).toReal := by
  have hc := hA.1.convex t u θ ht hu hθ0 hθ1
  rw [← EReal.coe_toReal hft (hA.1.ne_bot _), ← EReal.coe_toReal hfu (hA.1.ne_bot _),
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hc
  refine ⟨fun h => ?_, ?_⟩
  · rw [h] at hc; exact EReal.coe_ne_top _ (top_le_iff.mp hc)
  · have := EReal.toReal_le_toReal hc (hA.1.ne_bot _) (EReal.coe_ne_top _)
    rwa [EReal.toReal_coe] at this

lemma g_convexOn (f : ℝ → EReal) (hA : AssumptionA f) :
    ConvexOn ℝ (Set.Ioi 0) (fun t => (f t).toReal) := by
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  have := (g_conv f hA x y a (le_of_lt hx) (le_of_lt hy) ha (by linarith)
    (hA.1.ne_top_of_pos x hx) (hA.1.ne_top_of_pos y hy)).2
  simpa [smul_eq_mul] using this

end GEL13

open GenEmpLik.Coverage GEL13

theorem solution (f : ℝ → EReal) (hA : AssumptionA f)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ cf Cf : ℝ, 0 < cf ∧ cf ≤ Cf ∧
      (∀ n : ℕ, 0 < n → ∀ p ∈ divergenceBall f ρ n,
        Real.sqrt (∑ i : Fin n, ((n : ℝ) * p i - 1) ^ 2) ≤ Real.sqrt (ρ * Cf)) ∧
      (∃ n : ℕ, 0 < n ∧ ∃ p ∈ divergenceBall f ρ n,
        Real.sqrt (ρ * cf) ≤ Real.sqrt (∑ i : Fin n, ((n : ℝ) * p i - 1) ^ 2)) := by
  set g : ℝ → ℝ := fun t => (f t).toReal with hg
  obtain ⟨hφ, _, a, b, ha0, ha1, hb1, hcd, hd1, hd2⟩ := hA
  have hA' : AssumptionA f := ⟨hφ, ‹_›, a, b, ha0, ha1, hb1, hcd, hd1, hd2⟩
  have hgnn : ∀ t, 0 ≤ t → 0 ≤ g t := fun t ht => EReal.toReal_nonneg (f_nonneg f hA' t ht)
  have hg1 : g 1 = 0 := by simp [hg, hφ.map_one]
  have hU : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have h1 : ContDiffOn ℝ 2 (deriv g) (Set.Ioo a b) := hcd.deriv_of_isOpen hU (by norm_num)
  have hgdiff : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ g x := fun x hx =>
    ((hcd.differentiableOn (by norm_num)) x hx).differentiableAt (hU.mem_nhds hx)
  have hdd : HasDerivAt (deriv g) 2 1 := by
    have hd : DifferentiableAt ℝ (deriv g) 1 :=
      ((h1.differentiableOn (by norm_num)) 1 ⟨ha1, hb1⟩).differentiableAt (hU.mem_nhds ⟨ha1, hb1⟩)
    have : deriv (deriv g) 1 = 2 := by
      rw [← hd2, iteratedDeriv_succ, iteratedDeriv_one]
    rw [← this]; exact hd.hasDerivAt
  -- slope of g' at 1 eventually > 1
  have hsl := (tendsto_order.1 (hasDerivAt_iff_tendsto_slope.1 hdd)).1 1 (by norm_num)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hsl
  obtain ⟨ε, hε, hεs⟩ := hsl
  set δ := min (min (ε / 2) (1 / 4)) (min ((1 - a) / 2) ((b - 1) / 2)) with hδ
  have hδpos : 0 < δ := by
    simp only [hδ, lt_min_iff]; refine ⟨⟨by linarith, by norm_num⟩, by linarith, by linarith⟩
  have hδε : δ < ε := by
    have : δ ≤ ε / 2 := (min_le_left _ _).trans (min_le_left _ _); linarith
  have hδq : δ ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hδa : δ ≤ (1 - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδb : δ ≤ (b - 1) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hin : ∀ u, |u| ≤ δ → 1 + u ∈ Set.Ioo a b := by
    intro u hu; rw [abs_le] at hu; constructor <;> linarith [hu.1, hu.2]
  have hgd_pos : ∀ u, 0 < u → u ≤ δ → u ≤ deriv g (1 + u) := by
    intro u hu0 huδ
    have h := hεs (y := 1 + u) (by rw [Real.dist_eq]; simp; rw [abs_of_pos hu0]; linarith)
      (by simp; linarith)
    rw [slope_def_field, hd1, sub_zero, show 1 + u - 1 = u by ring, lt_div_iff₀ hu0] at h
    linarith
  have hgd_neg : ∀ u, u < 0 → -δ ≤ u → deriv g (1 + u) ≤ u := by
    intro u hu0 huδ
    have h := hεs (y := 1 + u) (by rw [Real.dist_eq]; simp; rw [abs_of_neg hu0]; linarith)
      (by simp; linarith)
    rw [slope_def_field, hd1, sub_zero, show 1 + u - 1 = u by ring, lt_div_iff_of_neg hu0] at h
    linarith
  have hconv := g_convexOn f hA'
  set r := 2 * δ with hr
  have hrpos : 0 < r := by linarith
  -- near bound
  have hnear : ∀ s, |s| ≤ r → s ^ 2 / 4 ≤ g (1 + s) := by
    intro s hs
    rw [abs_le] at hs
    rcases lt_trichotomy s 0 with hs0 | hs0 | hs0
    · have hx : 1 + s / 2 ∈ Set.Ioi (0:ℝ) := by simp; linarith
      have hy : 1 + s ∈ Set.Ioi (0:ℝ) := by simp; linarith
      have hlt : 1 + s < 1 + s / 2 := by linarith
      have hdx := hgdiff _ (hin (s / 2) (by rw [abs_le]; constructor <;> linarith))
      have h := hconv.slope_le_deriv hy hx hlt hdx
      have hdn := hgd_neg (s / 2) (by linarith) (by linarith)
      rw [slope_def_field, div_le_iff₀ (by linarith)] at h
      have hgx := hgnn (1 + s / 2) (by linarith)
      nlinarith
    · subst hs0; simp [hg1]
    · have hx : 1 + s / 2 ∈ Set.Ioi (0:ℝ) := by simp; linarith
      have hy : 1 + s ∈ Set.Ioi (0:ℝ) := by simp; linarith
      have hlt : 1 + s / 2 < 1 + s := by linarith
      have hdx := hgdiff _ (hin (s / 2) (by rw [abs_le]; constructor <;> linarith))
      have h := hconv.deriv_le_slope hx hy hlt hdx
      have hdp := hgd_pos (s / 2) (by linarith) (by linarith)
      rw [slope_def_field, le_div_iff₀ (by linarith)] at h
      have hgx := hgnn (1 + s / 2) (by linarith)
      nlinarith
  -- far bound
  have hfar : ∀ s, -1 ≤ s → r ≤ |s| → f (1 + s) ≠ ⊤ → r * |s| / 4 ≤ g (1 + s) := by
    intro s hs1 hsr hft
    have habs : 0 < |s| := lt_of_lt_of_le hrpos hsr
    set θ := r / |s| with hθ
    have hθ0 : 0 < θ := div_pos hrpos habs
    have hθ1 : θ ≤ 1 := (div_le_one habs).2 hsr
    have hc := (g_conv f hA' (1 + s) 1 θ (by linarith) zero_le_one hθ0.le hθ1 hft
      (by rw [hφ.map_one]; exact EReal.zero_ne_top)).2
    have heq : θ * (1 + s) + (1 - θ) * 1 = 1 + θ * s := by ring
    rw [heq, show (f 1).toReal = 0 from by simp [hφ.map_one], mul_zero, add_zero] at hc
    have hθs : |θ * s| = r := by
      rw [abs_mul, abs_of_pos hθ0, hθ, div_mul_cancel₀ _ habs.ne']
    have hn := hnear (θ * s) hθs.le
    have hsq : (θ * s) ^ 2 = r ^ 2 := by rw [← sq_abs, hθs]
    rw [hsq] at hn
    have : r ^ 2 / 4 ≤ θ * g (1 + s) := hn.trans hc
    rw [hθ, div_mul_eq_mul_div, le_div_iff₀ habs] at this
    nlinarith
  set A := 4 + 16 * ρ / r ^ 2 with hAdef
  have hApos : 0 < A := by positivity
  -- per-term bound
  have hterm : ∀ s, -1 ≤ s → f (1 + s) ≠ ⊤ → g (1 + s) ≤ ρ → s ^ 2 ≤ A * g (1 + s) := by
    intro s hs1 hft hgρ
    have hg0 := hgnn (1 + s) (by linarith)
    by_cases hsr : |s| ≤ r
    · have := hnear s hsr
      have : 0 ≤ 16 * ρ / r ^ 2 * g (1 + s) := by positivity
      nlinarith
    · push Not at hsr
      have hf := hfar s hs1 hsr.le hft
      have habs : |s| ≤ 4 * ρ / r := by
        rw [le_div_iff₀ hrpos]; nlinarith
      have h2 : |s| * (r * |s|) ≤ (4 * ρ / r) * (4 * g (1 + s)) := by
        apply mul_le_mul habs (by linarith) (by positivity) (by positivity)
      have h3 : s ^ 2 = |s| * |s| := by rw [← sq_abs, sq]
      have h4 : (4 * ρ / r) * (4 * g (1 + s)) = 16 * ρ / r ^ 2 * g (1 + s) * r := by
        field_simp; ring
      rw [h4] at h2
      have h5 : |s| * |s| ≤ 16 * ρ / r ^ 2 * g (1 + s) := by
        have : |s| * (r * |s|) = (|s| * |s|) * r := by ring
        rw [this] at h2
        exact le_of_mul_le_mul_right h2 hrpos
      nlinarith
  -- lower construction
  have hgc : ContinuousAt g 1 := (hgdiff 1 ⟨ha1, hb1⟩).continuousAt
  obtain ⟨δ', hδ', hδ's⟩ := Metric.continuousAt_iff.1 hgc (ρ / 2) (by linarith)
  set s₀ := min δ' 1 / 2 with hs₀
  have hs₀pos : 0 < s₀ := by positivity
  have hs₀lt : s₀ < δ' := by
    have := min_le_left δ' 1; linarith
  have hs₀1 : s₀ ≤ 1 / 2 := by
    have := min_le_right δ' 1; linarith
  have hgp : g (1 + s₀) < ρ / 2 := by
    have := hδ's (x := 1 + s₀) (by rw [Real.dist_eq]; simp; rw [abs_of_pos hs₀pos]; exact hs₀lt)
    rw [Real.dist_eq, hg1, sub_zero] at this
    exact lt_of_abs_lt this
  have hgm : g (1 - s₀) < ρ / 2 := by
    have := hδ's (x := 1 - s₀) (by rw [Real.dist_eq]; simp; rw [abs_of_pos hs₀pos]; exact hs₀lt)
    rw [Real.dist_eq, hg1, sub_zero] at this
    exact lt_of_abs_lt this
  set cf := min (2 * s₀ ^ 2 / ρ) A with hcf
  refine ⟨cf, A, lt_min (by positivity) hApos, min_le_right _ _, ?_, ?_⟩
  · intro n hn p hp
    rw [ball_iff f hA' ρ n hn] at hp
    obtain ⟨hp0, hp1, hpt, hps⟩ := hp
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    apply Real.sqrt_le_sqrt
    have hle : ∀ i, (f (n * p i)).toReal ≤ ρ := fun i =>
      le_trans (Finset.single_le_sum (f := fun j => (f (n * p j)).toReal)
        (fun j _ => hgnn _ (mul_nonneg hnR.le (hp0 j))) (Finset.mem_univ i)) hps
    calc ∑ i, ((n:ℝ) * p i - 1) ^ 2 ≤ ∑ i, A * (f (n * p i)).toReal := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have e : (1:ℝ) + ((n:ℝ) * p i - 1) = n * p i := by ring
          have := hterm ((n:ℝ) * p i - 1) (by have := mul_nonneg hnR.le (hp0 i); linarith) (by rw [e]; exact hpt i)
            (by rw [e]; exact hle i)
          rwa [e] at this
      _ = A * ∑ i, (f (n * p i)).toReal := by rw [Finset.mul_sum]
      _ ≤ A * ρ := mul_le_mul_of_nonneg_left hps hApos.le
      _ = ρ * A := mul_comm _ _
  · refine ⟨2, by norm_num, ![(1 + s₀) / 2, (1 - s₀) / 2], ?_, ?_⟩
    · rw [ball_iff f hA' ρ 2 (by norm_num)]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp <;> linarith
      · simp [Fin.sum_univ_two]; ring
      · intro i
        fin_cases i
        · exact hφ.ne_top_of_pos _ (by simp; linarith)
        · exact hφ.ne_top_of_pos _ (by simp; linarith)
      · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        have e1 : ((2:ℕ):ℝ) * ((1 + s₀) / 2) = 1 + s₀ := by push_cast; ring
        have e2 : ((2:ℕ):ℝ) * ((1 - s₀) / 2) = 1 - s₀ := by push_cast; ring
        rw [e1, e2]
        linarith
    · apply Real.sqrt_le_sqrt
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      have : ρ * cf ≤ ρ * (2 * s₀ ^ 2 / ρ) := mul_le_mul_of_nonneg_left (min_le_left _ _) hρ.le
      rw [mul_div_cancel₀ _ hρ.ne'] at this
      push_cast
      nlinarith
