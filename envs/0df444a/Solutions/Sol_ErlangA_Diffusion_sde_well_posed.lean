-- Prove2me | solution 1 for ErlangA.Diffusion.sde_well_posed
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:06:40.855805+00:00
-- url     : https://prove2.me/submissions/cd89e027-613c-4d99-9c2c-64cce3f50dab

import Mathlib
import Definitions.Def_ErlangA_Diffusion_SDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ErlangASdeWP

/-- Picard iterates for `y(t) = x0 + ∫₀ᵗ F(y(s) + w(s)) ds`. -/
noncomputable def pic (F : ℝ → ℝ) (x0 : ℝ) (w : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => x0
  | n+1 => fun t => x0 + ∫ s in (0:ℝ)..t, F (pic F x0 w n s + w s)

noncomputable def picLim (F : ℝ → ℝ) (x0 : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  x0 + ∑' n, (pic F x0 w (n+1) t - pic F x0 w n t)

lemma iter_bound (L C T : ℝ) (hL : 0 ≤ L) (e : ℕ → ℝ → ℝ)
    (hcont : ∀ n, ContinuousOn (e n) (Set.Icc 0 T))
    (h0 : ∀ t ∈ Set.Icc 0 T, |e 0 t| ≤ C)
    (hstep : ∀ n, ∀ t ∈ Set.Icc 0 T, |e (n+1) t| ≤ L * ∫ s in (0:ℝ)..t, |e n s|) :
    ∀ n, ∀ t ∈ Set.Icc 0 T, |e n t| ≤ C * (L * t) ^ n / n.factorial := by
  intro n
  induction n with
  | zero => intro t ht; simpa using h0 t ht
  | succ n ih =>
    intro t ht
    have hsub : Set.uIcc 0 t ⊆ Set.Icc 0 T := by
      rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2
    have hint1 : IntervalIntegrable (fun s => |e n s|) volume 0 t :=
      ((hcont n).mono hsub).abs.intervalIntegrable
    have hint2 : IntervalIntegrable (fun s : ℝ => C * (L * s) ^ n / n.factorial) volume 0 t := by
      apply Continuous.intervalIntegrable; fun_prop
    have hmono : ∫ s in (0:ℝ)..t, |e n s| ≤ ∫ s in (0:ℝ)..t, C * (L * s) ^ n / n.factorial := by
      apply intervalIntegral.integral_mono_on ht.1 hint1 hint2
      intro s hs
      exact ih s ⟨hs.1, hs.2.trans ht.2⟩
    have hcalc : ∫ s in (0:ℝ)..t, C * (L * s) ^ n / n.factorial
        = C * L ^ n / n.factorial * (t ^ (n+1) / (n+1)) := by
      have : (fun s : ℝ => C * (L * s) ^ n / n.factorial)
          = fun s => (C * L ^ n / n.factorial) * s ^ n := by
        funext s; rw [mul_pow]; ring
      rw [this, intervalIntegral.integral_const_mul, integral_pow]; simp
    calc |e (n+1) t| ≤ L * ∫ s in (0:ℝ)..t, |e n s| := hstep n t ht
      _ ≤ L * (C * L ^ n / n.factorial * (t ^ (n+1) / (n+1))) := by
          rw [← hcalc]; exact mul_le_mul_of_nonneg_left hmono hL
      _ = C * (L * t) ^ (n+1) / (n+1).factorial := by
          rw [Nat.factorial_succ]; push_cast; field_simp; ring

lemma int_diff_le (F : ℝ → ℝ) (L : ℝ) (hF : ∀ x y, |F x - F y| ≤ L * |x - y|)
    (hFc : Continuous F) (u v : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hu : ContinuousOn u (Set.Icc 0 t)) (hv : ContinuousOn v (Set.Icc 0 t)) :
    |(∫ s in (0:ℝ)..t, F (u s)) - ∫ s in (0:ℝ)..t, F (v s)|
      ≤ L * ∫ s in (0:ℝ)..t, |u s - v s| := by
  have hu' : ContinuousOn u (Set.uIcc 0 t) := by rwa [Set.uIcc_of_le ht]
  have hv' : ContinuousOn v (Set.uIcc 0 t) := by rwa [Set.uIcc_of_le ht]
  have hFu : IntervalIntegrable (fun s => F (u s)) volume 0 t :=
    (hFc.comp_continuousOn hu').intervalIntegrable
  have hFv : IntervalIntegrable (fun s => F (v s)) volume 0 t :=
    (hFc.comp_continuousOn hv').intervalIntegrable
  rw [← intervalIntegral.integral_sub hFu hFv, ← intervalIntegral.integral_const_mul]
  calc _ ≤ ∫ s in (0:ℝ)..t, |F (u s) - F (v s)| :=
        intervalIntegral.abs_integral_le_integral_abs ht
    _ ≤ ∫ s in (0:ℝ)..t, L * |u s - v s| := by
        apply intervalIntegral.integral_mono_on ht (hFu.sub hFv).abs
          (((hu'.sub hv').abs).intervalIntegrable.const_mul L)
        intro s _; exact hF _ _

lemma pic_cont (F : ℝ → ℝ) (hFc : Continuous F) (x0 : ℝ) (w : ℝ → ℝ) (hw : Continuous w) :
    ∀ n, Continuous (pic F x0 w n)
  | 0 => continuous_const
  | n+1 => by
      have hc : Continuous (fun s => F (pic F x0 w n s + w s)) :=
        hFc.comp ((pic_cont F hFc x0 w hw n).add hw)
      exact continuous_const.add
        (intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0)

lemma pic_at_zero (F : ℝ → ℝ) (x0 : ℝ) (w : ℝ → ℝ) : ∀ n, pic F x0 w n 0 = x0
  | 0 => rfl
  | n+1 => by simp [pic]

lemma pic_step (F : ℝ → ℝ) (L : ℝ) (hF : ∀ x y, |F x - F y| ≤ L * |x - y|)
    (hFc : Continuous F) (x0 : ℝ) (w : ℝ → ℝ) (hw : Continuous w) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    |pic F x0 w (n+2) t - pic F x0 w (n+1) t|
      ≤ L * ∫ s in (0:ℝ)..t, |pic F x0 w (n+1) s - pic F x0 w n s| := by
  have h := int_diff_le F L hF hFc (fun s => pic F x0 w (n+1) s + w s)
    (fun s => pic F x0 w n s + w s) t ht
    (((pic_cont F hFc x0 w hw (n+1)).add hw).continuousOn)
    (((pic_cont F hFc x0 w hw n).add hw).continuousOn)
  simp only [add_sub_add_right_eq_sub] at h
  have e2 : pic F x0 w (n+2) t - pic F x0 w (n+1) t
      = (∫ s in (0:ℝ)..t, F (pic F x0 w (n+1) s + w s))
        - ∫ s in (0:ℝ)..t, F (pic F x0 w n s + w s) := by
    simp only [pic]; ring
  rw [e2]; exact h

lemma pic_unif (F : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) (hF : ∀ x y, |F x - F y| ≤ L * |x - y|)
    (hFc : Continuous F) (x0 : ℝ) (w : ℝ → ℝ) (hw : Continuous w) (T : ℝ) :
    TendstoUniformlyOn (fun N => pic F x0 w N) (picLim F x0 w) atTop (Set.Icc 0 T) := by
  set e : ℕ → ℝ → ℝ := fun n t => pic F x0 w (n+1) t - pic F x0 w n t with he
  have hcont : ∀ n, ContinuousOn (e n) (Set.Icc 0 T) := fun n =>
    ((pic_cont F hFc x0 w hw (n+1)).sub (pic_cont F hFc x0 w hw n)).continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont 0)
  set C' := max C 0
  have h0 : ∀ t ∈ Set.Icc 0 T, |e 0 t| ≤ C' := fun t ht =>
    (by simpa [Real.norm_eq_abs] using hC t ht : |e 0 t| ≤ C).trans (le_max_left _ _)
  have hb := iter_bound L C' T hL e hcont h0
    (fun n t ht => pic_step F L hF hFc x0 w hw n t ht.1)
  set u : ℕ → ℝ := fun n => C' * ((L * T) ^ n / n.factorial)
  have hu : Summable u := (Real.summable_pow_div_factorial (L * T)).mul_left C'
  have hfu : ∀ n, ∀ t ∈ Set.Icc 0 T, ‖e n t‖ ≤ u n := by
    intro n t ht
    rw [Real.norm_eq_abs]
    refine (hb n t ht).trans ?_
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (mul_nonneg hL ht.1) (mul_le_mul_of_nonneg_left ht.2 hL) n
  have hT := tendstoUniformlyOn_tsum_nat hu hfu
  have hsum : ∀ N t, pic F x0 w N t = x0 + ∑ n ∈ Finset.range N, e n t := by
    intro N t
    rw [he]; simp only
    rw [Finset.sum_range_sub (fun n => pic F x0 w n t)]
    simp [pic]
  rw [Metric.tendstoUniformlyOn_iff] at hT ⊢
  intro ε hε
  filter_upwards [hT ε hε] with N hN t ht
  rw [hsum, picLim, dist_add_left]
  exact hN t ht

lemma picLim_cont (F : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) (hF : ∀ x y, |F x - F y| ≤ L * |x - y|)
    (hFc : Continuous F) (x0 : ℝ) (w : ℝ → ℝ) (hw : Continuous w) (T : ℝ) :
    ContinuousOn (picLim F x0 w) (Set.Icc 0 T) :=
  (pic_unif F L hL hF hFc x0 w hw T).continuousOn
    (Eventually.of_forall fun N => (pic_cont F hFc x0 w hw N).continuousOn).frequently

lemma picLim_contOn (F : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) (hF : ∀ x y, |F x - F y| ≤ L * |x - y|)
    (hFc : Continuous F) (x0 : ℝ) (w : ℝ → ℝ) (hw : Continuous w) :
    ContinuousOn (picLim F x0 w) (Set.Ici 0) := by
  intro x hx
  have h1 := (picLim_cont F L hL hF hFc x0 w hw (x+1)) x ⟨hx, by linarith⟩
  apply h1.mono_of_mem_nhdsWithin
  refine mem_nhdsWithin.2 ⟨Set.Iio (x+1), isOpen_Iio, by simp, ?_⟩
  rintro y ⟨h1, h2⟩
  exact ⟨h2, (Set.mem_Iio.1 h1).le⟩

lemma picLim_eq (F : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) (hF : ∀ x y, |F x - F y| ≤ L * |x - y|)
    (hFc : Continuous F) (x0 : ℝ) (w : ℝ → ℝ) (hw : Continuous w) (t : ℝ) (ht : 0 ≤ t) :
    picLim F x0 w t = x0 + ∫ s in (0:ℝ)..t, F (picLim F x0 w s + w s) := by
  have hU := pic_unif F L hL hF hFc x0 w hw t
  have hmem : t ∈ Set.Icc 0 t := ⟨ht, le_rfl⟩
  have h1 : Tendsto (fun N => pic F x0 w (N+1) t) atTop (𝓝 (picLim F x0 w t)) :=
    (hU.tendsto_at hmem).comp (tendsto_add_atTop_nat 1)
  have hlc := picLim_cont F L hL hF hFc x0 w hw t
  have h2 : Tendsto (fun N => pic F x0 w (N+1) t) atTop
      (𝓝 (x0 + ∫ s in (0:ℝ)..t, F (picLim F x0 w s + w s))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : 0 < ε / (L * t + 1) := div_pos hε (by positivity)
    obtain ⟨N0, hN0⟩ := Metric.tendstoUniformlyOn_iff.1 hU _ hδ |>.exists_forall_of_atTop
    refine ⟨N0, fun N hN => ?_⟩
    have hd := int_diff_le F L hF hFc (fun s => pic F x0 w N s + w s)
      (fun s => picLim F x0 w s + w s) t ht
      (((pic_cont F hFc x0 w hw N).add hw).continuousOn) (hlc.add hw.continuousOn)
    simp only [add_sub_add_right_eq_sub] at hd
    have hint : ∫ s in (0:ℝ)..t, |pic F x0 w N s - picLim F x0 w s|
        ≤ ∫ s in (0:ℝ)..t, ε / (L * t + 1) := by
      apply intervalIntegral.integral_mono_on ht
      · exact (((pic_cont F hFc x0 w hw N).continuousOn.sub hlc).abs.mono
          (by rw [Set.uIcc_of_le ht])).intervalIntegrable
      · exact intervalIntegrable_const
      · intro s hs
        have := hN0 N hN s hs
        rw [Real.dist_eq, abs_sub_comm] at this
        exact this.le
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
    rw [Real.dist_eq]
    have e1 : pic F x0 w (N+1) t - (x0 + ∫ s in (0:ℝ)..t, F (picLim F x0 w s + w s))
        = (∫ s in (0:ℝ)..t, F (pic F x0 w N s + w s))
          - ∫ s in (0:ℝ)..t, F (picLim F x0 w s + w s) := by
      simp only [pic]; ring
    rw [e1]
    calc _ ≤ L * ∫ s in (0:ℝ)..t, |pic F x0 w N s - picLim F x0 w s| := hd
      _ ≤ L * (t * (ε / (L * t + 1))) := mul_le_mul_of_nonneg_left hint hL
      _ < ε := by
        rw [← mul_assoc, mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [mul_nonneg hL ht]
  exact tendsto_nhds_unique h1 h2

lemma picLim_zero (F : ℝ → ℝ) (x0 : ℝ) (w : ℝ → ℝ) : picLim F x0 w 0 = x0 := by
  simp [picLim, pic_at_zero]

lemma uniq_det (L : ℝ) (hL : 0 ≤ L) (u v : ℝ → ℝ) (hu : ContinuousOn u (Set.Ici 0))
    (hv : ContinuousOn v (Set.Ici 0))
    (h : ∀ t, 0 ≤ t → |u t - v t| ≤ L * ∫ s in (0:ℝ)..t, |u s - v s|) :
    ∀ t, 0 ≤ t → u t = v t := by
  intro t ht
  have hcont : ContinuousOn (fun s => u s - v s) (Set.Icc 0 t) :=
    (hu.sub hv).mono Set.Icc_subset_Ici_self
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set C' := max C 0
  have hb := iter_bound L C' t hL (fun _ s => u s - v s) (fun _ => hcont)
    (fun s hs => (by simpa [Real.norm_eq_abs] using hC s hs : |u s - v s| ≤ C).trans
      (le_max_left _ _))
    (fun n s hs => h s hs.1)
  have hlim : Tendsto (fun n : ℕ => C' * ((L * t) ^ n / n.factorial)) atTop (𝓝 (C' * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (L * t)).const_mul C'
  rw [mul_zero] at hlim
  have : |u t - v t| ≤ 0 := ge_of_tendsto' hlim (fun n => by
    rw [← mul_div_assoc]; exact hb n t ⟨ht, le_rfl⟩)
  have := abs_nonpos_iff.1 this
  linarith

lemma meas_iint {Ω : Type*} {m : MeasurableSpace Ω} (G : Ω → ℝ → ℝ)
    (hc : ∀ ω, Continuous (G ω)) (hm : ∀ r, Measurable (fun ω => G ω r)) (a b : ℝ) :
    Measurable (fun ω => ∫ r in a..b, G ω r) := by
  have hu : Measurable (Function.uncurry (fun r ω => G ω r)) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => hc ω) hm
  have hG : StronglyMeasurable (Function.uncurry G) := by
    have : Function.uncurry G = Function.uncurry (fun r ω => G ω r) ∘ Prod.swap := by
      ext ⟨ω, r⟩; rfl
    rw [this]; exact (hu.comp measurable_swap).stronglyMeasurable
  have h1 := hG.integral_prod_right (ν := volume.restrict (Set.Ioc a b))
  have h2 := hG.integral_prod_right (ν := volume.restrict (Set.Ioc b a))
  simp only [intervalIntegral]
  exact h1.measurable.sub h2.measurable

/-- Measurability of the Picard iterates with respect to a σ-algebra in which `x0` and all
`w s`, `s ≤ T`, are measurable. -/
lemma pic_meas {Ω : Type*} {m : MeasurableSpace Ω} (F : ℝ → ℝ) (hFc : Continuous F)
    (x0 : Ω → ℝ) (w : Ω → ℝ → ℝ) (hw : ∀ ω, Continuous (w ω)) (T : ℝ) (hT : 0 ≤ T)
    (hx0 : Measurable x0) (hwm : ∀ s, s ≤ T → Measurable (fun ω => w ω s)) :
    ∀ n, ∀ s, s ≤ T → Measurable (fun ω => pic F (x0 ω) (w ω) n s)
  | 0 => fun s _ => hx0
  | n+1 => by
      intro s hs
      have ih := pic_meas F hFc x0 w hw T hT hx0 hwm n
      set a := min 0 s
      set c := max 0 s
      have hcT : c ≤ T := max_le hT hs
      let cl : ℝ → ℝ := fun r => max a (min r c)
      have hcl : Continuous cl := by fun_prop
      have hclT : ∀ r, cl r ≤ T := fun r =>
        (max_le (min_le_left _ _ |>.trans (le_max_left 0 s)) (min_le_right _ _)).trans hcT
      let G : Ω → ℝ → ℝ := fun ω r => F (pic F (x0 ω) (w ω) n (cl r) + w ω (cl r))
      have hGc : ∀ ω, Continuous (G ω) := fun ω =>
        hFc.comp (((pic_cont F hFc (x0 ω) (w ω) (hw ω) n).comp hcl).add ((hw ω).comp hcl))
      have hGm : ∀ r, Measurable (fun ω => G ω r) := fun r =>
        hFc.measurable.comp ((ih (cl r) (hclT r)).add (hwm (cl r) (hclT r)))
      have heq : ∀ ω, (∫ r in (0:ℝ)..s, F (pic F (x0 ω) (w ω) n r + w ω r))
          = ∫ r in (0:ℝ)..s, G ω r := by
        intro ω
        apply intervalIntegral.integral_congr
        intro r hr
        have : cl r = r := by
          simp only [cl, a, c]
          rw [Set.mem_uIcc] at hr
          rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [min_eq_left (h2.trans (le_max_right _ _)),
              max_eq_right ((min_le_left _ _).trans h1)]
          · rw [min_eq_left (h2.trans (le_max_left _ _)),
              max_eq_right ((min_le_right _ _).trans h1)]
        simp only [G, this]
      have : (fun ω => pic F (x0 ω) (w ω) (n+1) s)
          = fun ω => x0 ω + ∫ r in (0:ℝ)..s, G ω r := by
        funext ω; simp only [pic]; rw [heq]
      rw [this]
      exact hx0.add (meas_iint G hGc hGm 0 s)

end ErlangASdeWP

namespace ErlangA.Diffusion
open ErlangASdeWP

lemma drift_lip (μ β θ : ℝ) (hμ : 0 < μ) (hθ : 0 < θ) (x y : ℝ) :
    |drift μ β θ x - drift μ β θ y| ≤ max μ θ * |x - y| := by
  have hm1 := le_max_left μ θ
  have hm2 := le_max_right μ θ
  unfold drift
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonpos (by linarith : x - y ≤ 0)]
    split_ifs with h1 h2 h2
    · rw [abs_le]; constructor <;> nlinarith
    · rw [abs_le]; constructor <;> nlinarith
    · exfalso; linarith
    · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ x - y)]
    split_ifs with h1 h2 h2
    · rw [abs_le]; constructor <;> nlinarith
    · exfalso; linarith
    · rw [abs_le]; constructor <;> nlinarith
    · rw [abs_le]; constructor <;> nlinarith

end ErlangA.Diffusion

open ErlangA.Diffusion ErlangASdeWP

theorem solution (μ β θ : ℝ) (hμ : 0 < μ) (hθ : 0 < θ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ≥0 → Ω → ℝ) (hb : IsStandardBM P b)
    (X0 : Ω → ℝ) (hX0 : Measurable X0)
    (hind : IndepFun X0 (fun ω (t : ℝ≥0) => b t ω) P) :
    (∃ q : Ω → ℝ → ℝ, (∀ ω, q ω 0 = X0 ω) ∧ IsAdaptedToInitialAndBM b X0 q ∧
      SolvesDiffusionSDE P μ β θ b q) ∧
    ∀ q q' : Ω → ℝ → ℝ, SolvesDiffusionSDE P μ β θ b q → SolvesDiffusionSDE P μ β θ b q' →
      (∀ᵐ ω ∂P, q ω 0 = q' ω 0) → ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → q ω t = q' ω t := by
  set L := max μ θ with hLdef
  have hL : 0 ≤ L := le_trans hμ.le (le_max_left _ _)
  have hF := drift_lip μ β θ hμ hθ
  have hFc : Continuous (drift μ β θ) :=
    (LipschitzWith.of_dist_le_mul (K := ⟨L, hL⟩)
      (fun x y => by rw [Real.dist_eq, Real.dist_eq]; exact hF x y)).continuous
  let w : Ω → ℝ → ℝ := fun ω s => Real.sqrt (2 * μ) * (b s.toNNReal ω - b 0 ω)
  have hw : ∀ ω, Continuous (w ω) := fun ω =>
    continuous_const.mul (((hb.2.2 ω).comp continuous_real_toNNReal).sub continuous_const)
  let q : Ω → ℝ → ℝ := fun ω t => picLim (drift μ β θ) (X0 ω) (w ω) t + w ω t
  have hq0 : ∀ ω, q ω 0 = X0 ω := by intro ω; simp [q, w, picLim_zero]
  refine ⟨⟨q, hq0, ?_, ?_⟩, ?_⟩
  · intro T
    set M := MeasurableSpace.comap X0 inferInstance ⊔
      MeasurableSpace.comap (fun ω (s : Set.Iic T) => b s ω) inferInstance
    have hx0 : Measurable[M] X0 := (comap_measurable X0).mono le_sup_left le_rfl
    have hbm : ∀ s : ℝ≥0, s ≤ T → Measurable[M] (b s) := by
      intro s hs
      have : (b s) = (fun f : Set.Iic T → ℝ => f ⟨s, hs⟩) ∘
          (fun ω (s : Set.Iic T) => b s ω) := rfl
      rw [this]
      have h1 : Measurable[MeasurableSpace.comap (fun ω (s : Set.Iic T) => b s ω) inferInstance]
          ((fun f : Set.Iic T → ℝ => f ⟨s, hs⟩) ∘ (fun ω (s : Set.Iic T) => b s ω)) :=
        (measurable_pi_apply _).comp (comap_measurable _)
      exact h1.mono le_sup_right le_rfl
    have hwm : ∀ s : ℝ, s ≤ T → Measurable[M] (fun ω => w ω s) := by
      intro s hs
      exact measurable_const.mul
        ((hbm _ (Real.toNNReal_le_iff_le_coe.2 hs)).sub (hbm 0 bot_le))
    have hpm := @pic_meas Ω M (drift μ β θ) hFc X0 w hw T T.2 hx0 hwm
    have hlim : Measurable[M] (fun ω => picLim (drift μ β θ) (X0 ω) (w ω) T) := by
      apply @measurable_of_tendsto_metrizable Ω ℝ M _ _ _ _
        (fun N ω => pic (drift μ β θ) (X0 ω) (w ω) N T)
      · intro N; exact hpm N T le_rfl
      · rw [tendsto_pi_nhds]; intro ω
        exact (pic_unif (drift μ β θ) L hL hF hFc (X0 ω) (w ω) (hw ω) T).tendsto_at
          ⟨T.2, le_rfl⟩
    exact hlim.add (hwm T le_rfl)
  · refine ⟨fun ω => (picLim_contOn _ L hL hF hFc (X0 ω) (w ω) (hw ω)).add
      (hw ω).continuousOn, ?_⟩
    filter_upwards [hb.1.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω t ht
    rw [hq0 ω]
    simp only [q]
    rw [picLim_eq _ L hL hF hFc (X0 ω) (w ω) (hw ω) t ht]
    simp only [w, hω, sub_zero]
  · intro q1 q2 h1 h2 h0
    filter_upwards [h1.2, h2.2, h0] with ω e1 e2 e0
    apply uniq_det L hL (q1 ω) (q2 ω) (h1.1 ω) (h2.1 ω)
    intro t ht
    have : q1 ω t - q2 ω t = (∫ s in (0:ℝ)..t, drift μ β θ (q1 ω s))
        - ∫ s in (0:ℝ)..t, drift μ β θ (q2 ω s) := by
      rw [e1 t ht, e2 t ht, e0]; ring
    rw [this]
    exact int_diff_le _ L hF hFc _ _ t ht ((h1.1 ω).mono Set.Icc_subset_Ici_self)
      ((h2.1 ω).mono Set.Icc_subset_Ici_self)
