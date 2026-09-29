-- Prove2me | solution 1 for BertsekasDP.perturbed_terminal_cost_adjoint_limit
-- status  : ACCEPTED   (prove)
-- author  : @davidnet
-- created : 2026-09-07T22:32:30.483159+00:00
-- url     : https://prove2.me/submissions/3007f06b-1b49-4bcc-81a8-3dbedc7b5310

import Definitions.Def_BertsekasCTModel

open Set Filter MeasureTheory
open scoped Topology Interval

section Helpers

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A function continuous off a finite set and bounded there is interval integrable. -/
private lemma intervalIntegrable_of_continuousOn_diff_finset [CompleteSpace V]
    {a b : ℝ} (hab : a ≤ b) (φ : ℝ → V) (Fs : Finset ℝ)
    (hcont : ContinuousOn φ (Icc a b \ (Fs : Set ℝ)))
    {C : ℝ} (hbd : ∀ t ∈ Icc a b \ (Fs : Set ℝ), ‖φ t‖ ≤ C) :
    IntervalIntegrable φ volume a b := by
  have hmeas : MeasurableSet (Icc a b \ (Fs : Set ℝ)) :=
    measurableSet_Icc.diff (Fs.finite_toSet.measurableSet)
  have hae : (Icc a b \ (Fs : Set ℝ)) =ᵐ[volume] Icc a b := by
    refine diff_ae_eq_self.mpr ?_
    exact measure_mono_null inter_subset_right ((Fs.finite_toSet).measure_zero _)
  have hres : (volume : Measure ℝ).restrict (Icc a b \ (Fs : Set ℝ))
      = (volume : Measure ℝ).restrict (Icc a b) := Measure.restrict_congr_set hae
  have hint : IntegrableOn φ (Icc a b \ (Fs : Set ℝ)) volume := by
    have hfin : (volume : Measure ℝ) (Icc a b \ (Fs : Set ℝ)) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) (measure_mono diff_subset)
    refine Integrable.mono' (integrableOn_const (C := C) hfin)
      (hcont.aestronglyMeasurable hmeas) ?_
    filter_upwards [ae_restrict_mem hmeas] with t ht
    exact hbd t ht
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  rwa [IntegrableOn, hres] at hint

/-- A function continuous off a finite set is almost everywhere strongly measurable. -/
private lemma aestronglyMeasurable_of_continuousOn_diff_finset
    {a b : ℝ} (φ : ℝ → V) (Fs : Finset ℝ)
    (hcont : ContinuousOn φ (Icc a b \ (Fs : Set ℝ))) :
    AEStronglyMeasurable φ (volume.restrict (Icc a b)) := by
  have hmeas : MeasurableSet (Icc a b \ (Fs : Set ℝ)) :=
    measurableSet_Icc.diff (Fs.finite_toSet.measurableSet)
  have hae : (Icc a b \ (Fs : Set ℝ)) =ᵐ[volume] Icc a b := by
    refine diff_ae_eq_self.mpr ?_
    exact measure_mono_null inter_subset_right ((Fs.finite_toSet).measure_zero _)
  have hres : (volume : Measure ℝ).restrict (Icc a b \ (Fs : Set ℝ))
      = (volume : Measure ℝ).restrict (Icc a b) := Measure.restrict_congr_set hae
  have hm := hcont.aestronglyMeasurable (μ := (volume : Measure ℝ)) hmeas
  rwa [hres] at hm

/-- Fundamental theorem of calculus with a finite set of exceptional times. -/
private lemma sub_eq_integral_off_finset [CompleteSpace V] (Z Z' : ℝ → V) (Fs : Finset ℝ) :
    ∀ a b : ℝ, a ≤ b → ContinuousOn Z (Icc a b) →
      (∀ t ∈ Ioo a b \ (Fs : Set ℝ), HasDerivAt Z (Z' t) t) →
      IntervalIntegrable Z' volume a b →
      Z b - Z a = ∫ t in a..b, Z' t := by
  classical
  induction Fs using Finset.induction_on with
  | empty =>
    intro a b hab hcont hd hint
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
      (fun t ht => hd t ⟨ht, by simp⟩) hint).symm
  | @insert c Fs hcF ih =>
    intro a b hab hcont hd hint
    by_cases hci : c ∈ Ioo a b
    · have hac : a ≤ c := hci.1.le
      have hcb : c ≤ b := hci.2.le
      have hint1 : IntervalIntegrable Z' volume a c :=
        hint.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hac]; exact Icc_subset_Icc le_rfl hcb)
      have hint2 : IntervalIntegrable Z' volume c b :=
        hint.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hcb]; exact Icc_subset_Icc hac le_rfl)
      have h1 : Z c - Z a = ∫ t in a..c, Z' t := by
        refine ih a c hac (hcont.mono (Icc_subset_Icc le_rfl hcb)) ?_ hint1
        intro t ht
        refine hd t ⟨⟨ht.1.1, ht.1.2.trans hci.2⟩, ?_⟩
        simp only [Finset.coe_insert, mem_insert_iff, not_or]
        exact ⟨ne_of_lt ht.1.2, ht.2⟩
      have h2 : Z b - Z c = ∫ t in c..b, Z' t := by
        refine ih c b hcb (hcont.mono (Icc_subset_Icc hac le_rfl)) ?_ hint2
        intro t ht
        refine hd t ⟨⟨hci.1.trans ht.1.1, ht.1.2⟩, ?_⟩
        simp only [Finset.coe_insert, mem_insert_iff, not_or]
        exact ⟨ne_of_gt ht.1.1, ht.2⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, ← h1, ← h2]
      abel
    · refine ih a b hab hcont ?_ hint
      intro t ht
      refine hd t ⟨ht.1, ?_⟩
      have htc : t ≠ c := fun heq => hci (heq ▸ ht.1)
      simp only [Finset.coe_insert, mem_insert_iff, not_or]
      exact ⟨htc, ht.2⟩

/-- A jointly continuous integrand along a continuous state and a bounded measurable control
is interval integrable. -/
private lemma intervalIntegrable_comp_bounded [CompleteSpace V] {n m : ℕ} {a b : ℝ} (hab : a ≤ b)
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → V}
    (hG : Continuous (Function.uncurry G))
    {z : ℝ → EuclideanSpace ℝ (Fin n)} (hz : ContinuousOn z (Icc a b))
    {u : ℝ → EuclideanSpace ℝ (Fin m)}
    (hu : AEStronglyMeasurable u (volume.restrict (Icc a b)))
    {C : ℝ} (hC : ∀ s ∈ Icc a b, ‖u s‖ ≤ C) :
    IntervalIntegrable (fun s => G (z s) (u s)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hz
  have hK : IsCompact ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ×ˢ
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) C)) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  have hfin : (volume : Measure ℝ) (Icc a b) ≠ ⊤ := by simp
  refine (integrableOn_const (C := B) hfin).mono' ?_ ?_
  · exact hG.comp_aestronglyMeasurable ((hz.aestronglyMeasurable measurableSet_Icc).prodMk hu)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    refine hB (z s, u s) ⟨?_, ?_⟩ <;>
      simp only [Metric.mem_closedBall, dist_zero_right]
    · exact hR s hs
    · exact hC s hs

/-- An integrable operator path applied to a continuous path is interval integrable. -/
private lemma intervalIntegrable_clm_apply {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {a b : ℝ} (hab : a ≤ b)
    {B : ℝ → (X →L[ℝ] Y)} (hB : IntervalIntegrable B volume a b)
    {z : ℝ → X} (hz : ContinuousOn z (Icc a b)) :
    IntervalIntegrable (fun t => B t (z t)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hB ⊢
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hz
  apply (hB.norm.mul_const C).mono'
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hB.aestronglyMeasurable.prodMk (hz.aestronglyMeasurable measurableSet_Icc))
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (B t).le_opNorm (z t) |>.trans (mul_le_mul_of_nonneg_left (hC t ht) (norm_nonneg _))

/-- The inner product of a continuous path with an integrable path is interval integrable. -/
private lemma intervalIntegrable_inner_left {n : ℕ} {a b : ℝ} (hab : a ≤ b)
    {q : ℝ → EuclideanSpace ℝ (Fin n)} (hq : ContinuousOn q (Icc a b))
    {φ : ℝ → EuclideanSpace ℝ (Fin n)} (hφ : IntervalIntegrable φ volume a b) :
    IntervalIntegrable (fun t => (inner ℝ (q t) (φ t) : ℝ)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hφ ⊢
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  apply (hφ.norm.const_mul C).mono'
  · exact (continuous_inner (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))).comp_aestronglyMeasurable
      ((hq.aestronglyMeasurable measurableSet_Icc).prodMk hφ.aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    calc ‖(inner ℝ (q t) (φ t) : ℝ)‖ ≤ ‖q t‖ * ‖φ t‖ := norm_inner_le_norm _ _
      _ ≤ C * ‖φ t‖ := mul_le_mul_of_nonneg_right (hC t ht) (norm_nonneg _)

/-- Uniform first-order Taylor remainder on a compact set of base points. -/
private lemma uniform_remainder {X U Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [ProperSpace X] [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y]
    (G : X → U → Y) (Gx : X → U → (X →L[ℝ] Y))
    (hG : ∀ z ω, HasFDerivAt (fun ξ => G ξ ω) (Gx z ω) z)
    (hGx : Continuous (Function.uncurry Gx))
    {K : Set (X × U)} (hK : IsCompact K) :
    ∀ η > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ z ω, (z, ω) ∈ K → ∀ d : X, ‖d‖ ≤ δ →
      ‖G (z + d) ω - G z ω - Gx z ω d‖ ≤ η * ‖d‖ := by
  intro η hη
  let K₁ : Set (X × U) :=
    (fun q : (X × U) × X => (q.1.1 + q.2, q.1.2)) '' (K ×ˢ Metric.closedBall (0 : X) 1)
  have hK₁ : IsCompact K₁ := (hK.prod (isCompact_closedBall _ _)).image (by fun_prop)
  obtain ⟨δ, hδ, hδK⟩ := Metric.uniformContinuousOn_iff.mp
    (hK₁.uniformContinuousOn_of_continuous hGx.continuousOn) η hη
  refine ⟨min (δ / 2) 1, by positivity, ?_⟩
  intro z ω hzω d hd
  have hd1 : ‖d‖ ≤ 1 := hd.trans (min_le_right _ _)
  have hdδ : ‖d‖ < δ := lt_of_le_of_lt (hd.trans (min_le_left _ _)) (by linarith)
  have hmem : ∀ ξ ∈ Metric.closedBall z ‖d‖, (ξ, ω) ∈ K₁ := by
    intro ξ hξ
    rw [Metric.mem_closedBall, dist_eq_norm] at hξ
    refine ⟨((z, ω), ξ - z), ⟨hzω, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hξ.trans hd1
    · simp
  have hbound : ∀ ξ ∈ Metric.closedBall z ‖d‖, ‖Gx ξ ω - Gx z ω‖ ≤ η := by
    intro ξ hξ
    have hzK : (z, ω) ∈ K₁ := hmem z (Metric.mem_closedBall_self (norm_nonneg _))
    have hξz : dist (ξ, ω) (z, ω) < δ := by
      rw [Prod.dist_eq, dist_self, dist_eq_norm]
      rw [Metric.mem_closedBall, dist_eq_norm] at hξ
      exact max_lt (lt_of_le_of_lt hξ hdδ) hδ
    have := hδK (ξ, ω) (hmem ξ hξ) (z, ω) hzK hξz
    rw [dist_eq_norm] at this
    exact this.le
  have hz : z ∈ Metric.closedBall z ‖d‖ := Metric.mem_closedBall_self (norm_nonneg _)
  have hzd : z + d ∈ Metric.closedBall z ‖d‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := fun ξ => G ξ ω) (f' := fun ξ => Gx ξ ω) (φ := Gx z ω) (C := η)
    (s := Metric.closedBall z ‖d‖) (fun ξ _ => (hG ξ ω).hasFDerivWithinAt) hbound
    (convex_closedBall _ _) hz hzd
  simpa [add_sub_cancel_left] using this

/-- Grönwall estimate for two trajectories that stay in a tube of radius `r`. -/
private lemma gronwall_tube [CompleteSpace V]
    {a b : ℝ} (hab : a ≤ b) (X Y D : ℝ → V) (Fs : Finset ℝ)
    (hX : ContinuousOn X (Icc a b)) (hY : ContinuousOn Y (Icc a b))
    (hD : ∀ t ∈ Ioo a b \ (Fs : Set ℝ), HasDerivAt (fun s => Y s - X s) (D t) t)
    (hDint : IntervalIntegrable D volume a b)
    (L r : ℝ) (hL : 0 ≤ L) (hr : 0 < r)
    (hbound : ∀ t ∈ Ioo a b \ (Fs : Set ℝ), ‖Y t - X t‖ ≤ r → ‖D t‖ ≤ L * ‖Y t - X t‖)
    (h0 : ‖Y a - X a‖ * Real.exp (L * (b - a)) < r) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤ ‖Y a - X a‖ * Real.exp (L * (t - a)) := by
  classical
  set Δ : ℝ → V := fun s => Y s - X s with hΔ
  have hΔcont : ContinuousOn Δ (Icc a b) := hY.sub hX
  set pr : ℝ → ℝ := fun s => max a (min b s) with hpr
  have hprcont : Continuous pr := continuous_const.max (continuous_const.min continuous_id)
  have hprmem : ∀ s, pr s ∈ Icc a b := fun s =>
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hpreq : ∀ s ∈ Icc a b, pr s = s := by
    intro s hs
    simp only [hpr]
    rw [min_eq_right hs.2, max_eq_right hs.1]
  set ψ : ℝ → ℝ := fun s => ‖Δ (pr s)‖ with hψ
  have hψcont : Continuous ψ :=
    continuous_norm.comp (hΔcont.comp_continuous hprcont hprmem)
  have hψeq : ∀ s ∈ Icc a b, ψ s = ‖Δ s‖ := by
    intro s hs; simp only [hψ, hpreq s hs]
  set φ : ℝ → ℝ := fun s => L * ψ s with hφ
  have hφcont : Continuous φ := continuous_const.mul hψcont
  set W : ℝ → ℝ := fun t => ‖Δ a‖ + ∫ s in a..t, φ s with hW
  have hWderiv : ∀ t : ℝ, HasDerivAt W (φ t) t := by
    intro t
    simpa [hW] using
      ((intervalIntegral.integral_hasDerivAt_right (hφcont.intervalIntegrable a t)
        (hφcont.stronglyMeasurableAtFilter _ _) hφcont.continuousAt).const_add ‖Δ a‖)
  have hWcont : Continuous W :=
    continuous_iff_continuousAt.2 fun t => (hWderiv t).continuousAt
  have key : ∀ c ∈ Icc a b, (∀ s ∈ Icc a c, ‖Δ s‖ ≤ r) →
      ∀ t ∈ Icc a c, ‖Δ t‖ ≤ ‖Δ a‖ * Real.exp (L * (t - a)) := by
    intro c hc htube
    have hle : ∀ s ∈ Icc a c, ‖Δ s‖ ≤ W s := by
      intro s hs
      have hsb : s ≤ b := hs.2.trans hc.2
      have has : a ≤ s := hs.1
      have hFTC : Δ s - Δ a = ∫ σ in a..s, D σ :=
        sub_eq_integral_off_finset Δ D Fs a s has (hΔcont.mono (Icc_subset_Icc le_rfl hsb))
          (fun σ hσ => hD σ ⟨⟨hσ.1.1, hσ.1.2.trans_le hsb⟩, hσ.2⟩)
          (hDint.mono_set (by
            rw [uIcc_of_le hab, uIcc_of_le has]; exact Icc_subset_Icc le_rfl hsb))
      have hnorm : ‖∫ σ in a..s, D σ‖ ≤ ∫ σ in a..s, φ σ := by
        refine intervalIntegral.norm_integral_le_of_norm_le has ?_ (hφcont.intervalIntegrable a s)
        have hnullF : ∀ᵐ σ : ℝ, σ ∉ (Fs : Set ℝ) :=
          ae_iff.2 (by simpa using (Fs.finite_toSet).measure_zero (volume : Measure ℝ))
        have hnullb : ∀ᵐ σ : ℝ, σ ≠ b := by simp [ae_iff]
        filter_upwards [hnullF, hnullb] with σ hσF hσb hσmem
        have hσIcc : σ ∈ Icc a b := ⟨hσmem.1.le, hσmem.2.trans hsb⟩
        have hσab : σ ∈ Ioo a b \ (Fs : Set ℝ) :=
          ⟨⟨hσmem.1, lt_of_le_of_ne hσIcc.2 hσb⟩, hσF⟩
        have hσr : ‖Δ σ‖ ≤ r := htube σ ⟨hσmem.1.le, hσmem.2.trans hs.2⟩
        calc ‖D σ‖ ≤ L * ‖Δ σ‖ := hbound σ hσab hσr
          _ = φ σ := by simp only [hφ, hψeq σ hσIcc]
      have hstep : ‖Δ s‖ ≤ ‖Δ a‖ + ‖Δ s - Δ a‖ := by
        have := norm_add_le (Δ a) (Δ s - Δ a)
        simpa using this
      rw [hFTC] at hstep
      exact hstep.trans (by linarith [hnorm])
    intro t ht
    have hbnd : ∀ s ∈ Ico a c, ‖φ s‖ ≤ L * ‖W s‖ + 0 := by
      intro s hs
      have hsc : s ∈ Icc a c := ⟨hs.1, hs.2.le⟩
      have h1 : 0 ≤ ‖Δ s‖ := norm_nonneg _
      have h2 : ‖Δ s‖ ≤ W s := hle s hsc
      have h3 : φ s = L * ‖Δ s‖ := by
        simp only [hφ, hψeq s ⟨hsc.1, hsc.2.trans hc.2⟩]
      have h4 : 0 ≤ φ s := by rw [h3]; positivity
      have h5 : 0 ≤ W s := le_trans h1 h2
      rw [Real.norm_eq_abs, abs_of_nonneg h4, Real.norm_eq_abs, abs_of_nonneg h5, h3]
      nlinarith
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := W) (f' := φ)
      (δ := ‖Δ a‖) (K := L) (ε := 0) (a := a) (b := c)
      hWcont.continuousOn (fun s _ => (hWderiv s).hasDerivWithinAt)
      (by simp [hW]) hbnd t ht
    rw [gronwallBound_ε0] at hgr
    have h5 : 0 ≤ W t := le_trans (norm_nonneg _) (hle t ht)
    calc ‖Δ t‖ ≤ W t := hle t ht
      _ = ‖W t‖ := by rw [Real.norm_eq_abs, abs_of_nonneg h5]
      _ ≤ ‖Δ a‖ * Real.exp (L * (t - a)) := hgr
  have hexp1 : (1 : ℝ) ≤ Real.exp (L * (b - a)) :=
    Real.one_le_exp (by nlinarith [sub_nonneg.mpr hab])
  have htube_all : ∀ t ∈ Icc a b, ‖Δ t‖ ≤ r := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨t₀, ht₀mem, ht₀⟩ := hcon
    set S : Set ℝ := Icc a b ∩ {t | r ≤ ψ t} with hS
    have hSclosed : IsClosed S :=
      isClosed_Icc.inter (isClosed_le continuous_const hψcont)
    have hSne : S.Nonempty := ⟨t₀, ht₀mem, by
      simp only [mem_setOf_eq, hψeq t₀ ht₀mem]; exact ht₀.le⟩
    have hSbdd : BddBelow S := ⟨a, fun s hs => hs.1.1⟩
    set c := sInf S with hc
    have hcS : c ∈ S := hSclosed.csInf_mem hSne hSbdd
    have hcmem : c ∈ Icc a b := hcS.1
    have hcr : r ≤ ‖Δ c‖ := by
      have := hcS.2
      simp only [mem_setOf_eq, hψeq c hcmem] at this
      exact this
    have hac : a < c := by
      rcases eq_or_lt_of_le hcmem.1 with h | h
      · exfalso
        have h1 : ‖Δ a‖ ≤ ‖Δ a‖ * Real.exp (L * (b - a)) :=
          le_mul_of_one_le_right (norm_nonneg _) hexp1
        rw [← h] at hcr
        linarith
      · exact h
    have hlt : ∀ s ∈ Ico a c, ‖Δ s‖ < r := by
      intro s hs
      by_contra hcon2
      push_neg at hcon2
      have hsmem : s ∈ Icc a b := ⟨hs.1, hs.2.le.trans hcmem.2⟩
      have hmem : s ∈ S := ⟨hsmem, by simp only [mem_setOf_eq, hψeq s hsmem]; exact hcon2⟩
      have := csInf_le hSbdd hmem
      linarith [hs.2]
    have hcle : ‖Δ c‖ ≤ r := by
      have h2 : ∀ᶠ s in 𝓝[<] c, ψ s ≤ r := by
        filter_upwards [Ioo_mem_nhdsLT hac] with s hs
        rw [hψeq s ⟨hs.1.le, hs.2.le.trans hcmem.2⟩]
        exact (hlt s ⟨hs.1.le, hs.2⟩).le
      have h3 := le_of_tendsto (hψcont.continuousAt.continuousWithinAt.tendsto) h2
      rwa [hψeq c hcmem] at h3
    have hfin := key c hcmem (by
      intro s hs
      rcases eq_or_lt_of_le hs.2 with h | h
      · rw [h]; exact hcle
      · exact (hlt s ⟨hs.1, h⟩).le) c ⟨hcmem.1, le_rfl⟩
    have hmono : ‖Δ a‖ * Real.exp (L * (c - a)) ≤ ‖Δ a‖ * Real.exp (L * (b - a)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Real.exp_le_exp.mpr (by nlinarith [hcmem.2, sub_nonneg.mpr hcmem.1])
    linarith
  intro t ht
  exact key b ⟨hab, le_rfl⟩ htube_all t ht

end Helpers

theorem solution
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : ContDiff ℝ 1 (Function.uncurry M.f))
    (hg : ContDiff ℝ 1 (Function.uncurry M.g))
    (hh : ContDiff ℝ 1 M.h)
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (x p : ℝ → EuclideanSpace ℝ (Fin n))
    (hadm : BertsekasCTAdmissibleFrom M 0 M.x0 u x)
    (hp : ContinuousOn p (Set.Icc 0 M.T))
    (hterm : p M.T = gradient M.h (x M.T))
    (F : Finset ℝ)
    (hadj : ∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
      HasDerivAt p
        (-gradient (fun z => BertsekasHamiltonian M z (u t) (p t)) (x t)) t)
    (τ : ℝ) (hτ : τ ∈ Set.Ioo 0 M.T)
    (y : ℝ → ℝ → EuclideanSpace ℝ (Fin n))
    (hy : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ContinuousOn (y ε) (Set.Icc τ M.T) ∧
        ∃ G : Finset ℝ, ∀ t ∈ Set.Icc τ M.T \ (G : Set ℝ),
          HasDerivAt (y ε) (M.f (y ε t) (u t)) t)
    (w : EuclideanSpace ℝ (Fin n))
    (hlim : Tendsto (fun ε => ε⁻¹ • (y ε τ - x τ)) (𝓝[>] (0 : ℝ)) (𝓝 w)) :
    Tendsto
      (fun ε => ε⁻¹ * ((M.h (y ε M.T) + ∫ t in τ..M.T, M.g (y ε t) (u t)) -
        (M.h (x M.T) + ∫ t in τ..M.T, M.g (x t) (u t))))
      (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ (p τ) w)) := by
  classical
  obtain ⟨huU, ⟨hubdd, Fu, hucont⟩, hxcont, hx0eq, Fx, hxderiv⟩ := hadm
  have hτT : τ ≤ M.T := hτ.2.le
  have h0τ : (0 : ℝ) ≤ τ := hτ.1.le
  have hsub : Icc τ M.T ⊆ Icc (0 : ℝ) M.T := Icc_subset_Icc h0τ le_rfl
  have hxcont' : ContinuousOn x (Icc τ M.T) := hxcont.mono hsub
  have hpcont' : ContinuousOn p (Icc τ M.T) := hp.mono hsub
  -- bound and measurability of the control
  obtain ⟨cu0, hcu0⟩ := hubdd.subset_closedBall (0 : EuclideanSpace ℝ (Fin m))
  set cu : ℝ := max cu0 0 with hcudef
  have hcu : ∀ t ∈ Icc (0 : ℝ) M.T, ‖u t‖ ≤ cu := by
    intro t ht
    have hmem : u t ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) cu0 :=
      hcu0 (mem_image_of_mem u ht)
    rw [mem_closedBall_zero_iff] at hmem
    exact hmem.trans (le_max_left _ _)
  have hcu' : ∀ t ∈ Icc τ M.T, ‖u t‖ ≤ cu := fun t ht => hcu t (hsub ht)
  have humeas : AEStronglyMeasurable u (volume.restrict (Icc τ M.T)) :=
    aestronglyMeasurable_of_continuousOn_diff_finset u Fu
      (hucont.mono (fun s hs => ⟨hsub hs.1, hs.2⟩))
  -- bound on the state
  obtain ⟨rx0, hrx0⟩ := isCompact_Icc.exists_bound_of_continuousOn hxcont
  set rx : ℝ := max rx0 0 with hrxdef
  have hrx : ∀ t ∈ Icc (0 : ℝ) M.T, ‖x t‖ ≤ rx := fun t ht => (hrx0 t ht).trans (le_max_left _ _)
  set R : ℝ := rx + 1 with hRdef
  set Kset : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
    Metric.closedBall 0 R ×ˢ Metric.closedBall 0 cu with hKdef
  have hKcompact : IsCompact Kset :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hKconvex : Convex ℝ Kset := (convex_closedBall _ _).prod (convex_closedBall _ _)
  have hKmem : ∀ (z : EuclideanSpace ℝ (Fin n)) (ω : EuclideanSpace ℝ (Fin m)),
      ‖z‖ ≤ R → ‖ω‖ ≤ cu → (z, ω) ∈ Kset := by
    intro z ω hz hω
    refine ⟨?_, ?_⟩ <;> simp only [Metric.mem_closedBall, dist_zero_right]
    · exact hz
    · exact hω
  -- partial derivatives of the data
  set Ff : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := fun z ω =>
    (fderiv ℝ (Function.uncurry M.f) (z, ω)).comp
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) with hFfdef
  set Gg : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := fun z ω =>
    (fderiv ℝ (Function.uncurry M.g) (z, ω)).comp
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) with hGgdef
  have hFf : ∀ z ω, HasFDerivAt (fun ξ => M.f ξ ω) (Ff z ω) z := by
    intro z ω
    exact ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp z
      (hasFDerivAt_prodMk_left z ω)
  have hGgd : ∀ z ω, HasFDerivAt (fun ξ => M.g ξ ω) (Gg z ω) z := by
    intro z ω
    exact ((hg.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp z
      (hasFDerivAt_prodMk_left z ω)
  have hFfc : Continuous (Function.uncurry Ff) :=
    ((hf.continuous_fderiv (by norm_num)).comp continuous_id).clm_comp continuous_const
  have hGgc : Continuous (Function.uncurry Gg) :=
    ((hg.continuous_fderiv (by norm_num)).comp continuous_id).clm_comp continuous_const
  have hHd : ∀ (z : EuclideanSpace ℝ (Fin n)) (ω : EuclideanSpace ℝ (Fin m)),
      HasFDerivAt (fun ξ => M.h ξ) (fderiv ℝ M.h z) z :=
    fun z _ => (hh.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hHc : Continuous
      (Function.uncurry (fun (z : EuclideanSpace ℝ (Fin n))
        (_ : EuclideanSpace ℝ (Fin m)) => fderiv ℝ M.h z)) :=
    (hh.continuous_fderiv (by norm_num)).comp continuous_fst
  -- Lipschitz constant of the dynamics on the tube
  obtain ⟨Lf0, hLf0⟩ := hKcompact.exists_bound_of_continuousOn
    (hf.continuous_fderiv (by norm_num)).continuousOn
  set Lf : ℝ := max Lf0 0 with hLfdef
  have hLf : 0 ≤ Lf := le_max_right _ _
  have hLip : ∀ (z z' : EuclideanSpace ℝ (Fin n)) (ω : EuclideanSpace ℝ (Fin m)),
      (z, ω) ∈ Kset → (z', ω) ∈ Kset → ‖M.f z ω - M.f z' ω‖ ≤ Lf * ‖z - z'‖ := by
    intro z z' ω hz hz'
    have hbd : ∀ q ∈ Kset, ‖fderiv ℝ (Function.uncurry M.f) q‖ ≤ Lf :=
      fun q hq => (hLf0 q hq).trans (le_max_left _ _)
    have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := Function.uncurry M.f) (f' := fun q => fderiv ℝ (Function.uncurry M.f) q)
      (s := Kset) (C := Lf)
      (fun q _ => ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt).hasFDerivWithinAt)
      hbd hKconvex hz' hz
    simpa [Prod.norm_def, Function.uncurry] using this
  -- bound on the costate
  obtain ⟨Cp0, hCp0⟩ := isCompact_Icc.exists_bound_of_continuousOn hpcont'
  set Cp : ℝ := max Cp0 0 with hCpdef
  have hCp : ∀ t ∈ Icc τ M.T, ‖p t‖ ≤ Cp := fun t ht => (hCp0 t ht).trans (le_max_left _ _)
  have hCp0' : 0 ≤ Cp := le_max_right _ _
  -- the deviation is of order ε
  set Cd : ℝ := (‖w‖ + 1) * Real.exp (Lf * (M.T - τ)) with hCddef
  have hCd : 0 ≤ Cd := by positivity
  have hΔτ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖y ε τ - x τ‖ ≤ (‖w‖ + 1) * ε := by
    have h1 : Tendsto (fun ε => ‖ε⁻¹ • (y ε τ - x τ)‖) (𝓝[>] (0 : ℝ)) (𝓝 ‖w‖) := hlim.norm
    have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖ε⁻¹ • (y ε τ - x τ)‖ < ‖w‖ + 1 :=
      h1.eventually_lt_const (by linarith)
    filter_upwards [h2, self_mem_nhdsWithin] with ε hε hεp
    have hεpos : (0 : ℝ) < ε := hεp
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hεpos, inv_mul_eq_div,
      div_lt_iff₀ hεpos] at hε
    linarith
  have hCdtend : Tendsto (fun ε : ℝ => Cd * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Tendsto (fun ε : ℝ => Cd * ε) (𝓝 (0 : ℝ)) (𝓝 (Cd * 0)) :=
      (continuous_const.mul continuous_id).tendsto (0 : ℝ)
    rw [mul_zero] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  have hdev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc τ M.T, ‖y ε t - x t‖ ≤ Cd * ε := by
    have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Cd * ε < 1 := hCdtend.eventually_lt_const one_pos
    filter_upwards [hy, hΔτ, hsmall, self_mem_nhdsWithin] with ε hyε hΔ hs hεp
    obtain ⟨hycont, G, hyderiv⟩ := hyε
    have hεpos : (0 : ℝ) < ε := hεp
    have hDint : IntervalIntegrable
        (fun s => M.f (y ε s) (u s) - M.f (x s) (u s)) volume τ M.T :=
      (intervalIntegrable_comp_bounded hτT hf.continuous hycont humeas hcu').sub
        (intervalIntegrable_comp_bounded hτT hf.continuous hxcont' humeas hcu')
    have hgr := gronwall_tube hτT x (y ε) (fun s => M.f (y ε s) (u s) - M.f (x s) (u s))
      (Fx ∪ G) hxcont' hycont ?_ hDint Lf 1 hLf one_pos ?_ ?_
    · intro t ht
      have h1 := hgr t ht
      have h2 : Real.exp (Lf * (t - τ)) ≤ Real.exp (Lf * (M.T - τ)) :=
        Real.exp_le_exp.mpr (by nlinarith [ht.2, sub_nonneg.mpr ht.1])
      calc ‖y ε t - x t‖ ≤ ‖y ε τ - x τ‖ * Real.exp (Lf * (t - τ)) := h1
        _ ≤ ((‖w‖ + 1) * ε) * Real.exp (Lf * (M.T - τ)) := by
            apply mul_le_mul hΔ h2 (Real.exp_pos _).le
            positivity
        _ = Cd * ε := by rw [hCddef]; ring
    · intro t ht
      have htG : t ∈ Icc τ M.T \ (G : Set ℝ) := by
        refine ⟨⟨ht.1.1.le, ht.1.2.le⟩, ?_⟩
        intro hc
        exact ht.2 (by simp [hc])
      have htF : t ∈ Icc (0 : ℝ) M.T \ (Fx : Set ℝ) := by
        refine ⟨⟨h0τ.trans ht.1.1.le, ht.1.2.le⟩, ?_⟩
        intro hc
        exact ht.2 (by simp [hc])
      exact (hyderiv t htG).sub (hxderiv t htF)
    · intro t ht hle
      have htIcc : t ∈ Icc τ M.T := ⟨ht.1.1.le, ht.1.2.le⟩
      have h1 : ‖x t‖ ≤ rx := hrx t (hsub htIcc)
      have h2 : ‖y ε t‖ ≤ R := by
        have : ‖y ε t‖ ≤ ‖x t‖ + ‖y ε t - x t‖ := by
          simpa using norm_add_le (x t) (y ε t - x t)
        rw [hRdef]
        linarith
      exact hLip _ _ _ (hKmem _ _ h2 (hcu' t htIcc)) (hKmem _ _ (h1.trans (by simp [hRdef])) (hcu' t htIcc))
    · have h1 : ‖y ε τ - x τ‖ * Real.exp (Lf * (M.T - τ)) ≤ Cd * ε := by
        rw [hCddef]
        have := mul_le_mul_of_nonneg_right hΔ (Real.exp_pos (Lf * (M.T - τ))).le
        linarith [this]
      linarith
  set Rem : ℝ → ℝ := fun ε =>
    (M.h (y ε M.T) - M.h (x M.T) - (inner ℝ (p M.T) (y ε M.T - x M.T) : ℝ)) +
      ∫ s in τ..M.T,
        ((inner ℝ (p s) (M.f (y ε s) (u s) - M.f (x s) (u s) -
            Ff (x s) (u s) (y ε s - x s)) : ℝ) +
          (M.g (y ε s) (u s) - M.g (x s) (u s) - Gg (x s) (u s) (y ε s - x s))) with hRem
  -- the exact first-order identity for each small ε
  have hident : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ((M.h (y ε M.T) + ∫ t in τ..M.T, M.g (y ε t) (u t)) -
        (M.h (x M.T) + ∫ t in τ..M.T, M.g (x t) (u t)))
        = (inner ℝ (p τ) (y ε τ - x τ) : ℝ) + Rem ε := by
    filter_upwards [hy] with ε hyε
    simp only [hRem]
    obtain ⟨hycont, G, hyderiv⟩ := hyε
    have hΔcont : ContinuousOn (fun s => y ε s - x s) (Icc τ M.T) := hycont.sub hxcont'
    have hIy : IntervalIntegrable (fun s => M.g (y ε s) (u s)) volume τ M.T :=
      intervalIntegrable_comp_bounded hτT hg.continuous hycont humeas hcu'
    have hIx : IntervalIntegrable (fun s => M.g (x s) (u s)) volume τ M.T :=
      intervalIntegrable_comp_bounded hτT hg.continuous hxcont' humeas hcu'
    have hIGg : IntervalIntegrable (fun s => Gg (x s) (u s) (y ε s - x s)) volume τ M.T :=
      intervalIntegrable_clm_apply hτT
        (intervalIntegrable_comp_bounded hτT hGgc hxcont' humeas hcu') hΔcont
    have hIFf : IntervalIntegrable (fun s => Ff (x s) (u s) (y ε s - x s)) volume τ M.T :=
      intervalIntegrable_clm_apply hτT
        (intervalIntegrable_comp_bounded hτT hFfc hxcont' humeas hcu') hΔcont
    have hIfy : IntervalIntegrable (fun s => M.f (y ε s) (u s)) volume τ M.T :=
      intervalIntegrable_comp_bounded hτT hf.continuous hycont humeas hcu'
    have hIfx : IntervalIntegrable (fun s => M.f (x s) (u s)) volume τ M.T :=
      intervalIntegrable_comp_bounded hτT hf.continuous hxcont' humeas hcu'
    have hIRf : IntervalIntegrable (fun s => M.f (y ε s) (u s) - M.f (x s) (u s) -
        Ff (x s) (u s) (y ε s - x s)) volume τ M.T := (hIfy.sub hIfx).sub hIFf
    have hIpRf : IntervalIntegrable (fun s => (inner ℝ (p s)
        (M.f (y ε s) (u s) - M.f (x s) (u s) - Ff (x s) (u s) (y ε s - x s)) : ℝ))
        volume τ M.T := intervalIntegrable_inner_left hτT hpcont' hIRf
    have hIRg : IntervalIntegrable (fun s => M.g (y ε s) (u s) - M.g (x s) (u s) -
        Gg (x s) (u s) (y ε s - x s)) volume τ M.T := (hIy.sub hIx).sub hIGg
    have hpair : (inner ℝ (p M.T) (y ε M.T - x M.T) : ℝ) - (inner ℝ (p τ) (y ε τ - x τ) : ℝ)
        = ∫ s in τ..M.T, ((inner ℝ (p s) (M.f (y ε s) (u s) - M.f (x s) (u s) -
            Ff (x s) (u s) (y ε s - x s)) : ℝ) - Gg (x s) (u s) (y ε s - x s)) := by
      refine sub_eq_integral_off_finset _ _ (F ∪ Fx ∪ G) τ M.T hτT
        (hpcont'.inner hΔcont) ?_ (hIpRf.sub hIGg)
      intro s hs
      have hsIcc : s ∈ Icc τ M.T := ⟨hs.1.1.le, hs.1.2.le⟩
      have hnotF : s ∉ (F : Set ℝ) := fun hc => hs.2 (by simp [hc])
      have hnotFx : s ∉ (Fx : Set ℝ) := fun hc => hs.2 (by simp [hc])
      have hnotG : s ∉ (G : Set ℝ) := fun hc => hs.2 (by simp [hc])
      have hd1 := hadj s ⟨hsub hsIcc, hnotF⟩
      have hd2 : HasDerivAt (fun σ => y ε σ - x σ)
          (M.f (y ε s) (u s) - M.f (x s) (u s)) s :=
        (hyderiv s ⟨hsIcc, hnotG⟩).sub (hxderiv s ⟨hsub hsIcc, hnotFx⟩)
      have hinner := hd1.inner ℝ hd2
      have hψ : HasFDerivAt (fun z => BertsekasHamiltonian M z (u s) (p s))
          (Gg (x s) (u s) + (innerSL ℝ (p s)).comp (Ff (x s) (u s))) (x s) := by
        have h1 : HasFDerivAt (fun ξ => M.g ξ (u s)) (Gg (x s) (u s)) (x s) := hGgd (x s) (u s)
        have h2 : HasFDerivAt (fun ξ => (inner ℝ (p s) (M.f ξ (u s)) : ℝ))
            ((innerSL ℝ (p s)).comp (Ff (x s) (u s))) (x s) :=
          (innerSL ℝ (p s)).hasFDerivAt.comp (x s) (hFf (x s) (u s))
        simp only [BertsekasHamiltonian]
        exact h1.add h2
      have hgrad : (inner ℝ (gradient (fun z => BertsekasHamiltonian M z (u s) (p s)) (x s))
            (y ε s - x s) : ℝ)
          = Gg (x s) (u s) (y ε s - x s) +
            (inner ℝ (p s) (Ff (x s) (u s) (y ε s - x s)) : ℝ) := by
        rw [inner_gradient_left, hψ.fderiv]
        simp
      have heq : (inner ℝ (p s) (M.f (y ε s) (u s) - M.f (x s) (u s) -
            Ff (x s) (u s) (y ε s - x s)) : ℝ) - Gg (x s) (u s) (y ε s - x s)
          = (inner ℝ (p s) (M.f (y ε s) (u s) - M.f (x s) (u s)) : ℝ) +
            (inner ℝ (-gradient (fun z => BertsekasHamiltonian M z (u s) (p s)) (x s))
              (y ε s - x s) : ℝ) := by
        rw [inner_neg_left, hgrad, inner_sub_right]
        ring
      rw [← heq] at hinner
      exact hinner
    have hA : (∫ t in τ..M.T, M.g (y ε t) (u t)) - ∫ t in τ..M.T, M.g (x t) (u t)
        = (∫ s in τ..M.T, Gg (x s) (u s) (y ε s - x s)) +
          ∫ s in τ..M.T,
            (M.g (y ε s) (u s) - M.g (x s) (u s) - Gg (x s) (u s) (y ε s - x s)) := by
      rw [← intervalIntegral.integral_add hIGg hIRg, ← intervalIntegral.integral_sub hIy hIx]
      refine intervalIntegral.integral_congr ?_
      intro s _
      ring
    rw [intervalIntegral.integral_add hIpRf hIRg]
    rw [intervalIntegral.integral_sub hIpRf hIGg] at hpair
    linarith [hA, hpair]
  -- the remainder term is o(ε)
  have hzero : Tendsto (fun ε => ε⁻¹ * Rem ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro η hη
    have hTτ : 0 ≤ M.T - τ := by linarith
    set B : ℝ := 1 + (Cp + 1) * (M.T - τ) with hBdef
    have hB : 0 ≤ B := by rw [hBdef]; nlinarith
    set η' : ℝ := η / (Cd * B + 1) with hη'def
    have hden : 0 < Cd * B + 1 := by nlinarith
    have hη' : 0 < η' := by rw [hη'def]; positivity
    obtain ⟨δf, hδf, hδfb⟩ := uniform_remainder M.f Ff hFf hFfc hKcompact η' hη'
    obtain ⟨δg, hδg, hδgb⟩ := uniform_remainder M.g Gg hGgd hGgc hKcompact η' hη'
    obtain ⟨δh, hδh, hδhb⟩ := uniform_remainder
      (fun (z : EuclideanSpace ℝ (Fin n)) (_ : EuclideanSpace ℝ (Fin m)) => M.h z)
      (fun z _ => fderiv ℝ M.h z) hHd hHc hKcompact η' hη'
    have hδpos : 0 < min δf (min δg δh) := by positivity
    have hεsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Cd * ε ≤ min δf (min δg δh) :=
      (hCdtend.eventually_lt_const hδpos).mono fun ε hε => hε.le
    filter_upwards [hdev, hεsmall, self_mem_nhdsWithin] with ε hd hsm hεp
    have hεpos : (0 : ℝ) < ε := hεp
    have hCdε : 0 ≤ Cd * ε := by positivity
    have hxK : ∀ s ∈ Icc τ M.T, (x s, u s) ∈ Kset := by
      intro s hs
      refine hKmem _ _ ?_ (hcu' s hs)
      have := hrx s (hsub hs)
      rw [hRdef]; linarith
    have hRfb : ∀ s ∈ Icc τ M.T,
        ‖M.f (y ε s) (u s) - M.f (x s) (u s) - Ff (x s) (u s) (y ε s - x s)‖
          ≤ η' * (Cd * ε) := by
      intro s hs
      have h1 : ‖y ε s - x s‖ ≤ Cd * ε := hd s hs
      have h3 := hδfb (x s) (u s) (hxK s hs) (y ε s - x s)
        (h1.trans (hsm.trans (min_le_left _ _)))
      have hxy : x s + (y ε s - x s) = y ε s := by abel
      rw [hxy] at h3
      exact h3.trans (mul_le_mul_of_nonneg_left h1 hη'.le)
    have hRgb : ∀ s ∈ Icc τ M.T,
        ‖M.g (y ε s) (u s) - M.g (x s) (u s) - Gg (x s) (u s) (y ε s - x s)‖
          ≤ η' * (Cd * ε) := by
      intro s hs
      have h1 : ‖y ε s - x s‖ ≤ Cd * ε := hd s hs
      have h3 := hδgb (x s) (u s) (hxK s hs) (y ε s - x s)
        (h1.trans (hsm.trans ((min_le_right _ _).trans (min_le_left _ _))))
      have hxy : x s + (y ε s - x s) = y ε s := by abel
      rw [hxy] at h3
      exact h3.trans (mul_le_mul_of_nonneg_left h1 hη'.le)
    have hTmem : M.T ∈ Icc τ M.T := ⟨hτT, le_rfl⟩
    have hRhb : ‖M.h (y ε M.T) - M.h (x M.T) - (inner ℝ (p M.T) (y ε M.T - x M.T) : ℝ)‖
        ≤ η' * (Cd * ε) := by
      have h1 : ‖y ε M.T - x M.T‖ ≤ Cd * ε := hd M.T hTmem
      have h3 := hδhb (x M.T) (u M.T) (hxK M.T hTmem) (y ε M.T - x M.T)
        (h1.trans (hsm.trans ((min_le_right _ _).trans (min_le_right _ _))))
      have hxy : x M.T + (y ε M.T - x M.T) = y ε M.T := by abel
      rw [hxy] at h3
      have hinnerh : (inner ℝ (p M.T) (y ε M.T - x M.T) : ℝ)
          = fderiv ℝ M.h (x M.T) (y ε M.T - x M.T) := by
        rw [hterm, inner_gradient_left]
      rw [hinnerh]
      exact h3.trans (mul_le_mul_of_nonneg_left h1 hη'.le)
    have hIb : ‖∫ s in τ..M.T,
        ((inner ℝ (p s) (M.f (y ε s) (u s) - M.f (x s) (u s) -
            Ff (x s) (u s) (y ε s - x s)) : ℝ) +
          (M.g (y ε s) (u s) - M.g (x s) (u s) - Gg (x s) (u s) (y ε s - x s)))‖
        ≤ ((Cp + 1) * (η' * (Cd * ε))) * |M.T - τ| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro s hs
      rw [uIoc_of_le hτT] at hs
      have hsIcc : s ∈ Icc τ M.T := ⟨hs.1.le, hs.2⟩
      have h1 : ‖(inner ℝ (p s) (M.f (y ε s) (u s) - M.f (x s) (u s) -
          Ff (x s) (u s) (y ε s - x s)) : ℝ)‖ ≤ Cp * (η' * (Cd * ε)) := by
        refine (norm_inner_le_norm _ _).trans ?_
        exact mul_le_mul (hCp s hsIcc) (hRfb s hsIcc) (norm_nonneg _) hCp0'
      have h2 := hRgb s hsIcc
      exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq (by ring)))
    have habs : |M.T - τ| = M.T - τ := abs_of_nonneg hTτ
    rw [habs] at hIb
    have hsum : ‖Rem ε‖ ≤ η' * (Cd * ε) * B := by
      simp only [hRem, hBdef]
      exact (norm_add_le _ _).trans ((add_le_add hRhb hIb).trans (le_of_eq (by ring)))
    have hfin : ε⁻¹ * ‖Rem ε‖ ≤ η' * Cd * B := by
      have h1 : ε⁻¹ * (η' * (Cd * ε) * B) = η' * Cd * B := by
        field_simp
      calc ε⁻¹ * ‖Rem ε‖ ≤ ε⁻¹ * (η' * (Cd * ε) * B) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = η' * Cd * B := h1
    have hCdB : 0 ≤ Cd * B := mul_nonneg hCd hB
    have hstep : η' * (Cd * B) < η' * (Cd * B + 1) :=
      mul_lt_mul_of_pos_left (by linarith) hη'
    have heqη : η' * (Cd * B + 1) = η := by
      rw [hη'def]
      field_simp
    have hlast : η' * Cd * B < η := by
      have hassoc : η' * Cd * B = η' * (Cd * B) := by ring
      rw [hassoc]
      linarith
    have habs2 : ‖ε⁻¹ * Rem ε‖ = ε⁻¹ * ‖Rem ε‖ := by
      rw [norm_mul, norm_inv]
      congr 1
      rw [Real.norm_eq_abs, abs_of_pos hεpos]
    rw [habs2]
    exact lt_of_le_of_lt hfin hlast
  -- assemble
  have hmain : Tendsto (fun ε => (inner ℝ (p τ) (ε⁻¹ • (y ε τ - x τ)) : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ (p τ) w)) := tendsto_const_nhds.inner hlim
  have hsum2 := hmain.add hzero
  rw [add_zero] at hsum2
  refine Tendsto.congr' ?_ hsum2
  filter_upwards [hident] with ε heq
  rw [heq, real_inner_smul_right]
  ring
