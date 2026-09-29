-- Prove2me | solution 1 for BertsekasDP.piecewise_trajectory_continuation
-- status  : ACCEPTED   (prove)
-- author  : @davidnet
-- created : 2026-09-07T23:07:58.98196+00:00
-- url     : https://prove2.me/submissions/8db864c0-a221-4ed7-a564-11bacbd85851

import Definitions.Def_BertsekasCTModel

open Set Filter MeasureTheory Metric
open scoped Topology Interval

section Helpers

/-- A function continuous off a finite set and with bounded image is interval integrable. -/
private lemma integrable_of_bounded_continuous_off_finset
    {E : Type*} [NormedAddCommGroup E] {a b : ℝ} (hab : a ≤ b)
    (v : ℝ → E) (F : Finset ℝ)
    (hv : ContinuousOn v (Icc a b \ (F : Set ℝ)))
    (hbdd : Bornology.IsBounded (v '' Icc a b)) :
    IntervalIntegrable v volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hm : AEStronglyMeasurable v (volume.restrict (Icc a b)) := by
    have h := hv.aestronglyMeasurable (μ := volume)
      (measurableSet_Icc.diff F.finite_toSet.measurableSet)
    rwa [Measure.restrict_congr_set (sdiff_null_ae_eq_self (F.finite_toSet.measure_zero volume))]
      at h
  obtain ⟨C, hC⟩ := hbdd.exists_norm_le
  apply (integrable_const C).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC (v t) (mem_image_of_mem v ht)

/-- A jointly continuous field evaluated along a continuous state and a piecewise continuous
control is interval integrable. -/
private lemma continuous_comp_piecewise_integrable
    {n m : ℕ} {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (hab : a ≤ b)
    (x : ℝ → EuclideanSpace ℝ (Fin n))
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (hx : ContinuousOn x (Icc a b))
    (hu : BertsekasPiecewiseContinuousOn u (Icc a b))
    (φ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → E)
    (hφ : Continuous φ) :
    IntervalIntegrable (fun t => φ (x t, u t)) volume a b := by
  obtain ⟨hbu, F, hcu⟩ := hu
  apply integrable_of_bounded_continuous_off_finset hab _ F
  · exact hφ.comp_continuousOn ((hx.mono sdiff_subset).prodMk hcu)
  · have hK := (isCompact_Icc.image_of_continuousOn hx).prod hbu.isCompact_closure
    apply (hK.image hφ).isBounded.subset
    rintro z ⟨t, ht, rfl⟩
    exact mem_image_of_mem φ ⟨mem_image_of_mem x ht, subset_closure (mem_image_of_mem u ht)⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

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

/-- The Bielecki weight estimate behind the Carathéodory contraction. -/
private lemma exp_weight_half {K a t : ℝ} (hK : 0 < K) :
    K * (Real.exp (-(2 * K * t)) * (∫ s in a..t, Real.exp (2 * K * s))) ≤ 1 / 2 := by
  have h2K : (0 : ℝ) < 2 * K := by linarith
  have hint : (∫ s in a..t, Real.exp (2 * K * s))
      = (Real.exp (2 * K * t) - Real.exp (2 * K * a)) / (2 * K) := by
    rw [intervalIntegral.integral_comp_mul_left Real.exp h2K.ne', integral_exp]
    simp only [smul_eq_mul]
    field_simp
  rw [hint]
  have hx : Real.exp (-(2 * K * t)) * Real.exp (2 * K * t) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-(2 * K * t)) * Real.exp (2 * K * a) := by positivity
  have hgoal : K * (Real.exp (-(2 * K * t)) *
      ((Real.exp (2 * K * t) - Real.exp (2 * K * a)) / (2 * K)))
      = (Real.exp (-(2 * K * t)) * Real.exp (2 * K * t) -
          Real.exp (-(2 * K * t)) * Real.exp (2 * K * a)) / 2 := by
    field_simp
  rw [hgoal, hx]
  linarith

/-- Carathéodory existence on a compact interval for a field that is globally Lipschitz in the
state, with only integrability in time.  The solution is produced as the fixed point of the
Picard operator in a Bielecki-weighted sup norm. -/
private lemma caratheodory_forward_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a < b) (G : ℝ → E → E) (K : ℝ) (hK : 0 < K)
    (hlip : ∀ t ∈ Icc a b, ∀ y w : E, ‖G t y - G t w‖ ≤ K * ‖y - w‖)
    (hint : ∀ y : ℝ → E, ContinuousOn y (Icc a b) →
      IntervalIntegrable (fun s => G s (y s)) volume a b)
    (ξ : E) :
    ∃ z : ℝ → E, ContinuousOn z (Icc a b) ∧
      ∀ t ∈ Icc a b, z t = ξ + ∫ s in a..t, G s (z s) := by
  have hexpc : Continuous fun t : ℝ => Real.exp (2 * K * t) := by fun_prop
  have hexpc' : Continuous fun t : ℝ => Real.exp (-(2 * K * t)) := by fun_prop
  let U : C(Icc a b, E) → ℝ → E := fun y t => Real.exp (2 * K * t) • IccExtend hab.le y t
  have hU : ∀ y, Continuous (U y) := fun y => hexpc.smul y.continuous.Icc_extend'
  have hInt : ∀ y, IntervalIntegrable (fun s => G s (U y s)) volume a b :=
    fun y => hint _ (hU y).continuousOn
  have hPrim : ∀ y, ContinuousOn (fun t => ∫ s in a..t, G s (U y s)) (Icc a b) := by
    intro y
    have hi : IntegrableOn (fun s => G s (U y s)) (uIcc a b) volume := by
      rw [uIcc_of_le hab.le]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp (hInt y)
    simpa [uIcc_of_le hab.le] using intervalIntegral.continuousOn_primitive_interval hi
  let Φ : C(Icc a b, E) → C(Icc a b, E) := fun y =>
    ⟨fun t => Real.exp (-(2 * K * (t : ℝ))) • (ξ + ∫ s in a..(t : ℝ), G s (U y s)),
      (hexpc'.continuousOn.smul (continuousOn_const.add (hPrim y))).domRestrict⟩
  have hΦ : ContractingWith (1 / 2) Φ := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro y w
    apply (ContinuousMap.dist_le (by positivity)).mpr
    intro t
    have ht : (t : ℝ) ∈ Icc a b := t.property
    have hwint : IntervalIntegrable (fun s => Real.exp (2 * K * s)) volume a (t : ℝ) :=
      hexpc.intervalIntegrable a t
    have hsub : uIcc a (t : ℝ) ⊆ uIcc a b := by
      rw [uIcc_of_le hab.le, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
    have hbound : ‖∫ s in a..(t : ℝ), (G s (U y s) - G s (U w s))‖ ≤
        (∫ s in a..(t : ℝ), K * Real.exp (2 * K * s)) * dist y w := by
      rw [← intervalIntegral.integral_mul_const]
      refine intervalIntegral.norm_integral_le_of_norm_le ht.1
        (Filter.Eventually.of_forall fun s hs => ?_) ((hwint.const_mul K).mul_const _)
      have hsIcc : s ∈ Icc a b := ⟨hs.1.le, hs.2.trans ht.2⟩
      have h2 : ‖U y s - U w s‖ ≤ Real.exp (2 * K * s) * dist y w := by
        have hUs : U y s - U w s = Real.exp (2 * K * s) •
            (IccExtend hab.le y s - IccExtend hab.le w s) := by
          simp only [U, smul_sub]
        rw [hUs, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have hd : ‖IccExtend hab.le y s - IccExtend hab.le w s‖ ≤ dist y w := by
          show ‖y (projIcc a b hab.le s) - w (projIcc a b hab.le s)‖ ≤ dist y w
          rw [← dist_eq_norm]
          exact ContinuousMap.dist_apply_le_dist _
        exact mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le
      calc ‖G s (U y s) - G s (U w s)‖ ≤ K * ‖U y s - U w s‖ := hlip s hsIcc _ _
        _ ≤ K * (Real.exp (2 * K * s) * dist y w) := mul_le_mul_of_nonneg_left h2 hK.le
        _ = K * Real.exp (2 * K * s) * dist y w := by ring
    change dist (Real.exp (-(2 * K * (t : ℝ))) • (ξ + ∫ s in a..(t : ℝ), G s (U y s)))
      (Real.exp (-(2 * K * (t : ℝ))) • (ξ + ∫ s in a..(t : ℝ), G s (U w s))) ≤ _
    rw [dist_eq_norm, ← smul_sub, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub ((hInt y).mono_set hsub) ((hInt w).mono_set hsub),
      norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(2 * K * (t : ℝ))) * ‖∫ s in a..(t : ℝ), (G s (U y s) - G s (U w s))‖
        ≤ Real.exp (-(2 * K * (t : ℝ))) *
            ((∫ s in a..(t : ℝ), K * Real.exp (2 * K * s)) * dist y w) :=
          mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
      _ = (K * (Real.exp (-(2 * K * (t : ℝ))) *
            (∫ s in a..(t : ℝ), Real.exp (2 * K * s)))) * dist y w := by
          rw [intervalIntegral.integral_const_mul]; ring
      _ ≤ (1 / 2 : ℝ) * dist y w := mul_le_mul_of_nonneg_right (exp_weight_half hK) dist_nonneg
      _ = _ := by norm_num
  let y := hΦ.fixedPoint Φ
  have hy : Φ y = y := hΦ.fixedPoint_isFixedPt
  refine ⟨U y, (hU y).continuousOn, ?_⟩
  intro t ht
  have hyt := congrArg (fun c : C(Icc a b, E) => c ⟨t, ht⟩) hy
  change Real.exp (-(2 * K * t)) • (ξ + ∫ s in a..t, G s (U y s)) = y ⟨t, ht⟩ at hyt
  dsimp only [U]
  rw [IccExtend_of_mem hab.le y ht, ← hyt, smul_smul]
  have hexp : Real.exp (2 * K * t) * Real.exp (-(2 * K * t)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [hexp, one_smul]

end Helpers

theorem solution
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : ContDiff ℝ 1 (Function.uncurry M.f))
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hadm : BertsekasCTAdmissibleFrom M 0 M.x0 u x)
    (τ : ℝ) (hτ : τ ∈ Set.Ioo 0 M.T) :
    ∃ δ > (0 : ℝ), ∀ ξ : EuclideanSpace ℝ (Fin n),
      ‖ξ - x τ‖ < δ →
      ∃ z : ℝ → EuclideanSpace ℝ (Fin n),
        BertsekasCTAdmissibleFrom M τ ξ u z := by
  classical
  obtain ⟨hUmem, hupc, hxc, -, Fx, hxd⟩ := hadm
  obtain ⟨hubdd, Fu, huc⟩ := hupc
  have hτT : τ < M.T := hτ.2
  have hsub : Icc τ M.T ⊆ Icc 0 M.T := Icc_subset_Icc hτ.1.le le_rfl
  have hxc' : ContinuousOn x (Icc τ M.T) := hxc.mono hsub
  -- a radius containing the reference trajectory
  obtain ⟨ρ0, hρ0⟩ := isCompact_Icc.exists_bound_of_continuousOn hxc'
  set ρ : ℝ := max ρ0 0 with hρdef
  have hρnn : (0 : ℝ) ≤ ρ := le_max_right _ _
  have hρ : ∀ t ∈ Icc τ M.T, ‖x t‖ ≤ ρ := fun t ht => (hρ0 t ht).trans (le_max_left _ _)
  -- a smooth cutoff equal to one on the tube and vanishing outside a compact ball
  let bump : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨ρ + 1, ρ + 2, by linarith, by linarith⟩
  have hbump1 : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ ≤ ρ + 1 → bump y = 1 := by
    intro y hy
    exact bump.one_of_mem_closedBall (by simpa [mem_closedBall, dist_zero_right] using hy)
  have hbump0 : ∀ y : EuclideanSpace ℝ (Fin n), ρ + 2 ≤ ‖y‖ → bump y = 0 := by
    intro y hy
    exact bump.zero_of_le_dist (by simpa [dist_zero_right] using hy)
  have hbumpC : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin n) => bump y) :=
    ContDiff.contDiffBump (f := fun _ => bump) contDiff_const contDiff_const contDiff_const
      contDiff_id
  -- the truncated field
  set Ff : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) :=
    fun z => bump z.1 • M.f z.1 z.2 with hFfdef
  have hFfC : ContDiff ℝ 1 Ff := (hbumpC.comp contDiff_fst).smul hf
  have hFfcont : Continuous Ff := hFfC.continuous
  set Dd : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := fun z =>
    (fderiv ℝ Ff z).comp
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) with hDddef
  have hDdcont : Continuous Dd :=
    (hFfC.continuous_fderiv one_ne_zero).clm_comp continuous_const
  have hDdderiv : ∀ (y : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin m)),
      HasFDerivAt (fun q => Ff (q, v)) (Dd (y, v)) y := by
    intro y v
    have hpair : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin n) => (q, v))
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) y := by
      convert (hasFDerivAt_id y).prodMk (hasFDerivAt_const v y) using 1 <;> rfl
    simpa [hDddef, Function.comp_def] using
      ((hFfC.differentiable one_ne_zero (y, v)).hasFDerivAt).comp y hpair
  -- the compact set of relevant control values
  have hubdd' : Bornology.IsBounded (u '' Icc τ M.T) := hubdd.subset (image_mono hsub)
  set Cu : Set (EuclideanSpace ℝ (Fin m)) := closure (u '' Icc τ M.T) with hCudef
  have hCu : IsCompact Cu := hubdd'.isCompact_closure
  have huCu : ∀ t ∈ Icc τ M.T, u t ∈ Cu := fun t ht => subset_closure (mem_image_of_mem u ht)
  -- a uniform Lipschitz constant for the truncated field
  have hSc : IsCompact ((closedBall (0 : EuclideanSpace ℝ (Fin n)) (ρ + 2)) ×ˢ Cu) :=
    (isCompact_closedBall _ _).prod hCu
  obtain ⟨K0, hK0⟩ := hSc.exists_bound_of_continuousOn hDdcont.continuousOn
  set K : ℝ := max K0 1 with hKdef
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hDdbound : ∀ y : EuclideanSpace ℝ (Fin n), ∀ v ∈ Cu, ‖Dd (y, v)‖ ≤ K := by
    intro y v hv
    by_cases hy : ‖y‖ ≤ ρ + 2
    · exact (hK0 (y, v) ⟨by simpa [mem_closedBall, dist_zero_right] using hy, hv⟩).trans
        (le_max_left _ _)
    · push_neg at hy
      have hzero : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin n) => Ff (q, v))
          (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) y := by
        have heq : (fun q : EuclideanSpace ℝ (Fin n) => Ff (q, v)) =ᶠ[𝓝 y]
            fun _ => (0 : EuclideanSpace ℝ (Fin n)) := by
          filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with q hq
          simp [hFfdef, hbump0 q (le_of_lt hq)]
        exact (hasFDerivAt_const (0 : EuclideanSpace ℝ (Fin n)) y).congr_of_eventuallyEq heq
      rw [(hDdderiv y v).unique hzero]
      simpa using hK.le
  have hlipF : ∀ v ∈ Cu, ∀ y w : EuclideanSpace ℝ (Fin n),
      ‖Ff (y, v) - Ff (w, v)‖ ≤ K * ‖y - w‖ := by
    intro v hv y w
    exact convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun q => Ff (q, v)) (f' := fun q => Dd (q, v))
      (fun q _ => (hDdderiv q v).hasFDerivWithinAt)
      (fun q _ => hDdbound q v hv) (mem_univ w) (mem_univ y)
  -- restricted piecewise continuity of the control
  have hupc' : BertsekasPiecewiseContinuousOn u (Icc τ M.T) :=
    ⟨hubdd', Fu, huc.mono (diff_subset_diff_left hsub)⟩
  have hintG : ∀ y : ℝ → EuclideanSpace ℝ (Fin n), ContinuousOn y (Icc τ M.T) →
      IntervalIntegrable (fun s => Ff (y s, u s)) volume τ M.T := fun y hy =>
    continuous_comp_piecewise_integrable hτT.le y u hy hupc' Ff hFfcont
  -- the reference trajectory solves the truncated equation
  have hxFf : ∀ t ∈ Icc τ M.T, Ff (x t, u t) = M.f (x t) (u t) := by
    intro t ht
    simp [hFfdef, hbump1 (x t) ((hρ t ht).trans (by linarith))]
  refine ⟨Real.exp (-(K * (M.T - τ))), Real.exp_pos _, ?_⟩
  intro ξ hξ
  obtain ⟨z, hzc, hzeq⟩ := caratheodory_forward_exists hτT (fun t y => Ff (y, u t)) K hK
    (fun t ht y w => hlipF (u t) (huCu t ht) y w) (fun y hy => hintG y hy) ξ
  have hzτ : z τ = ξ := by simpa using hzeq τ ⟨le_rfl, hτT.le⟩
  have hGzi : IntervalIntegrable (fun s => Ff (z s, u s)) volume τ M.T := hintG z hzc
  have hGz : ContinuousOn (fun s => Ff (z s, u s)) (Icc τ M.T \ (Fu : Set ℝ)) :=
    hFfcont.comp_continuousOn
      ((hzc.mono sdiff_subset).prodMk (huc.mono (diff_subset_diff_left hsub)))
  have hzd : ∀ t ∈ Ioo τ M.T \ (Fu : Set ℝ), HasDerivAt z (Ff (z t, u t)) t := by
    intro t ht
    have htIcc : t ∈ Icc τ M.T := ⟨ht.1.1.le, ht.1.2.le⟩
    have hnhds : Icc τ M.T ∈ 𝓝 t := Icc_mem_nhds ht.1.1 ht.1.2
    have hreg : Icc τ M.T \ (Fu : Set ℝ) ∈ 𝓝 t :=
      inter_mem hnhds (Fu.finite_toSet.isClosed.isOpen_compl.mem_nhds ht.2)
    have hAt : ContinuousAt (fun s => Ff (z s, u s)) t := hGz.continuousAt hreg
    have hmeas : StronglyMeasurableAtFilter (fun s => Ff (z s, u s)) (𝓝 t) volume :=
      ⟨Icc τ M.T, hnhds,
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hτT.le).mp hGzi).aestronglyMeasurable⟩
    have hti : IntervalIntegrable (fun s => Ff (z s, u s)) volume τ t :=
      hGzi.mono_set (by
        rw [uIcc_of_le hτT.le, uIcc_of_le htIcc.1]; exact Icc_subset_Icc le_rfl htIcc.2)
    have hd := (intervalIntegral.integral_hasDerivAt_right hti hmeas hAt).const_add ξ
    exact hd.congr_of_eventuallyEq (by filter_upwards [hnhds] with s hs using hzeq s hs)
  set Fs : Finset ℝ := Fx ∪ Fu with hFsdef
  have hxd' : ∀ t ∈ Ioo τ M.T \ (Fs : Set ℝ), HasDerivAt x (Ff (x t, u t)) t := by
    intro t ht
    have htIcc : t ∈ Icc τ M.T := ⟨ht.1.1.le, ht.1.2.le⟩
    rw [hxFf t htIcc]
    refine hxd t ⟨hsub htIcc, ?_⟩
    intro hmem
    exact ht.2 (by simp [hFsdef, hmem])
  have hdelta : ∀ t ∈ Ioo τ M.T \ (Fs : Set ℝ),
      HasDerivAt (fun s => z s - x s) (Ff (z t, u t) - Ff (x t, u t)) t := by
    intro t ht
    exact (hzd t ⟨ht.1, fun hmem => ht.2 (by simp [hFsdef, hmem])⟩).sub (hxd' t ht)
  have hDint : IntervalIntegrable (fun t => Ff (z t, u t) - Ff (x t, u t)) volume τ M.T :=
    hGzi.sub (hintG x hxc')
  have hgr := gronwall_tube (V := EuclideanSpace ℝ (Fin n)) hτT.le x z
    (fun t => Ff (z t, u t) - Ff (x t, u t)) Fs hxc' hzc hdelta hDint K 1 hK.le one_pos
    (by
      intro t ht _
      exact hlipF (u t) (huCu t ⟨ht.1.1.le, ht.1.2.le⟩) (z t) (x t))
    (by
      rw [hzτ]
      have hpos : (0 : ℝ) < Real.exp (K * (M.T - τ)) := Real.exp_pos _
      have hmul : ‖ξ - x τ‖ * Real.exp (K * (M.T - τ)) <
          Real.exp (-(K * (M.T - τ))) * Real.exp (K * (M.T - τ)) :=
        mul_lt_mul_of_pos_right hξ hpos
      rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul)
  have hztube : ∀ t ∈ Icc τ M.T, ‖z t - x t‖ < 1 := by
    intro t ht
    have h1 := hgr t ht
    rw [hzτ] at h1
    have h2 : Real.exp (K * (t - τ)) ≤ Real.exp (K * (M.T - τ)) :=
      Real.exp_le_exp.mpr (by nlinarith [ht.2, sub_nonneg.mpr ht.1])
    have h3 : ‖ξ - x τ‖ * Real.exp (K * (t - τ)) ≤
        ‖ξ - x τ‖ * Real.exp (K * (M.T - τ)) :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have h4 : ‖ξ - x τ‖ * Real.exp (K * (M.T - τ)) < 1 := by
      have hpos : (0 : ℝ) < Real.exp (K * (M.T - τ)) := Real.exp_pos _
      have hmul : ‖ξ - x τ‖ * Real.exp (K * (M.T - τ)) <
          Real.exp (-(K * (M.T - τ))) * Real.exp (K * (M.T - τ)) :=
        mul_lt_mul_of_pos_right hξ hpos
      rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
    linarith
  have hzFf : ∀ t ∈ Icc τ M.T, Ff (z t, u t) = M.f (z t) (u t) := by
    intro t ht
    have h1 : ‖z t‖ ≤ ρ + 1 := by
      have h2 : ‖z t‖ ≤ ‖x t‖ + ‖z t - x t‖ := by
        have := norm_add_le (x t) (z t - x t)
        simpa using this
      have := hztube t ht
      have := hρ t ht
      linarith
    simp [hFfdef, hbump1 (z t) h1]
  refine ⟨z, fun t ht => hUmem t (hsub ht), hupc', hzc, hzτ, Fu ∪ {τ, M.T}, ?_⟩
  intro t ht
  have htF : t ∉ Fu ∧ t ≠ τ ∧ t ≠ M.T := by
    simpa [and_assoc, and_comm, and_left_comm] using ht.2
  have htIoo : t ∈ Ioo τ M.T :=
    ⟨lt_of_le_of_ne ht.1.1 (Ne.symm htF.2.1), lt_of_le_of_ne ht.1.2 htF.2.2⟩
  rw [← hzFf t ht.1]
  exact hzd t ⟨htIoo, htF.1⟩
