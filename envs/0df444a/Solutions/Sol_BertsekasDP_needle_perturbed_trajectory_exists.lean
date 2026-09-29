-- Prove2me | solution 1 for BertsekasDP.needle_perturbed_trajectory_exists
-- status  : ACCEPTED   (prove)
-- author  : @davidnet
-- created : 2026-09-07T22:51:55.172393+00:00
-- url     : https://prove2.me/submissions/0bedf609-324d-41e6-aa94-c2baafb5d918

import Theorems.Thm_BertsekasDP_short_autonomous_arc_exists
import Theorems.Thm_BertsekasDP_piecewise_trajectory_continuation

open Set Filter MeasureTheory
open scoped Topology Interval

set_option backward.isDefEq.respectTransparency false

private lemma integral_eq_sub_off_finset {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (z w : ℝ → E) (F : Finset ℝ) (a b : ℝ) (hab : a ≤ b)
    (hc : ContinuousOn z (Icc a b))
    (hd : ∀ t ∈ Ioo a b \ (F : Set ℝ), HasDerivAt z (w t) t)
    (hi : IntervalIntegrable w volume a b) :
    (∫ t in a..b, w t) = z b - z a := by
  classical
  induction F using Finset.induction_on generalizing a b with
  | empty =>
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc
      (fun t ht => hd t ⟨ht, by simp⟩) hi
  | @insert c F hcF ih =>
    by_cases hci : c ∈ Ioo a b
    · have hl : IntervalIntegrable w volume a c := hi.mono_set (by
        simpa [uIcc_of_le hab, uIcc_of_le hci.1.le] using
          Icc_subset_Icc_right hci.2.le)
      have hr : IntervalIntegrable w volume c b := hi.mono_set (by
        simpa [uIcc_of_le hab, uIcc_of_le hci.2.le] using
          Icc_subset_Icc_left hci.1.le)
      have hleft := ih a c hci.1.le
        (hc.mono (Icc_subset_Icc_right hci.2.le)) (by
          intro t ht
          apply hd t
          exact ⟨⟨ht.1.1, ht.1.2.trans hci.2⟩, by
            simpa only [Finset.coe_insert, mem_insert_iff, not_or] using
              And.intro (ne_of_lt ht.1.2) ht.2⟩) hl
      have hright := ih c b hci.2.le
        (hc.mono (Icc_subset_Icc_left hci.1.le)) (by
          intro t ht
          apply hd t
          exact ⟨⟨hci.1.trans ht.1.1, ht.1.2⟩, by
            simpa only [Finset.coe_insert, mem_insert_iff, not_or] using
              And.intro (ne_of_gt ht.1.1) ht.2⟩) hr
      rw [← intervalIntegral.integral_add_adjacent_intervals hl hr, hleft, hright]
      abel
    · apply ih a b hab hc _ hi
      intro t ht
      apply hd t
      refine ⟨ht.1, ?_⟩
      have htc : t ≠ c := fun heq => hci (heq ▸ ht.1)
      simpa only [Finset.coe_insert, mem_insert_iff, not_or] using And.intro htc ht.2

private lemma window_average_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {τ : ℝ} {c : E} {Φ : ℝ → ℝ → E}
    (hint : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable (Φ ε) volume (τ - ε) τ)
    (hclose : ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ s ∈ Icc (τ - ε) τ, ‖Φ ε s - c‖ ≤ η) :
    Tendsto (fun ε => ε⁻¹ • ∫ s in (τ - ε)..τ, Φ ε s)
      (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [hint, hclose (η / 2) (by linarith), self_mem_nhdsWithin]
    with ε hi hc hεp
  have hεpos : (0 : ℝ) < ε := hεp
  have hle : τ - ε ≤ τ := by linarith
  have hsub : (∫ s in (τ - ε)..τ, Φ ε s) - ε • c =
      ∫ s in (τ - ε)..τ, (Φ ε s - c) := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const, show τ - (τ - ε) = ε by ring]
  have hbd : ‖∫ s in (τ - ε)..τ, (Φ ε s - c)‖ ≤ (η / 2) * ε := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := τ - ε) (b := τ)
      (fun s hs => hc s (by
        rw [uIoc_of_le hle] at hs
        exact ⟨hs.1.le, hs.2⟩))
    simpa only [show τ - (τ - ε) = ε by ring, abs_of_pos hεpos] using hnorm
  have key : ε⁻¹ • (∫ s in (τ - ε)..τ, Φ ε s) - c =
      ε⁻¹ • ((∫ s in (τ - ε)..τ, Φ ε s) - ε • c) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hεpos.ne', one_smul]
  rw [dist_eq_norm, key, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hεpos), hsub]
  calc ε⁻¹ * ‖∫ s in (τ - ε)..τ, (Φ ε s - c)‖ ≤ ε⁻¹ * ((η / 2) * ε) :=
        mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = η / 2 := by field_simp
    _ < η := by linarith

private lemma continuousOn_glue {E : Type*} [TopologicalSpace E]
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (f g : ℝ → E)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc b c))
    (heq : f b = g b) :
    ContinuousOn (fun t => if t ≤ b then f t else g t) (Icc a c) := by
  have hl : ContinuousOn (fun t => if t ≤ b then f t else g t) (Icc a b) :=
    hf.congr (fun t ht => if_pos ht.2)
  have hr : ContinuousOn (fun t => if t ≤ b then f t else g t) (Icc b c) := by
    apply hg.congr
    intro t ht
    by_cases h : t ≤ b
    · have he : t = b := le_antisymm h ht.1
      simp [he, heq]
    · simp [h]
  have h := hl.union_of_isClosed hr isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc hab hbc] at h

private lemma integrable_of_bounded_continuous_off_finset
    {E : Type*} [NormedAddCommGroup E] {a b : ℝ} (hab : a ≤ b)
    (v : ℝ → E) (F : Finset ℝ)
    (hv : ContinuousOn v (Icc a b \ (F : Set ℝ)))
    (hbdd : Bornology.IsBounded (v '' Icc a b)) :
    IntervalIntegrable v volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hm : AEStronglyMeasurable v (volume.restrict (Icc a b)) := by
    have h := hv.aestronglyMeasurable (μ := volume) (measurableSet_Icc.diff F.finite_toSet.measurableSet)
    rwa [Measure.restrict_congr_set (sdiff_null_ae_eq_self (F.finite_toSet.measure_zero volume))] at h
  obtain ⟨C, hC⟩ := hbdd.exists_norm_le
  apply (integrable_const C).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC (v t) (mem_image_of_mem v ht)

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

private lemma admissible_dynamics_integral {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : Continuous (Function.uncurry M.f))
    (u : ℝ → EuclideanSpace ℝ (Fin m)) (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hadm : BertsekasCTAdmissibleFrom M 0 M.x0 u x)
    (a b : ℝ) (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ M.T) :
    (∫ t in a..b, M.f (x t) (u t)) = x b - x a := by
  obtain ⟨F, hF⟩ := hadm.2.2.2.2
  have hsub : Icc a b ⊆ Icc 0 M.T := Icc_subset_Icc ha hb
  apply integral_eq_sub_off_finset x _ F a b hab (hadm.2.2.1.mono hsub)
  · intro t ht
    exact hF t ⟨hsub ⟨ht.1.1.le, ht.1.2.le⟩, ht.2⟩
  · exact (continuous_comp_piecewise_integrable M.hT.le x u hadm.2.2.1 hadm.2.1
      (Function.uncurry M.f) hf).mono_set (by
        simpa [uIcc_of_le M.hT.le, uIcc_of_le hab] using hsub)

private lemma glue_needle_admissible {n m : ℕ} (M : BertsekasCTModel n m)
    (u : ℝ → EuclideanSpace ℝ (Fin m)) (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hadm : BertsekasCTAdmissibleFrom M 0 M.x0 u x)
    (τ ε : ℝ) (hτ : τ ∈ Ioo 0 M.T) (hε : 0 < ε) (hετ : ε < τ)
    (v : EuclideanSpace ℝ (Fin m)) (hv : v ∈ M.U)
    (y z : ℝ → EuclideanSpace ℝ (Fin n))
    (hyc : ContinuousOn y (Icc (τ - ε) τ)) (hyi : y (τ - ε) = x (τ - ε))
    (hyd : ∀ t ∈ Ioo (τ - ε) τ, HasDerivAt y (M.f (y t) v) t)
    (hz : BertsekasCTAdmissibleFrom M τ (y τ) u z) :
    BertsekasCTAdmissibleFrom M 0 M.x0
      (fun t => if t ∈ Ioc (τ - ε) τ then v else u t)
      (fun t => if t ≤ τ - ε then x t else if t ≤ τ then y t else z t) := by
  classical
  let w := fun t => if t ∈ Ioc (τ - ε) τ then v else u t
  let X := fun t => if t ≤ τ - ε then x t else if t ≤ τ then y t else z t
  have hab : 0 ≤ τ - ε := by linarith
  have hbc : τ - ε ≤ τ := by linarith
  have hwleft {t : ℝ} (ht : t < τ - ε) : w =ᶠ[𝓝 t] u := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    have hs : s < τ - ε := hs
    simp only [w, if_neg (show s ∉ Ioc (τ - ε) τ from fun h => by linarith [h.1])]
  have hwmid {t : ℝ} (ht : t ∈ Ioo (τ - ε) τ) : w =ᶠ[𝓝 t] (fun _ => v) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact if_pos ⟨hs.1, hs.2.le⟩
  have hwright {t : ℝ} (ht : τ < t) : w =ᶠ[𝓝 t] u := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hs : τ < s := hs
    exact if_neg (show s ∉ Ioc (τ - ε) τ from fun h => by linarith [h.2])
  have hXleft {t : ℝ} (ht : t < τ - ε) : X =ᶠ[𝓝 t] x := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact if_pos hs.le
  have hXmid {t : ℝ} (ht : t ∈ Ioo (τ - ε) τ) : X =ᶠ[𝓝 t] y := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    simp only [X, if_neg (not_le.mpr hs.1), if_pos hs.2.le]
  have hXright {t : ℝ} (ht : τ < t) : X =ᶠ[𝓝 t] z := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hs : τ < s := hs
    simp only [X, if_neg (show ¬s ≤ τ - ε by linarith), if_neg (not_le.mpr hs)]
  obtain ⟨Fu, hFu⟩ := hadm.2.1.2
  obtain ⟨Fx, hFx⟩ := hadm.2.2.2.2
  obtain ⟨Fz, hFz⟩ := hz.2.2.2.2
  let G : Finset ℝ := Fu ∪ Fx ∪ Fz ∪ {0, M.T, τ - ε, τ}
  have hreg {t : ℝ} (ht : t ∈ Icc 0 M.T \ (G : Set ℝ)) :
      t ∈ Ioo 0 M.T ∧ t ∉ Fu ∧ t ∉ Fx ∧ t ∉ Fz ∧ t ≠ τ - ε ∧ t ≠ τ := by
    have hn : t ∉ Fu ∧ t ∉ Fx ∧ t ∉ Fz ∧ t ≠ 0 ∧ t ≠ M.T ∧
        t ≠ τ - ε ∧ t ≠ τ := by
      simpa [G, not_or, and_assoc, and_left_comm, and_comm] using ht.2
    exact ⟨⟨lt_of_le_of_ne ht.1.1 hn.2.2.2.1.symm,
      lt_of_le_of_ne ht.1.2 hn.2.2.2.2.1⟩, hn.1, hn.2.1, hn.2.2.1,
      hn.2.2.2.2.2.1, hn.2.2.2.2.2.2⟩
  refine ⟨?_, ⟨?_, G, ?_⟩, ?_, ?_, G, ?_⟩
  · intro t ht
    change (if t ∈ Ioc (τ - ε) τ then v else u t) ∈ M.U
    split_ifs
    · exact hv
    · exact hadm.1 t ht
  · apply ((Bornology.isBounded_singleton (x := v)).union hadm.2.1.1).subset
    rintro q ⟨t, ht, rfl⟩
    by_cases h : t ∈ Ioc (τ - ε) τ
    · simp [h]
    · simp only [if_neg h]
      exact Or.inr (mem_image_of_mem u ht)
  · intro t ht
    have hr := hreg ht
    have hut : ContinuousAt u t := hFu.continuousAt
      (inter_mem (Icc_mem_nhds hr.1.1 hr.1.2)
        ((Fu.finite_toSet.isClosed.isOpen_compl).mem_nhds hr.2.1))
    apply ContinuousAt.continuousWithinAt
    change ContinuousAt w t
    rcases lt_or_gt_of_ne hr.2.2.2.2.1 with hleft | hright
    · exact (continuousAt_congr (hwleft hleft)).mpr hut
    · rcases lt_or_gt_of_ne hr.2.2.2.2.2 with hmid | htail
      · exact (continuousAt_congr (hwmid ⟨hright, hmid⟩)).mpr continuousAt_const
      · exact (continuousAt_congr (hwright htail)).mpr hut
  · apply continuousOn_glue hab (hbc.trans hτ.2.le) x
      (fun t => if t ≤ τ then y t else z t)
      (hadm.2.2.1.mono (Icc_subset_Icc_right (hbc.trans hτ.2.le)))
    · exact continuousOn_glue hbc hτ.2.le y z hyc hz.2.2.1 hz.2.2.2.1.symm
    · simp only [if_pos hbc, hyi]
  · simp only [if_pos hab, hadm.2.2.2.1]
  · intro t ht
    have hr := hreg ht
    change HasDerivAt X (M.f (X t) (w t)) t
    rcases lt_or_gt_of_ne hr.2.2.2.2.1 with hleft | hright
    · have h := (hFx t ⟨ht.1, hr.2.2.1⟩).congr_of_eventuallyEq (hXleft hleft)
      simpa only [(hXleft hleft).eq_of_nhds, (hwleft hleft).eq_of_nhds] using h
    · rcases lt_or_gt_of_ne hr.2.2.2.2.2 with hmid | htail
      · have h := (hyd t ⟨hright, hmid⟩).congr_of_eventuallyEq (hXmid ⟨hright, hmid⟩)
        simpa only [(hXmid ⟨hright, hmid⟩).eq_of_nhds,
          (hwmid ⟨hright, hmid⟩).eq_of_nhds] using h
      · have h := (hFz t ⟨⟨htail.le, ht.1.2⟩, hr.2.2.2.1⟩).congr_of_eventuallyEq
          (hXright htail)
        simpa only [(hXright htail).eq_of_nhds, (hwright htail).eq_of_nhds] using h

theorem solution
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : ContDiff ℝ 1 (Function.uncurry M.f))
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hadm : BertsekasCTAdmissibleFrom M 0 M.x0 u x)
    (τ : ℝ) (hτ : τ ∈ Set.Ioo 0 M.T) (huτ : ContinuousAt u τ)
    (v : EuclideanSpace ℝ (Fin m)) (hv : v ∈ M.U) :
    ∃ (xε : ℝ → ℝ → EuclideanSpace ℝ (Fin n)) (K : ℝ),
      (∀ᶠ ε in 𝓝[>] (0 : ℝ),
        BertsekasCTAdmissibleFrom M 0 M.x0
            (fun s => if s ∈ Set.Ioc (τ - ε) τ then v else u s) (xε ε) ∧
          (∀ s ∈ Set.Icc 0 (τ - ε), xε ε s = x s) ∧
          (∀ s ∈ Set.Icc (τ - ε) τ, ‖xε ε s - x τ‖ ≤ K * ε)) ∧
      Tendsto (fun ε => ε⁻¹ • (xε ε τ - x τ)) (𝓝[>] (0 : ℝ))
        (𝓝 (M.f (x τ) v - M.f (x τ) (u τ)))  := by
  classical
  have hx := hadm.2.2.1
  have hfi := continuous_comp_piecewise_integrable M.hT.le x u hx hadm.2.1
    (Function.uncurry M.f) hf.continuous
  have hK := (isCompact_Icc.image_of_continuousOn hx).prod
    hadm.2.1.1.isCompact_closure
  obtain ⟨C, hC⟩ := (hK.image hf.continuous).isBounded.exists_norm_le
  have hbound : ∀ t ∈ Icc 0 M.T, ‖M.f (x t) (u t)‖ ≤ C := by
    intro t ht
    exact hC _ ⟨(x t, u t),
      ⟨mem_image_of_mem x ht, subset_closure (mem_image_of_mem u ht)⟩, rfl⟩
  have hlt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < τ :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hτ.1)
  have hwin : ∀ ε : ℝ, ε < τ → 0 < ε → Icc (τ - ε) τ ⊆ Icc 0 M.T := by
    intro ε he ht s hs
    exact ⟨by linarith [hs.1], hs.2.trans hτ.2.le⟩
  have ha : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖x (τ - ε) - x τ‖ ≤ C * ε := by
    filter_upwards [hlt, self_mem_nhdsWithin] with ε he hp
    have hp : (0 : ℝ) < ε := hp
    have hab : τ - ε ≤ τ := by linarith
    rw [norm_sub_rev, ← admissible_dynamics_integral M hf.continuous u x hadm
      (τ - ε) τ hab (by linarith) hτ.2.le]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := τ - ε) (b := τ)
      (fun s hs => hbound s (hwin ε he hp (by
        rw [uIoc_of_le hab] at hs
        exact ⟨hs.1.le, hs.2⟩)))
    simpa only [show τ - (τ - ε) = ε by ring, abs_of_pos hp] using h
  have hfv : ContDiff ℝ 1 (fun q => M.f q v) :=
    hf.comp (contDiff_id.prodMk contDiff_const)
  obtain ⟨y, K, hy⟩ := BertsekasDP.short_autonomous_arc_exists
    (fun q => M.f q v) hfv (x τ) (fun ε => x (τ - ε)) τ C ha
  have hA : Tendsto (fun ε => ε⁻¹ • ∫ s in (τ - ε)..τ, M.f (y ε s) v)
      (𝓝[>] (0 : ℝ)) (𝓝 (M.f (x τ) v)) := by
    refine window_average_tendsto ?_ ?_
    · filter_upwards [hy, self_mem_nhdsWithin] with ε he hp
      have hp : (0 : ℝ) < ε := hp
      exact (hfv.continuous.comp_continuousOn he.1).intervalIntegrable_of_Icc (by linarith)
    · intro η hη
      obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hfv.continuous.continuousAt η hη
      have hk : Tendsto (fun ε : ℝ => K * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa only [id_eq, mul_zero] using
          (tendsto_const_nhds (x := K)).mul ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left
            nhdsWithin_le_nhds)
      filter_upwards [hy, hk.eventually_lt_const hδ] with ε he hkε
      intro s hs
      exact (hd (by rw [dist_eq_norm]; exact (he.2.2.2 s hs).trans_lt hkε)).le
  have hB : Tendsto (fun ε => ε⁻¹ • ∫ s in (τ - ε)..τ, M.f (x s) (u s))
      (𝓝[>] (0 : ℝ)) (𝓝 (M.f (x τ) (u τ))) := by
    refine window_average_tendsto ?_ ?_
    · filter_upwards [hlt, self_mem_nhdsWithin] with ε he hp
      have hp : (0 : ℝ) < ε := hp
      exact hfi.mono_set (by
        simpa [uIcc_of_le M.hT.le, uIcc_of_le (by linarith : τ - ε ≤ τ)] using
          hwin ε he hp)
    · intro η hη
      have hc : ContinuousAt (fun s => M.f (x s) (u s)) τ :=
        hf.continuous.continuousAt.comp
          ((hx.continuousAt (Icc_mem_nhds hτ.1 hτ.2)).prodMk huτ)
      obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hc η hη
      have he : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < δ :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
      filter_upwards [he] with ε he
      intro s hs
      apply (hd ?_).le
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hs.2])]
      linarith [hs.1]
  have hfirst : Tendsto (fun ε => ε⁻¹ • (y ε τ - x τ)) (𝓝[>] (0 : ℝ))
      (𝓝 (M.f (x τ) v - M.f (x τ) (u τ))) := by
    refine Tendsto.congr' ?_ (hA.sub hB)
    filter_upwards [hy, hlt, self_mem_nhdsWithin] with ε he heτ hp
    have hp : (0 : ℝ) < ε := hp
    have hab : τ - ε ≤ τ := by linarith
    rw [← smul_sub, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab he.1
      he.2.2.1 ((hfv.continuous.comp_continuousOn he.1).intervalIntegrable_of_Icc hab),
      admissible_dynamics_integral M hf.continuous u x hadm (τ - ε) τ hab
        (by linarith) hτ.2.le, he.2.1]
    congr 1
    abel
  obtain ⟨δ, hδ, hcontinue⟩ := BertsekasDP.piecewise_trajectory_continuation
    M hf u x hadm τ hτ
  have hk : Tendsto (fun ε : ℝ => K * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [id_eq, mul_zero] using
      (tendsto_const_nhds (x := K)).mul ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left
            nhdsWithin_le_nhds)
  have hz : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∃ z, BertsekasCTAdmissibleFrom M τ (y ε τ) u z := by
    filter_upwards [hy, hk.eventually_lt_const hδ, self_mem_nhdsWithin] with ε he hkε hp
    have hp : (0 : ℝ) < ε := hp
    exact hcontinue _ ((he.2.2.2 τ ⟨by linarith, le_rfl⟩).trans_lt hkε)
  let z : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun ε =>
    if h : ∃ z, BertsekasCTAdmissibleFrom M τ (y ε τ) u z then h.choose else x
  have hzc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), BertsekasCTAdmissibleFrom M τ (y ε τ) u (z ε) := by
    filter_upwards [hz] with ε he
    simpa only [z, dif_pos he] using he.choose_spec
  let X := fun ε t => if t ≤ τ - ε then x t else if t ≤ τ then y ε t else z ε t
  refine ⟨X, K, ?_, ?_⟩
  · filter_upwards [hy, hzc, hlt, self_mem_nhdsWithin] with ε he hzε heτ hp
    have hp : (0 : ℝ) < ε := hp
    refine ⟨glue_needle_admissible M u x hadm τ ε hτ hp heτ v hv
      (y ε) (z ε) he.1 he.2.1 he.2.2.1 hzε, ?_, ?_⟩
    · intro s hs
      exact if_pos hs.2
    · intro s hs
      have heq : X ε s = y ε s := by
        by_cases h : s ≤ τ - ε
        · have hs' : s = τ - ε := le_antisymm h hs.1
          simp [X, hs', he.2.1]
        · simp only [X, if_neg h, if_pos hs.2]
      rw [heq]
      exact he.2.2.2 s hs
  · refine Tendsto.congr' ?_ hfirst
    filter_upwards [self_mem_nhdsWithin] with ε hp
    have hp : (0 : ℝ) < ε := hp
    simp only [X, if_neg (show ¬τ ≤ τ - ε by linarith), if_pos le_rfl]
