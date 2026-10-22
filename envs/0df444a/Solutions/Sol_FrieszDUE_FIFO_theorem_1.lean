-- Prove2me | solution 1 for FrieszDUE.FIFO.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T11:42:06.34958+00:00
-- url     : https://prove2.me/submissions/89b7e4b8-6619-43ab-b3c8-6dd6f1f822fd

import Mathlib
import Definitions.Def_FrieszDUE_FIFO_Setting

set_option autoImplicit false

namespace FrieszDUE.FIFO.Aux

open MeasureTheory Set Filter Topology

/-- vehicles that entered during `[0,t]` and have exited by time `t` -/
def Eset (τ : ℝ → ℝ) (t : ℝ) : Set ℝ := {s | s ∈ Icc 0 t ∧ τ s ≤ t}

/-- cumulative inflow, using the continuous extension `u (max s 0)` -/
noncomputable def Ufun (u : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, u (max s 0)

/-- `t - α * (exited mass by time t)` -/
noncomputable def phi (α : ℝ) (u τ : ℝ → ℝ) (t : ℝ) : ℝ := t - α * ∫ s in Eset τ t, u s

lemma ut_cont (u : ℝ → ℝ) (hu_cont : ContinuousOn u (Ici 0)) :
    Continuous (fun s : ℝ => u (max s 0)) :=
  hu_cont.comp_continuous (continuous_id.max continuous_const) (fun s => le_max_right s 0)

lemma ut_nonneg (u : ℝ → ℝ) (hu_nonneg : ∀ t, 0 ≤ t → 0 ≤ u t) (s : ℝ) :
    0 ≤ u (max s 0) := hu_nonneg _ (le_max_right s 0)

lemma U_sub (u : ℝ → ℝ) (hu_cont : ContinuousOn u (Ici 0)) (x y : ℝ) :
    Ufun u y - Ufun u x = ∫ s in x..y, u (max s 0) := by
  unfold Ufun
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ => u (max s 0)) volume a b :=
    fun a b => (ut_cont u hu_cont).intervalIntegrable a b
  rw [intervalIntegral.integral_interval_sub_left (hi 0 y) (hi 0 x)]

lemma U_mono (u : ℝ → ℝ) (hu_nonneg : ∀ t, 0 ≤ t → 0 ≤ u t)
    (hu_cont : ContinuousOn u (Ici 0)) : Monotone (Ufun u) := by
  intro x y hxy
  have h := U_sub u hu_cont x y
  have : 0 ≤ ∫ s in x..y, u (max s 0) :=
    intervalIntegral.integral_nonneg hxy (fun s _ => ut_nonneg u hu_nonneg s)
  linarith

lemma U_cont (u : ℝ → ℝ) (hu_cont : ContinuousOn u (Ici 0)) : Continuous (Ufun u) := by
  unfold Ufun
  exact intervalIntegral.continuous_primitive
    (fun a b => (ut_cont u hu_cont).intervalIntegrable a b) 0

lemma setInt_Icc (u : ℝ → ℝ) (hu_cont : ContinuousOn u (Ici 0)) (x y : ℝ)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∫ s in Icc x y, u s = Ufun u y - Ufun u x := by
  rw [U_sub u hu_cont x y, intervalIntegral.integral_of_le hxy, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
  rw [max_eq_left (le_trans hx hs.1)]

lemma intOn_Icc (u : ℝ → ℝ) (hu_cont : ContinuousOn u (Ici 0)) (x y : ℝ) (hx : 0 ≤ x) :
    IntegrableOn u (Icc x y) :=
  (hu_cont.mono (fun s hs => le_trans hx hs.1)).integrableOn_compact isCompact_Icc

lemma arcVolume_nonneg (u τ : ℝ → ℝ) (hu_nonneg : ∀ t, 0 ≤ t → 0 ≤ u t) (t : ℝ) :
    0 ≤ arcVolume u τ t := by
  unfold arcVolume
  apply integral_nonneg_of_ae
  have hle : (volume.restrict {s : ℝ | s ∈ Icc 0 t ∧ t < τ s}) ≤ volume.restrict (Icc 0 t) :=
    Measure.restrict_mono (fun s hs => hs.1) le_rfl
  exact ae_mono hle (ae_restrict_of_forall_mem measurableSet_Icc
    (fun s hs => hu_nonneg s hs.1))

lemma tau_ge (α β : ℝ) (hα : 0 < α) (u τ : ℝ → ℝ) (hu_nonneg : ∀ t, 0 ≤ t → 0 ≤ u t)
    (hτ : IsLinearExitTime α β u τ) (s : ℝ) (hs : 0 ≤ s) : s + β ≤ τ s := by
  rw [hτ s hs]
  unfold linearDelay
  have := arcVolume_nonneg u τ hu_nonneg s
  nlinarith

lemma step (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (u : ℝ → ℝ)
    (hu_nonneg : ∀ t, 0 ≤ t → 0 ≤ u t) (hu_cont : ContinuousOn u (Ici 0))
    (τ : ℝ → ℝ) (hτ : IsLinearExitTime α β u τ) (T : ℝ)
    (hT : StrictMonoOn τ (Ico 0 T)) (hφ : StrictMonoOn (phi α u τ) (Ico 0 T)) :
    StrictMonoOn τ (Ico 0 (T + β)) ∧ StrictMonoOn (phi α u τ) (Ico 0 (T + β)) := by
  -- exited vehicles entered before `T`
  have hEsub : ∀ t, t < T + β → Eset τ t ⊆ Ico 0 T := by
    intro t ht s hs
    have h1 := tau_ge α β hα u τ hu_nonneg hτ s hs.1.1
    exact ⟨hs.1.1, by linarith [hs.2]⟩
  have hEmeas : ∀ t, t < T + β → MeasurableSet (Eset τ t) := by
    intro t ht
    have hoc : (Eset τ t).OrdConnected := by
      refine ⟨fun x hx y hy z hz => ?_⟩
      have hyT := hEsub t ht hy
      have hzT : z ∈ Ico 0 T := ⟨le_trans hx.1.1 hz.1, lt_of_le_of_lt hz.2 hyT.2⟩
      refine ⟨⟨le_trans hx.1.1 hz.1, le_trans hz.2 hy.1.2⟩, ?_⟩
      exact le_trans (hT.monotoneOn hzT hyT hz.2) hy.2
    exact hoc.measurableSet
  have hEint : ∀ t, IntegrableOn u (Eset τ t) := fun t =>
    (intOn_Icc u hu_cont 0 t le_rfl).mono_set (fun s hs => hs.1)
  -- the decomposition of the exit time
  have hform : ∀ t, 0 ≤ t → t < T + β → τ t = phi α u τ t + α * Ufun u t + β := by
    intro t ht0 ht
    have hS : {s : ℝ | s ∈ Icc 0 t ∧ t < τ s} = Icc 0 t \ Eset τ t := by
      ext s
      simp only [Eset, mem_setOf_eq, mem_diff, not_and, not_le]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun _ => h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2 h1⟩
    have hv : arcVolume u τ t = Ufun u t - ∫ s in Eset τ t, u s := by
      unfold arcVolume
      rw [hS, integral_diff (hEmeas t ht) (intOn_Icc u hu_cont 0 t le_rfl) (fun s hs => hs.1),
        setInt_Icc u hu_cont 0 t le_rfl ht0]
      have : Ufun u 0 = 0 := by simp [Ufun]
      rw [this, sub_zero]
    rw [hτ t ht0, hv]
    unfold phi linearDelay
    ring
  -- the exits between two times
  have hDmem : ∀ t1 t2, 0 ≤ t1 → t1 < t2 → t2 < T + β → ∀ s ∈ Eset τ t2 \ Eset τ t1,
      t1 < τ s ∧ τ s ≤ t2 ∧ s ∈ Ico 0 T := by
    intro t1 t2 h0 h12 h2 s hs
    refine ⟨?_, hs.1.2, hEsub t2 h2 hs.1⟩
    by_contra hc
    push_neg at hc
    have h1 := tau_ge α β hα u τ hu_nonneg hτ s hs.1.1.1
    exact hs.2 ⟨⟨hs.1.1.1, by linarith⟩, hc⟩
  have hdiff : ∀ t1 t2, t1 ≤ t2 → t1 < T + β →
      phi α u τ t2 - phi α u τ t1 = (t2 - t1) - α * ∫ s in Eset τ t2 \ Eset τ t1, u s := by
    intro t1 t2 h12 h1
    have hsub : Eset τ t1 ⊆ Eset τ t2 := fun s hs =>
      ⟨⟨hs.1.1, le_trans hs.1.2 h12⟩, le_trans hs.2 h12⟩
    rw [integral_diff (hEmeas t1 h1) (hEint t2) hsub]
    unfold phi
    ring
  have key : ∀ t1 t2, 0 ≤ t1 → t1 < t2 → t2 < T + β →
      α * ∫ s in Eset τ t2 \ Eset τ t1, u s < t2 - t1 := by
    intro t1 t2 h0 h12 h2
    set D := Eset τ t2 \ Eset τ t1 with hDdef
    have hD := hDmem t1 t2 h0 h12 h2
    by_cases hsing : D.Subsingleton
    · rw [setIntegral_measure_zero _ (hsing.measure_zero volume)]
      linarith
    · obtain ⟨s1, hs1, s1', hs1', hlt⟩ := (not_subsingleton_iff.mp hsing).exists_lt
      set δ := phi α u τ s1' - phi α u τ s1 with hδ
      have hδpos : 0 < δ := by
        have := hφ (hD s1 hs1).2.2 (hD s1' hs1').2.2 hlt
        linarith
      have bound : ∀ s ∈ D, ∀ s' ∈ D, s ≤ s1 → s1' ≤ s' →
          α * (Ufun u s' - Ufun u s) < t2 - t1 - δ := by
        intro s hs s' hs' hss hss'
        obtain ⟨a1, a2, a3⟩ := hD s hs
        obtain ⟨b1, b2, b3⟩ := hD s' hs'
        have f1 := hform s a3.1 (by linarith [a3.2])
        have f2 := hform s' b3.1 (by linarith [b3.2])
        have m1 : phi α u τ s ≤ phi α u τ s1 := hφ.monotoneOn a3 (hD s1 hs1).2.2 hss
        have m2 : phi α u τ s1' ≤ phi α u τ s' := hφ.monotoneOn (hD s1' hs1').2.2 b3 hss'
        linarith
      have hne : D.Nonempty := ⟨s1, hs1⟩
      have hbb : BddBelow D := ⟨0, fun s hs => (hD s hs).2.2.1⟩
      have hba : BddAbove D := ⟨T, fun s hs => (hD s hs).2.2.2.le⟩
      set a := sInf D with ha
      set b := sSup D with hb
      have ha0 : 0 ≤ a := le_csInf hne (fun s hs => (hD s hs).2.2.1)
      have hab : a ≤ b := le_trans (csInf_le hbb hs1) (le_csSup hba hs1)
      have hDab : D ⊆ Icc a b := fun s hs => ⟨csInf_le hbb hs, le_csSup hba hs⟩
      have hint1 : ∫ s in D, u s ≤ ∫ s in Icc a b, u s := by
        apply setIntegral_mono_set (intOn_Icc u hu_cont a b ha0)
        · exact ae_restrict_of_forall_mem measurableSet_Icc
            (fun s hs => hu_nonneg s (le_trans ha0 hs.1))
        · exact Eventually.of_forall hDab
      rw [setInt_Icc u hu_cont a b ha0 hab] at hint1
      have hlim : α * (Ufun u b - Ufun u a) ≤ t2 - t1 - δ := by
        have hc : Continuous (fun η : ℝ => α * (Ufun u (b - η) - Ufun u (a + η))) := by
          have := U_cont u hu_cont
          fun_prop
        have ht : Tendsto (fun η : ℝ => α * (Ufun u (b - η) - Ufun u (a + η))) (𝓝[>] 0)
            (𝓝 (α * (Ufun u b - Ufun u a))) := by
          have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
          simpa using this
        refine le_of_tendsto ht (eventually_nhdsWithin_of_forall (fun η hη => ?_))
        have hη : (0:ℝ) < η := hη
        obtain ⟨s, hs, hsa⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right a hη)
        obtain ⟨s', hs', hsb⟩ := exists_lt_of_lt_csSup hne (sub_lt_self b hη)
        have hm : min s s1 ∈ D := by
          rcases min_choice s s1 with h | h <;> rw [h] <;> assumption
        have hM : max s' s1' ∈ D := by
          rcases max_choice s' s1' with h | h <;> rw [h] <;> assumption
        have hb' := bound (min s s1) hm (max s' s1') hM (min_le_right _ _) (le_max_right _ _)
        have u1 : Ufun u (b - η) ≤ Ufun u (max s' s1') :=
          U_mono u hu_nonneg hu_cont (le_trans hsb.le (le_max_left _ _))
        have u2 : Ufun u (min s s1) ≤ Ufun u (a + η) :=
          U_mono u hu_nonneg hu_cont (le_trans (min_le_left _ _) hsa.le)
        have : α * (Ufun u (b - η) - Ufun u (a + η)) ≤ α * (Ufun u (max s' s1') - Ufun u (min s s1)) :=
          mul_le_mul_of_nonneg_left (by linarith) hα.le
        linarith
      have := mul_le_mul_of_nonneg_left hint1 hα.le
      linarith
  constructor
  · intro t1 ht1 t2 ht2 h12
    have f1 := hform t1 ht1.1 ht1.2
    have f2 := hform t2 ht2.1 ht2.2
    have k := key t1 t2 ht1.1 h12 ht2.2
    have d := hdiff t1 t2 h12.le ht1.2
    have um : α * Ufun u t1 ≤ α * Ufun u t2 :=
      mul_le_mul_of_nonneg_left (U_mono u hu_nonneg hu_cont h12.le) hα.le
    linarith
  · intro t1 ht1 t2 ht2 h12
    have k := key t1 t2 ht1.1 h12 ht2.2
    have d := hdiff t1 t2 h12.le ht1.2
    linarith

lemma all_n (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (u : ℝ → ℝ)
    (hu_nonneg : ∀ t, 0 ≤ t → 0 ≤ u t) (hu_cont : ContinuousOn u (Ici 0))
    (τ : ℝ → ℝ) (hτ : IsLinearExitTime α β u τ) (n : ℕ) :
    StrictMonoOn τ (Ico 0 (n * β)) ∧ StrictMonoOn (phi α u τ) (Ico 0 (n * β)) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, Ico_self]
    exact ⟨fun a ha => by simp at ha, fun a ha => by simp at ha⟩
  | succ k ih =>
    have := step α β hα hβ u hu_nonneg hu_cont τ hτ (k * β) ih.1 ih.2
    have e : ((k + 1 : ℕ) : ℝ) * β = k * β + β := by push_cast; ring
    rw [e]
    exact this

end FrieszDUE.FIFO.Aux

open FrieszDUE.FIFO in
theorem solution (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (u : ℝ → ℝ)
    (hu_nonneg : ∀ t, 0 ≤ t → 0 ≤ u t) (hu_cont : ContinuousOn u (Set.Ici 0))
    (τ : ℝ → ℝ) (hτ : IsLinearExitTime α β u τ) :
    StrictMonoOn τ (Set.Ici 0) ∧ Set.InjOn τ (Set.Ici 0) := by
  have hsm : StrictMonoOn τ (Set.Ici 0) := by
    intro a ha b hb hab
    obtain ⟨n, hn⟩ := exists_nat_gt (b / β)
    have hbn : b < n * β := by rwa [div_lt_iff₀ hβ] at hn
    have h := (FrieszDUE.FIFO.Aux.all_n α β hα hβ u hu_nonneg hu_cont τ hτ n).1
    exact h ⟨ha, lt_trans hab hbn⟩ ⟨hb, hbn⟩ hab
  exact ⟨hsm, hsm.injOn⟩
