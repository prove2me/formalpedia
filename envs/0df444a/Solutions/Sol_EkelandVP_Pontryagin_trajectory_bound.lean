-- Prove2me | solution 1 for EkelandVP.Pontryagin.trajectory_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:44:09.864762+00:00
-- url     : https://prove2.me/submissions/5a2d3f48-de31-4ffd-ac94-8511f771fd5d

import Mathlib
import Definitions.Def_EkelandVP_Pontryagin_IsTrajectory

set_option autoImplicit false
open MeasureTheory Filter Topology Set intervalIntegral EkelandVP.Pontryagin

lemma ekv_meas_bdd {n : ℕ} {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K]
    (T : ℝ) (hT : 0 < T)
    (f : EuclideanSpace ℝ (Fin n) → K → ℝ → EuclideanSpace ℝ (Fin n))
    (hf : ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) × K × ℝ => f z.1 z.2.1 z.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc 0 T))
    (u : ℝ → K) (hu : Measurable u) (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hx : ContinuousOn x (Set.Icc 0 T)) :
    ∃ g : ℝ → EuclideanSpace ℝ (Fin n), Measurable g ∧
      (∀ s ∈ Set.Icc 0 T, g s = f (x s) (u s) s) ∧ ∃ M : ℝ, ∀ s ∈ Set.Icc 0 T, ‖g s‖ ≤ M := by
  set cl : ℝ → ℝ := fun s => max 0 (min s T) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hclmem : ∀ s, cl s ∈ Set.Icc (0 : ℝ) T := fun s =>
    ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hclid : ∀ s ∈ Set.Icc (0 : ℝ) T, cl s = s := fun s hs => by
    simp only [hcl]
    rw [min_eq_left hs.2, max_eq_right hs.1]
  have hx'' : Continuous (fun s => x (cl s)) := hx.comp_continuous hclc hclmem
  have hF : Continuous (fun z : EuclideanSpace ℝ (Fin n) × K × ℝ => f z.1 z.2.1 (cl z.2.2)) := by
    have hc : Continuous (fun z : EuclideanSpace ℝ (Fin n) × K × ℝ => (z.1, z.2.1, cl z.2.2)) :=
      continuous_fst.prodMk (continuous_snd.fst.prodMk (hclc.comp continuous_snd.snd))
    exact hf.comp_continuous hc (fun z => ⟨mem_univ _, mem_univ _, hclmem _⟩)
  refine ⟨fun s => f (x (cl s)) (u s) (cl s), ?_, ?_, ?_⟩
  · have hm : Measurable (fun s : ℝ => (x (cl s), u s, s)) :=
      hx''.measurable.prodMk (hu.prodMk measurable_id)
    exact hF.measurable.comp hm
  · intro s hs
    simp only [hclid s hs]
  · have hCx : IsCompact (x '' Set.Icc 0 T) := isCompact_Icc.image_of_continuousOn hx
    have hS : IsCompact ((x '' Set.Icc 0 T) ×ˢ (Set.univ ×ˢ Set.Icc (0 : ℝ) T)) :=
      hCx.prod ((isCompact_univ : IsCompact (Set.univ : Set K)).prod isCompact_Icc)
    have hfS : ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) × K × ℝ => f z.1 z.2.1 z.2.2)
        ((x '' Set.Icc 0 T) ×ˢ (Set.univ ×ˢ Set.Icc (0 : ℝ) T)) :=
      hf.mono (fun z hz => ⟨mem_univ _, mem_univ _, hz.2.2⟩)
    obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hfS
    refine ⟨M, fun s hs => ?_⟩
    simp only [hclid s hs]
    exact hM (x s, u s, s) ⟨⟨s, hs, rfl⟩, mem_univ _, hs⟩

lemma ekv_ac_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) {a b : ℝ}
    (h : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => ∑ i ∈ s, f i t) a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (contDiffOn_const (c := (0 : ℝ)) (n := 1) (s := uIcc a b)).absolutelyContinuousOnInterval
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self _ _)).fun_add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma ekv_gron {m : ℕ} (T c : ℝ) (hT : 0 < T) (a : Fin m → ℝ) (G : ℝ → Fin m → ℝ)
    (hG : ∀ i, IntervalIntegrable (fun s => G s i) volume 0 T)
    (hineq : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∑ i, (a i + ∫ v in (0:ℝ)..s, G v i) * G s i ≤
        c * (1 + ∑ i, (a i + ∫ v in (0:ℝ)..s, G v i) ^ 2)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, 1 + ∑ i, (a i + ∫ v in (0:ℝ)..t, G v i) ^ 2 ≤
      Real.exp (2 * c * t) * (1 + ∑ i, a i ^ 2) := by
  set ψ : Fin m → ℝ → ℝ := fun i t => a i + ∫ v in (0:ℝ)..t, G v i with hψ
  set Φ : ℝ → ℝ := fun t => ∑ i, (ψ i t) ^ 2 with hΦ
  set Ψ : ℝ → ℝ := fun t => Real.exp (-(2 * c) * t) * (1 + Φ t) with hΨ
  have h0mem : (0 : ℝ) ∈ uIcc (0 : ℝ) T := by simp [uIcc_of_le hT.le, hT.le]
  have hACψ : ∀ i, AbsolutelyContinuousOnInterval (ψ i) 0 T := fun i =>
    ((contDiffOn_const (c := a i) (n := 1) (s := uIcc (0:ℝ) T)).absolutelyContinuousOnInterval).fun_add
      ((hG i).absolutelyContinuousOnInterval_intervalIntegral h0mem)
  have hACΦ : AbsolutelyContinuousOnInterval Φ 0 T :=
    ekv_ac_sum Finset.univ (fun i t => (ψ i t) ^ 2) (fun i _ => by
      have := (hACψ i).fun_mul (hACψ i)
      simpa [sq] using this)
  have hACe : AbsolutelyContinuousOnInterval (fun t => Real.exp (-(2 * c) * t)) 0 T :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffOn.absolutelyContinuousOnInterval
  have hACΨ : AbsolutelyContinuousOnInterval Ψ 0 T :=
    hACe.fun_mul ((contDiffOn_const (c := (1 : ℝ)) (n := 1) (s := uIcc (0:ℝ) T)).absolutelyContinuousOnInterval.fun_add hACΦ)
  have hder : ∀ᵐ s : ℝ, s ∈ uIcc (0 : ℝ) T → ∀ i,
      HasDerivAt (fun t => ∫ v in (0:ℝ)..t, G v i) (G s i) s := by
    have h1 : ∀ i, ∀ᵐ s : ℝ, s ∈ uIcc (0:ℝ) T →
        HasDerivAt (fun t => ∫ v in (0:ℝ)..t, G v i) (G s i) s := fun i => by
      filter_upwards [(hG i).ae_hasDerivAt_integral] with s hs hmem using hs hmem 0 h0mem
    filter_upwards [ae_all_iff.2 h1] with s hs hmem i using hs i hmem
  have hΨder : ∀ᵐ s : ℝ, s ∈ uIcc (0:ℝ) T → deriv Ψ s ≤ 0 := by
    filter_upwards [hder] with s hs hmem
    have hs' := hs hmem
    have hsI : s ∈ Set.Icc (0:ℝ) T := by rwa [uIcc_of_le hT.le] at hmem
    have hψd : ∀ i, HasDerivAt (ψ i) (G s i) s := fun i => (hs' i).const_add (a i)
    have hΦd : HasDerivAt Φ (∑ i, 2 * ψ i s * G s i) s := by
      have := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hψd i).pow 2)
      simpa using this
    have hed : HasDerivAt (fun t => Real.exp (-(2 * c) * t))
        (Real.exp (-(2 * c) * s) * (-(2 * c))) s := by
      have := ((hasDerivAt_id s).const_mul (-(2*c))).exp
      simpa using this
    have hΨd : HasDerivAt Ψ (Real.exp (-(2 * c) * s) * (-(2 * c)) * (1 + Φ s) +
        Real.exp (-(2 * c) * s) * (∑ i, 2 * ψ i s * G s i)) s := hed.mul (hΦd.const_add 1)
    rw [hΨd.deriv]
    have h1 := hineq s hsI
    have hS : ∑ i, 2 * ψ i s * G s i = 2 * ∑ i, ψ i s * G s i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have hle : ∑ i, 2 * ψ i s * G s i ≤ 2 * c * (1 + Φ s) := by
      rw [hS]
      have : ∑ i, ψ i s * G s i ≤ c * (1 + Φ s) := h1
      linarith
    have hexp := Real.exp_pos (-(2 * c) * s)
    have h3 : 0 ≤ Real.exp (-(2 * c) * s) * (2 * c * (1 + Φ s) - ∑ i, 2 * ψ i s * G s i) :=
      mul_nonneg hexp.le (sub_nonneg.2 hle)
    nlinarith [h3]
  intro t ht
  have hsub : uIcc (0:ℝ) t ⊆ uIcc (0:ℝ) T := by
    rw [uIcc_of_le ht.1, uIcc_of_le hT.le]; exact Icc_subset_Icc le_rfl ht.2
  have hmono : AbsolutelyContinuousOnInterval Ψ 0 t := hACΨ.mono hsub
  have hFTC := hmono.integral_deriv_eq_sub
  have hnonpos : ∫ x in (0:ℝ)..t, deriv Ψ x ≤ 0 := by
    have hint := hmono.intervalIntegrable_deriv
    have h0 : 0 ≤ ∫ x in (0:ℝ)..t, -deriv Ψ x := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict ht.1
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hΨder] with s hs hmem
      have := hs (by rw [uIcc_of_le hT.le]; exact ⟨hmem.1, hmem.2.trans ht.2⟩)
      simp only [Pi.zero_apply, Pi.neg_apply]
      linarith
    rw [intervalIntegral.integral_neg] at h0
    linarith
  have hle : Ψ t ≤ Ψ 0 := by linarith
  have hΨ0 : Ψ 0 = 1 + ∑ i, a i ^ 2 := by
    simp [hΨ, hΦ, hψ]
  rw [hΨ0] at hle
  have hΨt : Ψ t = Real.exp (-(2 * c) * t) * (1 + Φ t) := rfl
  have hexp : 0 < Real.exp (2 * c * t) := Real.exp_pos _
  calc 1 + ∑ i, (a i + ∫ v in (0:ℝ)..t, G v i) ^ 2 = 1 + Φ t := rfl
    _ = Real.exp (2 * c * t) * Ψ t := by
        rw [hΨt, ← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (2 * c * t) * (1 + ∑ i, a i ^ 2) := mul_le_mul_of_nonneg_left hle hexp.le

theorem solution {n : ℕ} {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K]
    (T : ℝ) (hT : 0 < T) (x₀ : EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → K → ℝ → EuclideanSpace ℝ (Fin n))
    (hf : ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) × K × ℝ => f z.1 z.2.1 z.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc 0 T))
    (c : ℝ) (hc : ∀ (x : EuclideanSpace ℝ (Fin n)) (u : K), ∀ t ∈ Set.Icc 0 T,
      inner ℝ x (f x u t) ≤ c * (1 + ‖x‖ ^ 2))
    (u : ℝ → K) (hu : Measurable u) (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hx : IsTrajectory f x₀ T u x) :
    ∀ t ∈ Set.Icc 0 T, ‖x t‖ ^ 2 ≤ (‖x₀‖ ^ 2 + 2 * c * T) * Real.exp (2 * c * T) := by
  obtain ⟨hxc, hxeq⟩ := hx
  obtain ⟨g, hgm, hgeq, M, hM⟩ := ekv_meas_bdd T hT f hf u hu x hxc
  have hintg : IntervalIntegrable g volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    refine Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
      hgm.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => hM s (Ioc_subset_Icc_self hs)
  have hint : ∀ i : Fin n, IntervalIntegrable (fun s => g s i) volume 0 T := by
    intro i
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    refine Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne ?_ ?_
    · exact ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.measurable.comp
        hgm).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
      calc ‖g s i‖ ≤ ‖g s‖ := PiLp.norm_apply_le (g s) i
        _ ≤ M := hM s (Ioc_subset_Icc_self hs)
  have hxg : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ i, x t i = x₀ i + ∫ v in (0:ℝ)..t, g v i := by
    intro t ht i
    rw [hxeq t ht]
    have hsub : uIcc (0:ℝ) t ⊆ Set.Icc (0:ℝ) T := by
      rw [uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2
    have hcongr : ∫ s in (0:ℝ)..t, f (x s) (u s) s = ∫ s in (0:ℝ)..t, g s :=
      intervalIntegral.integral_congr (fun s hs => (hgeq s (hsub hs)).symm)
    rw [hcongr]
    have hit : IntervalIntegrable g volume 0 t :=
      hintg.mono_set (by rw [uIcc_of_le ht.1, uIcc_of_le hT.le]; exact Set.Icc_subset_Icc le_rfl ht.2)
    have := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).intervalIntegral_comp_comm hit
    change ∫ s in (0:ℝ)..t, g s i = (∫ s in (0:ℝ)..t, g s) i at this
    rw [PiLp.add_apply, this]
  have hc0 : 0 ≤ c := by
    have := hc 0 (u 0) 0 ⟨le_rfl, hT.le⟩
    simpa using this
  have hineq : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∑ i, (x₀ i + ∫ v in (0:ℝ)..s, g v i) * g s i ≤
        c * (1 + ∑ i, (x₀ i + ∫ v in (0:ℝ)..s, g v i) ^ 2) := by
    intro s hs
    have e : ∀ i, x₀ i + ∫ v in (0:ℝ)..s, g v i = x s i := fun i => (hxg s hs i).symm
    simp only [e]
    have h1 := hc (x s) (u s) s hs
    rw [← hgeq s hs] at h1
    rw [EuclideanSpace.real_norm_sq_eq] at h1
    simpa [PiLp.inner_apply, mul_comm] using h1
  have hG := ekv_gron T c hT (fun i => x₀ i) (fun s i => g s i) hint hineq
  intro t ht
  have h1 := hG t ht
  have e : ∀ i, x₀ i + ∫ v in (0:ℝ)..t, g v i = x t i := fun i => (hxg t ht i).symm
  simp only [e] at h1
  rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq] at h1
  set y := 2 * c * T with hy
  have hy0 : 0 ≤ y := by positivity
  have hA : 0 ≤ ‖x₀‖ ^ 2 := by positivity
  have hEt : Real.exp (2 * c * t) ≤ Real.exp y :=
    Real.exp_le_exp.2 (by nlinarith [ht.2])
  have hkey : (1 - y) * Real.exp y ≤ 1 := by
    have h2 := Real.add_one_le_exp (-y)
    have h3 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
    have h4 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos y).le
    nlinarith [h3, h4]
  have h5 : Real.exp (2 * c * t) * (1 + ‖x₀‖ ^ 2) ≤ Real.exp y * (1 + ‖x₀‖ ^ 2) :=
    mul_le_mul_of_nonneg_right hEt (by positivity)
  nlinarith [h1, h5, hkey]
