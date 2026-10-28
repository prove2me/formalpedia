-- Prove2me | solution 1 for ChanceStateCtrl.General.convex_subdiff_eq_clarke
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T22:16:40.656998+00:00
-- url     : https://prove2.me/submissions/4adf7e0b-e3a8-4575-911a-3b22c8ee5c36

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Pointwise

theorem solution {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (S : Set U) (hS_open : IsOpen S) (f : U → ℝ) (hf : ConvexOn ℝ S f) (u : U) (hu : u ∈ S)
    (hf_lip : ChanceStateCtrl.General.LocLipAt f u) :
    {x : StrongDual ℝ U | ∀ w ∈ S, f u + x (w - u) ≤ f w} =
      ChanceStateCtrl.General.clarkeSubdiff f u := by
  obtain ⟨K, T, hT, hK⟩ := hf_lip
  set F : Filter (U × ℝ) := 𝓝 u ×ˢ 𝓝[>] (0:ℝ) with hF
  set Q : U → U × ℝ → ℝ := fun h q => (f (q.1 + q.2 • h) - f q.1) / q.2 with hQ
  have hlim1 : ∀ h : U, Tendsto (fun q : U × ℝ => q.1 + q.2 • h) F (𝓝 u) := by
    intro h
    have hc : Continuous (fun q : U × ℝ => q.1 + q.2 • h) := by fun_prop
    have := hc.tendsto (u, 0)
    simp only [zero_smul, add_zero] at this
    refine this.mono_left ?_
    rw [hF, nhds_prod_eq]
    exact Filter.prod_mono le_rfl nhdsWithin_le_nhds
  have hlim0 : Tendsto (fun q : U × ℝ => q.1) F (𝓝 u) := tendsto_fst
  have hpos : ∀ᶠ q in F, 0 < q.2 :=
    (tendsto_snd (f := 𝓝 u)).eventually self_mem_nhdsWithin
  have hbd : ∀ h, ∀ᶠ q in F, |Q h q| ≤ K * ‖h‖ := by
    intro h
    filter_upwards [hlim0.eventually hT, (hlim1 h).eventually hT, hpos] with q h1 h2 h3
    have := hK.dist_le_mul _ h2 _ h1
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos h3] at this
    simp only [hQ]
    rw [abs_div, abs_of_pos h3, div_le_iff₀ h3]
    nlinarith
  have hcob : ∀ h, F.IsCoboundedUnder (· ≤ ·) (Q h) := fun h =>
    isCoboundedUnder_le_of_eventually_le F (x := -(K * ‖h‖))
      (by filter_upwards [hbd h] with q hq using neg_le_of_abs_le hq)
  have hbdd : ∀ h, F.IsBoundedUnder (· ≤ ·) (Q h) := fun h =>
    isBoundedUnder_of_eventually_le (a := K * ‖h‖)
      (by filter_upwards [hbd h] with q hq using le_of_abs_le hq)
  ext x
  simp only [Set.mem_setOf_eq, ChanceStateCtrl.General.clarkeSubdiff,
    ChanceStateCtrl.General.clarkeDir]
  constructor
  · intro hx h
    refine le_limsup_of_frequently_le ?_ (hbdd h)
    have htend : Tendsto (fun t : ℝ => (u, t)) (𝓝[>] (0:ℝ)) F :=
      tendsto_const_nhds.prodMk tendsto_id
    refine htend.frequently (Eventually.frequently ?_)
    have hc : Continuous (fun t : ℝ => u + t • h) := by fun_prop
    have h1 : ∀ᶠ t in 𝓝[>] (0:ℝ), u + t • h ∈ S := by
      have := hc.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact (this.mono_left nhdsWithin_le_nhds).eventually (hS_open.mem_nhds hu)
    filter_upwards [h1, self_mem_nhdsWithin] with t ht htpos
    have := hx _ ht
    simp only [add_sub_cancel_left, map_smul, smul_eq_mul] at this
    show x h ≤ (f (u + t • h) - f u) / t
    rw [le_div_iff₀ htpos]
    linarith
  · intro hx w hw
    set h := w - u
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem (hS_open.mem_nhds hu) hT)
    set ε := min 1 (r / (2 * (‖h‖ + 1))) with hε
    have hε0 : 0 < ε := lt_min one_pos (by positivity)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hεh : ε * ‖h‖ < r / 2 := by
      have : ε ≤ r / (2 * (‖h‖ + 1)) := min_le_right _ _
      calc ε * ‖h‖ ≤ r / (2 * (‖h‖ + 1)) * ‖h‖ := by gcongr
        _ < r / (2 * (‖h‖ + 1)) * (‖h‖ + 1) := by gcongr; linarith
        _ = r / 2 := by field_simp
    have hin : ∀ y, dist y u < r / 2 → ∀ s, 0 ≤ s → s ≤ ε → y + s • h ∈ S ∩ T := by
      intro y hy s hs hsε
      apply hball
      rw [Metric.mem_ball]
      calc dist (y + s • h) u ≤ dist y u + ‖s • h‖ := by
            rw [dist_eq_norm, dist_eq_norm]
            calc ‖y + s • h - u‖ = ‖(y - u) + s • h‖ := by congr 1; abel
              _ ≤ _ := norm_add_le _ _
        _ < r / 2 + r / 2 := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
            gcongr
            calc s * ‖h‖ ≤ ε * ‖h‖ := by gcongr
              _ < r / 2 := hεh
        _ = r := by ring
    set g : U × ℝ → ℝ := fun q => (f (q.1 + ε • h) - f q.1) / ε
    have hfc : ∀ y, dist y u < r → ContinuousAt f y := by
      intro y hy
      have hmem : T ∈ 𝓝 y := by
        refine mem_of_superset (Metric.isOpen_ball.mem_nhds hy) ?_
        intro z hz; exact (hball hz).2
      exact (hK.continuousOn.continuousAt hmem)
    have hgt : Tendsto g F (𝓝 ((f (u + ε • h) - f u) / ε)) := by
      have h1 : Tendsto (fun q : U × ℝ => q.1 + ε • h) F (𝓝 (u + ε • h)) :=
        hlim0.add_const _
      have hu1 : dist (u + ε • h) u < r := by
        have := hin u (by simp; positivity) ε hε0.le le_rfl
        exact hball |>.trans (fun _ h => h) |> fun _ => by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_pos hε0]; linarith
      have hu0 : dist u u < r := by simp [hr]
      exact (((hfc _ hu1).tendsto.comp h1).sub ((hfc _ hu0).tendsto.comp hlim0)).div_const ε
    have hle : Q h ≤ᶠ[F] g := by
      have hnear : ∀ᶠ q in F, dist q.1 u < r / 2 :=
        hlim0.eventually (Metric.ball_mem_nhds u (by positivity))
      have hsmall : ∀ᶠ q in F, q.2 < ε :=
        (tendsto_snd (f := 𝓝 u)).eventually
          (Ioo_mem_nhdsGT hε0 |> fun h => mem_of_superset h (fun t ht => ht.2))
      filter_upwards [hnear, hsmall, hpos] with q hq1 hq2 hq3
      have hA := (hin q.1 hq1 0 le_rfl hε0.le).1
      have hA' : q.1 ∈ S := by simpa using hA
      have hB := (hin q.1 hq1 ε hε0.le le_rfl).1
      have hconv := hf.2 hA' hB
        (show (0:ℝ) ≤ 1 - q.2 / ε by rw [sub_nonneg, div_le_one hε0]; exact hq2.le)
        (show (0:ℝ) ≤ q.2 / ε by positivity) (show 1 - q.2 / ε + q.2 / ε = 1 by ring)
      have hpt : (1 - q.2 / ε) • q.1 + (q.2 / ε) • (q.1 + ε • h) = q.1 + q.2 • h := by
        rw [smul_add, smul_smul, div_mul_cancel₀ _ hε0.ne', sub_smul, one_smul]; abel
      rw [hpt, smul_eq_mul, smul_eq_mul] at hconv
      simp only [hQ, g]
      rw [div_le_div_iff₀ hq3 hε0]
      have : f (q.1 + q.2 • h) - f q.1 ≤ q.2 / ε * (f (q.1 + ε • h) - f q.1) := by linarith
      calc (f (q.1 + q.2 • h) - f q.1) * ε ≤ q.2 / ε * (f (q.1 + ε • h) - f q.1) * ε := by
            gcongr
        _ = (f (q.1 + ε • h) - f q.1) * q.2 := by field_simp
    have hls : limsup (Q h) F ≤ (f (u + ε • h) - f u) / ε := by
      rw [← hgt.limsup_eq]
      exact limsup_le_limsup hle (hcob h) hgt.isBoundedUnder_le
    have hconv := hf.2 hu hw (show (0:ℝ) ≤ 1 - ε by linarith) hε0.le
      (show 1 - ε + ε = 1 by ring)
    have hpt : (1 - ε) • u + ε • w = u + ε • h := by
      simp only [h, smul_sub, sub_smul, one_smul]; abel
    rw [hpt, smul_eq_mul, smul_eq_mul] at hconv
    have h1 : (f (u + ε • h) - f u) / ε ≤ f w - f u := by
      rw [div_le_iff₀ hε0]; linarith
    have := (hx h).trans (hls.trans h1)
    linarith
