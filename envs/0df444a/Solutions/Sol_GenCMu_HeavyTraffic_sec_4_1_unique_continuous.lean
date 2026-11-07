-- Prove2me | solution 1 for GenCMu.HeavyTraffic.sec_4_1_unique_continuous
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T06:54:40.616976+00:00
-- url     : https://prove2.me/submissions/56d1f987-da96-4492-bf93-056630e2e3c6

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model
import Definitions.Def_GenCMu_HeavyTraffic_Sequence
import Definitions.Def_GenCMu_HeavyTraffic_Limits

open Filter Topology Finset GenCMu.HeavyTraffic

theorem solution {d : ℕ} (hd : 0 < d) (lam rho : ℝ → Fin d → ℝ)
    (Cs : Fin d → ℝ → ℝ)
    (hlam_cont : ContinuousOn lam (Set.Icc 0 1)) (hrho_cont : ContinuousOn rho (Set.Icc 0 1))
    (hlam : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ k, 0 < lam t k)
    (hrho : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ k, 0 < rho t k)
    (hstrict : ∀ k, StrictConvexOn ℝ (Set.Ici 0) (Cs k))
    (hcont : ∀ k, ContinuousOn (Cs k) (Set.Ici 0))
    (hmono : ∀ k, MonotoneOn (Cs k) (Set.Ici 0))
    (y : ℝ → ℝ) (hy : ContinuousOn y (Set.Icc 0 1)) (hy0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ y t) :
    ∃ G : ℝ → Fin d → ℝ, ContinuousOn G (Set.Icc 0 1) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, IsMin43 (lam t) (rho t) Cs (y t) (G t) ∧
        ∀ x : Fin d → ℝ, IsMin43 (lam t) (rho t) Cs (y t) x → x = G t := by
  classical
  set K := Set.Icc (0 : ℝ) 1 with hK
  set P : Set (Fin d → ℝ) := {x | ∀ k, 0 ≤ x k} with hP
  -- joint continuity of the objective
  have hA : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => obj43 (lam p.1) (rho p.1) Cs p.2)
      (K ×ˢ P) := by
    unfold obj43
    refine continuousOn_finsetSum _ fun k _ => ?_
    have hfst : Set.MapsTo Prod.fst (K ×ˢ P) K := fun p hp => hp.1
    have hlk : ContinuousOn (fun t => lam t k) K := (continuous_apply k).comp_continuousOn hlam_cont
    have hrk : ContinuousOn (fun t => rho t k) K := (continuous_apply k).comp_continuousOn hrho_cont
    have hin : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => p.2 k / rho p.1 k) (K ×ˢ P) :=
      ((continuous_apply k).comp continuous_snd).continuousOn.div
        (hrk.comp continuous_fst.continuousOn hfst) (fun p hp => ne_of_gt (hrho p.1 hp.1 k))
    exact (hlk.comp continuous_fst.continuousOn hfst).mul
      ((hcont k).comp hin (fun p hp => div_nonneg (hp.2 k) (hrho p.1 hp.1 k).le))
  -- existence
  have hex : ∀ t ∈ K, ∃ x, IsMin43 (lam t) (rho t) Cs (y t) x := by
    intro t ht
    set Ω : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Set.Icc 0 (y t)) ∩ {x | ∑ k, x k = y t}
    have hΩc : IsCompact Ω := (isCompact_univ_pi fun _ => isCompact_Icc).inter_right
      (isClosed_eq (continuous_finsetSum _ fun k _ => continuous_apply k) continuous_const)
    have hΩmem : ∀ x : Fin d → ℝ, (∀ k, 0 ≤ x k) → ∑ k, x k = y t → x ∈ Ω := by
      intro x hx hs
      refine ⟨fun k _ => ⟨hx k, ?_⟩, hs⟩
      rw [← hs]; exact Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ k)
    have hne : Ω.Nonempty := by
      refine ⟨Pi.single ⟨0, hd⟩ (y t), hΩmem _ (fun k => ?_) ?_⟩
      · by_cases h : k = ⟨0, hd⟩
        · subst h; simp [hy0 t ht]
        · simp [Pi.single_apply, h]
      · simp
    have hcO : ContinuousOn (fun x => obj43 (lam t) (rho t) Cs x) Ω := by
      have := hA.comp (continuous_const.prodMk continuous_id).continuousOn
        (s := Ω) (fun x hx => ⟨ht, fun k => (hx.1 k (Set.mem_univ k)).1⟩)
      exact this
    obtain ⟨x0, hx0, hmin⟩ := hΩc.exists_isMinOn hne hcO
    refine ⟨x0, fun k => (hx0.1 k (Set.mem_univ k)).1, hx0.2, fun x' hx' hs' => ?_⟩
    exact hmin (hΩmem x' hx' hs')
  -- uniqueness
  have huniq : ∀ t ∈ K, ∀ x x', IsMin43 (lam t) (rho t) Cs (y t) x →
      IsMin43 (lam t) (rho t) Cs (y t) x' → x = x' := by
    intro t ht x x' hx hx'
    by_contra hne
    obtain ⟨k0, hk0⟩ : ∃ k, x k ≠ x' k := by
      by_contra h; push Not at h; exact hne (funext h)
    set m : Fin d → ℝ := fun k => (1 / 2 : ℝ) * x k + (1 / 2 : ℝ) * x' k
    have hm0 : ∀ k, 0 ≤ m k := fun k => by
      have := hx.1 k; have := hx'.1 k; simp only [m]; positivity
    have hms : ∑ k, m k = y t := by
      simp only [m, Finset.sum_add_distrib, ← Finset.mul_sum, hx.2.1, hx'.2.1]; ring
    have h1 := hx.2.2 m hm0 hms
    have h2 := hx'.2.2 x hx.1 hx.2.1
    unfold obj43 at h1 h2
    have hlt : ∑ k, lam t k * Cs k (m k / rho t k) <
        ∑ k, ((1 / 2 : ℝ) * (lam t k * Cs k (x k / rho t k)) +
          (1 / 2 : ℝ) * (lam t k * Cs k (x' k / rho t k))) := by
      have key : ∀ k, x k ≠ x' k → Cs k (m k / rho t k) <
          (1 / 2 : ℝ) * Cs k (x k / rho t k) + (1 / 2 : ℝ) * Cs k (x' k / rho t k) := by
        intro k hk
        have hr := hrho t ht k
        have := (hstrict k).2 (Set.mem_Ici.mpr (div_nonneg (hx.1 k) hr.le))
          (Set.mem_Ici.mpr (div_nonneg (hx'.1 k) hr.le))
          (fun h => hk (by field_simp at h; linarith)) (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
        simp only [smul_eq_mul] at this
        have e : m k / rho t k = 1 / 2 * (x k / rho t k) + 1 / 2 * (x' k / rho t k) := by
          simp only [m]; field_simp
        rw [e]; exact this
      have keyle : ∀ k, Cs k (m k / rho t k) ≤
          (1 / 2 : ℝ) * Cs k (x k / rho t k) + (1 / 2 : ℝ) * Cs k (x' k / rho t k) := by
        intro k
        by_cases hk : x k = x' k
        · have e : m k = x k := by simp only [m]; rw [← hk]; ring
          rw [e, ← hk]; ring_nf; exact le_rfl
        · exact (key k hk).le
      apply Finset.sum_lt_sum
      · intro k _
        have := mul_le_mul_of_nonneg_left (keyle k) (hlam t ht k).le
        linarith
      · refine ⟨k0, Finset.mem_univ _, ?_⟩
        have := mul_lt_mul_of_pos_left (key k0 hk0) (hlam t ht k0)
        linarith
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hlt
    have h3 := hx.2.2 x' hx'.1 hx'.2.1
    unfold obj43 at h3
    linarith
  -- the choice
  set G : ℝ → Fin d → ℝ := fun t =>
    if h : ∃ x, IsMin43 (lam t) (rho t) Cs (y t) x then h.choose else 0 with hG
  have hGmin : ∀ t ∈ K, IsMin43 (lam t) (rho t) Cs (y t) (G t) := by
    intro t ht
    have h := hex t ht
    simp only [hG, dif_pos h]
    exact h.choose_spec
  obtain ⟨Y, hY⟩ := isCompact_Icc.exists_bound_of_continuousOn hy
  have hY' : ∀ t ∈ K, y t ≤ Y := fun t ht => by
    have := hY t ht; rw [Real.norm_eq_abs] at this; exact (abs_le.mp this).2
  set B : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Set.Icc 0 Y)
  have hBc : IsCompact B := isCompact_univ_pi fun _ => isCompact_Icc
  have hGB : ∀ t ∈ K, G t ∈ B := by
    intro t ht k _
    have hm := hGmin t ht
    refine ⟨hm.1 k, ?_⟩
    have := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => hm.1 j)
      (Finset.mem_univ k)
    rw [hm.2.1] at this
    linarith [hY' t ht]
  refine ⟨G, ?_, fun t ht => ⟨hGmin t ht, fun x hx => huniq t ht x (G t) hx (hGmin t ht)⟩⟩
  -- continuity
  rw [Metric.continuousOn_iff]
  intro t0 ht0 ε hε
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ t ∈ K, dist t t0 < 1 / ((n : ℝ) + 1) ∧ ε ≤ dist (G t) (G t0) :=
    fun n => hcon _ (by positivity)
  choose ts htsK htsd htsε using hseq
  have hts : Tendsto ts atTop (𝓝 t0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => (htsd n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨xb, hxbB, φ, hφ, hlim⟩ := hBc.tendsto_subseq (fun n => hGB (ts n) (htsK n))
  have htsφ : Tendsto (ts ∘ φ) atTop (𝓝 t0) := hts.comp hφ.tendsto_atTop
  have hxb0 : ∀ k, 0 ≤ xb k := fun k => (hxbB k (Set.mem_univ k)).1
  have hyφ : Tendsto (fun n => y (ts (φ n))) atTop (𝓝 (y t0)) :=
    (hy t0 ht0).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨htsφ, Eventually.of_forall fun n => htsK (φ n)⟩)
  have hsumb : ∑ k, xb k = y t0 := by
    have h1 : Tendsto (fun n => ∑ k, G (ts (φ n)) k) atTop (𝓝 (∑ k, xb k)) :=
      ((continuous_finsetSum _ fun k _ => continuous_apply k).tendsto xb).comp hlim
    have h2 : (fun n => ∑ k, G (ts (φ n)) k) = fun n => y (ts (φ n)) :=
      funext fun n => (hGmin _ (htsK (φ n))).2.1
    rw [h2] at h1
    exact tendsto_nhds_unique h1 hyφ
  -- joint convergence helper
  have hjoint : ∀ (u : ℕ → Fin d → ℝ) (v : Fin d → ℝ), (∀ n, u n ∈ P) → v ∈ P →
      Tendsto u atTop (𝓝 v) →
      Tendsto (fun n => obj43 (lam (ts (φ n))) (rho (ts (φ n))) Cs (u n)) atTop
        (𝓝 (obj43 (lam t0) (rho t0) Cs v)) := by
    intro u v hu hv huv
    have := (hA (t0, v) ⟨ht0, hv⟩).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨htsφ.prodMk_nhds huv, Eventually.of_forall fun n => ⟨htsK (φ n), hu n⟩⟩)
    exact this
  have hxbmin : IsMin43 (lam t0) (rho t0) Cs (y t0) xb := by
    refine ⟨hxb0, hsumb, fun x' hx' hs' => ?_⟩
    rcases (hy0 t0 ht0).lt_or_eq with hpos | hzero
    · set u : ℕ → Fin d → ℝ := fun n => (y (ts (φ n)) / y t0) • x'
      have hu : ∀ n, u n ∈ P := fun n k => by
        simp only [u, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (div_nonneg (hy0 _ (htsK (φ n))) hpos.le) (hx' k)
      have hus : ∀ n, ∑ k, u n k = y (ts (φ n)) := fun n => by
        simp only [u, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hs']
        field_simp
      have hul : Tendsto u atTop (𝓝 x') := by
        have : Tendsto (fun n => y (ts (φ n)) / y t0) atTop (𝓝 1) := by
          have := hyφ.div_const (y t0)
          rwa [div_self hpos.ne'] at this
        have := this.smul_const x'
        simpa [u] using this
      have hle : ∀ n, obj43 (lam (ts (φ n))) (rho (ts (φ n))) Cs (G (ts (φ n))) ≤
          obj43 (lam (ts (φ n))) (rho (ts (φ n))) Cs (u n) := fun n =>
        (hGmin _ (htsK (φ n))).2.2 (u n) (hu n) (hus n)
      exact le_of_tendsto_of_tendsto' (hjoint (fun n => G (ts (φ n))) xb
        (fun n => (hGmin _ (htsK (φ n))).1) hxb0 hlim) (hjoint u x' hu hx' hul) hle
    · have hz : ∀ v : Fin d → ℝ, (∀ k, 0 ≤ v k) → ∑ k, v k = y t0 → v = 0 := by
        intro v hv hvs
        rw [← hzero] at hvs
        funext k
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hv j)).mp hvs k (Finset.mem_univ k)
      rw [hz xb hxb0 hsumb, hz x' hx' hs']
  have hxbG : xb = G t0 := huniq t0 ht0 xb (G t0) hxbmin (hGmin t0 ht0)
  have hdl : Tendsto (fun n => dist (G (ts (φ n))) (G t0)) atTop (𝓝 (dist xb (G t0))) :=
    (continuous_id.dist continuous_const).continuousAt.tendsto.comp hlim
  rw [hxbG, dist_self] at hdl
  have := ge_of_tendsto hdl (Eventually.of_forall fun n => htsε (φ n))
  linarith
