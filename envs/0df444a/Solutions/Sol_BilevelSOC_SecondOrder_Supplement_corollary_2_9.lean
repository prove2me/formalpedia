-- Prove2me | solution 1 for BilevelSOC.SecondOrder.Supplement.corollary_2_9
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:40:28.894403+00:00
-- url     : https://prove2.me/submissions/19dda622-f018-4ca5-a283-255cc5d1a2dc

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_FirstOrder
open scoped Topology

open BilevelSOC
open BilevelSOC.SecondOrder
open BilevelSOC.SecondOrder.Supplement

theorem solution {n k : ℕ} (θ : E n → EReal) (c : Fin k → E n → EReal)
    (x : E n) (θstar : E n → EReal)
    (hfinite : ∃ v : ℝ, θ x = (v : EReal))
    (hfeas : ∀ i, c i x ≤ 0)
    (hclosed : IsClosed {a | ∀ i, c i a ≤ 0})
    (hLip : ∀ i, ELocallyLipschitzAt (c i) x)
    (hHad : ∀ d, HasEHadamardDirDerivAt θ x d (θstar d))
    (hexclude : ∀ d, θstar d ≤ 0 →
      (∀ i, c i x = 0 → lowerDini (c i) x d ≤ 0) → d = 0) :
    EGrowthCondition θ {a | ∀ i, c i a ≤ 0} x := by
      classical
      obtain ⟨v, hv⟩ := hfinite
      have key : ∀ (z : EReal) (s C : ℝ), 0 < s → z < (v : EReal) + ((C * s : ℝ) : EReal) →
          ((s⁻¹ : ℝ) : EReal) * (z - (v : EReal)) ≤ (C : EReal) := by
        intro z s C hs hz
        induction z using EReal.rec with
        | bot => simp [EReal.coe_mul_bot_of_pos (inv_pos.mpr hs)]
        | top => exact absurd hz (by rw [← EReal.coe_add]; exact not_lt.mpr le_top)
        | coe r =>
          rw [← EReal.coe_add] at hz
          have hz' : r < v + C * s := EReal.coe_lt_coe_iff.mp hz
          rw [← EReal.coe_sub, ← EReal.coe_mul]
          apply EReal.coe_le_coe_iff.mpr
          rw [← div_eq_inv_mul, div_le_iff₀ hs]; linarith
      refine ⟨hfeas, ?_⟩
      by_contra hcon
      push_neg at hcon
      have hseq : ∀ k : ℕ, ∃ a : E n, (∀ i, c i a ≤ 0) ∧ dist a x < 1 / ((k:ℝ)+1) ∧
          θ a < θ x + (((1 / ((k:ℝ)+1)) * ‖a - x‖ : ℝ) : EReal) := by
        intro k
        have hk : (0:ℝ) < 1 / ((k:ℝ)+1) := by positivity
        obtain ⟨a, ⟨haX, haU⟩, ha⟩ :=
          hcon (Metric.ball x (1 / ((k:ℝ)+1))) (Metric.ball_mem_nhds _ hk) _ hk
        exact ⟨a, haX, haU, ha⟩
      choose a haX hadist haθ using hseq
      have hane : ∀ k, a k ≠ x := by
        intro k h
        have := haθ k
        rw [h, sub_self, norm_zero, mul_zero, EReal.coe_zero, add_zero] at this
        exact lt_irrefl _ this
      set t : ℕ → ℝ := fun k => ‖a k - x‖ with ht
      have htpos : ∀ k, 0 < t k := fun k => norm_pos_iff.mpr (sub_ne_zero.mpr (hane k))
      set dd : ℕ → E n := fun k => (t k)⁻¹ • (a k - x) with hdd
      have hdd_mem : ∀ k, dd k ∈ Metric.sphere (0 : E n) 1 := by
        intro k
        simp only [mem_sphere_zero_iff_norm, hdd, norm_smul, norm_inv, Real.norm_eq_abs,
          abs_of_pos (htpos k)]
        exact inv_mul_cancel₀ (htpos k).ne'
      have hak : ∀ k, x + t k • dd k = a k := by
        intro k
        simp only [hdd, smul_smul, mul_inv_cancel₀ (htpos k).ne', one_smul]
        abel
      obtain ⟨d, hdS, φ, hφ, hφlim⟩ := (isCompact_sphere (0 : E n) 1).tendsto_subseq hdd_mem
      have hd0 : d ≠ 0 := by
        intro h; rw [h] at hdS; simp at hdS
      have hinv : Filter.Tendsto (fun k : ℕ => 1 / ((k:ℝ)+1)) Filter.atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hinvφ : Filter.Tendsto (fun k : ℕ => 1 / ((φ k:ℝ)+1)) Filter.atTop (𝓝 0) :=
        hinv.comp hφ.tendsto_atTop
      have ht0 : Filter.Tendsto (fun k => t (φ k)) Filter.atTop (𝓝 0) := by
        refine squeeze_zero (fun k => (htpos _).le) (fun k => ?_) hinvφ
        have := (hadist (φ k)).le
        rw [dist_eq_norm] at this
        exact this
      have htlim : Filter.Tendsto (fun k => t (φ k)) Filter.atTop (𝓝[>] 0) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨ht0, Filter.Eventually.of_forall (fun k => htpos (φ k))⟩
      have hprod : Filter.Tendsto (fun k => (t (φ k), dd (φ k))) Filter.atTop
          ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 d) :=
        htlim.prodMk hφlim
      have hθlim := (hHad d).comp hprod
      have hθle : θstar d ≤ 0 := by
        have h2 : Filter.Tendsto (fun k : ℕ => ((1 / ((φ k:ℝ)+1) : ℝ) : EReal)) Filter.atTop
            (𝓝 ((0:ℝ) : EReal)) :=
          (continuous_coe_real_ereal.tendsto 0).comp hinvφ
        have := le_of_tendsto_of_tendsto' hθlim h2 (fun k => ?_)
        · simpa using this
        simp only [Function.comp, dirQuot]
        rw [hak, hv]
        have := haθ (φ k)
        rw [hv] at this
        exact key _ _ _ (htpos _) this
      have hcons : ∀ i, c i x = 0 → lowerDini (c i) x d ≤ 0 := by
        intro i hi0
        obtain ⟨r, U, hU, hcr, K, hK⟩ := hLip i
        have hxU : x ∈ U := mem_of_mem_nhds hU
        have h1 : Filter.Tendsto (fun k => x + t (φ k) • d) Filter.atTop (𝓝 x) := by
          have : Filter.Tendsto (fun k => x + t (φ k) • d) Filter.atTop (𝓝 (x + (0:ℝ) • d)) :=
            tendsto_const_nhds.add (ht0.smul_const d)
          simpa using this
        have h2 : Filter.Tendsto (fun k => a (φ k)) Filter.atTop (𝓝 x) := by
          have : Filter.Tendsto (fun k => x + t (φ k) • dd (φ k)) Filter.atTop
              (𝓝 (x + (0:ℝ) • d)) :=
            tendsto_const_nhds.add (ht0.smul hφlim)
          simp only [hak, zero_smul, add_zero] at this
          exact this
        have hbd : Filter.Tendsto (fun k => (K : ℝ) * ‖dd (φ k) - d‖) Filter.atTop (𝓝 0) := by
          have := (tendsto_iff_norm_sub_tendsto_zero.mp hφlim).const_mul (K : ℝ)
          simpa using this
        have hev : ∀ᶠ k in Filter.atTop,
            dirQuot (c i) x d (t (φ k)) ≤ (((K : ℝ) * ‖dd (φ k) - d‖ : ℝ) : EReal) := by
          filter_upwards [h1 hU, h2 hU] with k hk1 hk2
          have hpU : x + t (φ k) • d ∈ U := hk1
          have haU : a (φ k) ∈ U := hk2
          have hra : r (a (φ k)) ≤ 0 := by
            have h := haX (φ k) i
            rw [hcr _ haU] at h
            exact_mod_cast h
          have hlip := hK.dist_le_mul _ hpU _ haU
          have hdist : dist (x + t (φ k) • d) (a (φ k)) = t (φ k) * ‖dd (φ k) - d‖ := by
            rw [← hak (φ k), dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
              Real.norm_eq_abs, abs_of_pos (htpos _), norm_sub_rev]
          rw [hdist] at hlip
          have hle : r (x + t (φ k) • d) ≤ K * (t (φ k) * ‖dd (φ k) - d‖) := by
            have := (abs_le.mp ((Real.dist_eq _ _) ▸ hlip)).2
            linarith
          simp only [dirQuot]
          rw [hcr _ hpU, hi0, sub_zero, ← EReal.coe_mul]
          apply EReal.coe_le_coe_iff.mpr
          rw [← div_eq_inv_mul, div_le_iff₀ (htpos _)]
          nlinarith
        by_contra hneg
        push_neg at hneg
        obtain ⟨ε, h0ε, hε⟩ := EReal.lt_iff_exists_real_btwn.mp hneg
        have hε0 : (0:ℝ) < ε := by exact_mod_cast h0ε
        have hev2 : ∀ᶠ k in Filter.atTop, dirQuot (c i) x d (t (φ k)) ≤ (ε : EReal) := by
          filter_upwards [hev, hbd.eventually (gt_mem_nhds hε0)] with k hk1 hk2
          exact hk1.trans (EReal.coe_le_coe_iff.mpr hk2.le)
        have hfr : ∃ᶠ s in 𝓝[>] (0:ℝ), dirQuot (c i) x d s ≤ (ε : EReal) :=
          htlim.frequently (p := fun s => dirQuot (c i) x d s ≤ (ε : EReal)) hev2.frequently
        have := Filter.liminf_le_of_frequently_le' hfr
        exact absurd (lt_of_le_of_lt this hε) (lt_irrefl _)
      exact hd0 (hexclude d hθle hcons)
