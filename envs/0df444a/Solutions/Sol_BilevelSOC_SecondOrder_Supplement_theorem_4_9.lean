-- Prove2me | solution 1 for BilevelSOC.SecondOrder.Supplement.theorem_4_9
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:41:08.131096+00:00
-- url     : https://prove2.me/submissions/47253d3e-ea44-451c-a6d1-dca80553f6e8

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_FirstOrder
open scoped Topology

open BilevelSOC
open BilevelSOC.SecondOrder
open BilevelSOC.SecondOrder.Supplement

theorem solution {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m)
    (U : Set (E n)) (s : E n → Y m) (s' : E n → Y m)
    (hStanding : Standing D) (hfeas : z ∈ feasSet D)
    (hU : IsOpen U) (hxU : z.1 ∈ U)
    (hs : ∀ x ∈ U, solMap D x = {s x})
    (hLip : ∀ x ∈ U, LocallyLipschitzAt s x)
    (hDir : ∀ x ∈ U, ∀ d, ∃ v, HasVectorDirDerivAt s x d v)
    (hs' : ∀ d, HasVectorDirDerivAt s z.1 d (s' d))
    (hexclude : ∀ dx, fderiv ℝ D.F z (dx, s' dx) ≤ 0 →
      (∀ i ∈ actG D z, fderiv ℝ (D.G i) z (dx, s' dx) ≤ 0) → dx = 0) :
    StrictLocalMin D.F (feasSet D) z := by
      classical
      obtain ⟨hF, hf, hG, hg⟩ := hStanding
      have hsx : ∀ x ∈ U, ∀ y, y ∈ solMap D x → y = s x := by
        intro x hx y hy
        rw [hs x hx] at hy
        exact hy
      have hz2 : z.2 = s z.1 := hsx z.1 hxU z.2 hfeas.2
      by_contra hnot
      have hfreq : ∃ᶠ a in 𝓝 z, a ∈ feasSet D ∧ a ≠ z ∧ D.F a ≤ D.F z := by
        intro hev
        apply hnot
        refine ⟨hfeas, _, hev, ?_⟩
        rintro a ⟨haX, haU⟩ hne
        by_contra hlt
        exact haU ⟨haX, hne, not_lt.mp hlt⟩
      have hUev : ∀ᶠ a : E n × Y m in 𝓝 z, a.1 ∈ U :=
        (continuous_fst.tendsto z).eventually (hU.mem_nhds hxU)
      obtain ⟨a, ha, hap⟩ := Filter.exists_seq_forall_of_frequently (hfreq.and_eventually hUev)
      have ha2 : ∀ k, (a k).2 = s (a k).1 := fun k => hsx _ (hap k).2 _ (hap k).1.1.2
      have hne : ∀ k, (a k).1 - z.1 ≠ 0 := by
        intro k h
        have h1 : (a k).1 = z.1 := sub_eq_zero.mp h
        apply (hap k).1.2.1
        exact Prod.ext h1 (by rw [ha2 k, h1, hz2])
      have hpos : ∀ k, 0 < ‖(a k).1 - z.1‖ := fun k => norm_pos_iff.mpr (hne k)
      have ha1 : Filter.Tendsto (fun k => (a k).1) Filter.atTop (𝓝 z.1) :=
        (continuous_fst.tendsto z).comp ha
      have hsph : ∀ k, ‖(a k).1 - z.1‖⁻¹ • ((a k).1 - z.1) ∈ Metric.sphere (0 : E n) 1 := by
        intro k
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (hpos k).ne']
      obtain ⟨d, hd, φ, hφ, hdlim⟩ := (isCompact_sphere (0 : E n) 1).tendsto_subseq hsph
      have hdne : d ≠ 0 := by
        rintro rfl
        simp at hd
      -- abbreviations along the subsequence
      obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, t = fun k => ‖(a (φ k)).1 - z.1‖ := ⟨_, rfl⟩
      obtain ⟨e, he⟩ : ∃ e : ℕ → E n, e = fun k => (t k)⁻¹ • ((a (φ k)).1 - z.1) := ⟨_, rfl⟩
      have htpos : ∀ k, 0 < t k := fun k => by rw [ht]; exact hpos _
      have ha1φ : Filter.Tendsto (fun k => (a (φ k)).1) Filter.atTop (𝓝 z.1) :=
        ha1.comp hφ.tendsto_atTop
      have ht0 : Filter.Tendsto t Filter.atTop (𝓝 0) := by
        rw [ht]
        have := (ha1φ.sub_const z.1).norm
        simpa using this
      have ht0' : Filter.Tendsto t Filter.atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.mpr ⟨ht0, Filter.Eventually.of_forall htpos⟩
      have helim : Filter.Tendsto e Filter.atTop (𝓝 d) := by
        rw [he, ht]
        exact hdlim
      have hxe : ∀ k, (a (φ k)).1 = z.1 + t k • e k := by
        intro k
        rw [he]
        simp only
        rw [smul_smul, mul_inv_cancel₀ (htpos k).ne', one_smul, add_sub_cancel]
      -- the directional quotient of `s`
      have hsdir : Filter.Tendsto (fun k => (t k)⁻¹ • (s (z.1 + t k • d) - s z.1)) Filter.atTop
          (𝓝 (s' d)) := (hs' d).comp ht0'
      obtain ⟨V, hV, K, hK⟩ := hLip z.1 hxU
      have hdV : ∀ᶠ k in Filter.atTop, z.1 + t k • d ∈ V := by
        have h : Filter.Tendsto (fun k => z.1 + t k • d) Filter.atTop (𝓝 z.1) := by
          have := (ht0.smul_const d).const_add z.1
          simpa using this
        exact h hV
      have heV : ∀ᶠ k in Filter.atTop, (a (φ k)).1 ∈ V := ha1φ hV
      have hdiff : Filter.Tendsto
          (fun k => (t k)⁻¹ • (s (a (φ k)).1 - s (z.1 + t k • d))) Filter.atTop (𝓝 0) := by
        have hb : Filter.Tendsto (fun k => (K : ℝ) * ‖e k - d‖) Filter.atTop (𝓝 0) := by
          have := ((helim.sub_const d).norm).const_mul (K : ℝ)
          simpa using this
        refine squeeze_zero_norm' ?_ hb
        filter_upwards [hdV, heV] with k h1 h2
        have h3 := hK.norm_sub_le h2 h1
        have h4 : (a (φ k)).1 - (z.1 + t k • d) = t k • (e k - d) := by
          rw [hxe k, smul_sub]; abel
        rw [h4, norm_smul, Real.norm_of_nonneg (htpos k).le] at h3
        rw [norm_smul, norm_inv, Real.norm_of_nonneg (htpos k).le]
        calc (t k)⁻¹ * ‖s (a (φ k)).1 - s (z.1 + t k • d)‖
            ≤ (t k)⁻¹ * (K * (t k * ‖e k - d‖)) :=
              mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr (htpos k).le)
          _ = K * ‖e k - d‖ := by
              have := (htpos k).ne'
              field_simp
      have hsq : Filter.Tendsto (fun k => (t k)⁻¹ • (s (a (φ k)).1 - s z.1)) Filter.atTop
          (𝓝 (s' d)) := by
        have := hdiff.add hsdir
        rw [zero_add] at this
        refine this.congr (fun k => ?_)
        rw [← smul_add, sub_add_sub_cancel]
      have hq : Filter.Tendsto (fun k => (t k)⁻¹ • (a (φ k) - z)) Filter.atTop (𝓝 (d, s' d)) := by
        refine (helim.prodMk_nhds hsq).congr (fun k => ?_)
        rw [he]
        refine Prod.ext rfl ?_
        simp only [Prod.smul_snd, Prod.snd_sub]
        rw [ha2, hz2]
      have hsub0 : Filter.Tendsto (fun k => a (φ k) - z) Filter.atTop (𝓝 0) := by
        have := (ha.comp hφ.tendsto_atTop).sub_const z
        simpa using this
      -- key derivative claim
      have key : ∀ h : E n × Y m → ℝ, ContDiff ℝ 2 h → (∀ k, h (a (φ k)) ≤ h z) →
          fderiv ℝ h z (d, s' d) ≤ 0 := by
        intro h hh hle
        have hd1 : HasFDerivAt h (fderiv ℝ h z) z :=
          ((hh.differentiable (by norm_num)) z).hasFDerivAt
        have hlim := (hd1.hasFDerivWithinAt (s := Set.univ)).lim
          (c := fun k => (t k)⁻¹) (d := fun k => a (φ k) - z) (v := (d, s' d))
          hsub0 (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hq
        refine le_of_tendsto hlim (Filter.Eventually.of_forall fun k => ?_)
        simp only [add_sub_cancel, smul_eq_mul]
        exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (htpos k).le)
          (sub_nonpos.mpr (hle k))
      apply hdne
      apply hexclude d
      · exact key D.F hF (fun k => (hap (φ k)).1.2.2)
      · intro i hi
        refine key (D.G i) (hG i) (fun k => ?_)
        have hi0 : D.G i z = 0 := hi
        rw [hi0]
        exact (hap (φ k)).1.1.1 i
