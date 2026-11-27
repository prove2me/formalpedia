-- Prove2me | solution 1 for BilevelSOC.SecondOrder.Supplement.theorem_4_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:40:49.392096+00:00
-- url     : https://prove2.me/submissions/94ac6aa2-35a5-4d34-8a1e-ab5b65085718

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_ValueCriteria
open scoped Topology

open BilevelSOC
open BilevelSOC.SecondOrder
open BilevelSOC.SecondOrder.Supplement

theorem solution {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m)
    (φ : E n → ℝ) (hStanding : Standing D) (hfeas : z ∈ feasSet D)
    (hrep : ∀ᶠ x in 𝓝 z.1, valueFn D x = (φ x : EReal))
    (hLip : LocallyLipschitzAt φ z.1)
    (hregular : ClarkeRegularAt (fun x => -φ x) z.1)
    (hpolar : dualPolar (Q42 D z φ) = {0}) :
    StrictLocalMin D.F (feasSet D) z := by
      classical
      obtain ⟨hF, hf, hG, hg⟩ := hStanding
      refine ⟨hfeas, ?_⟩
      by_contra hcon
      push Not at hcon
      have hseq : ∀ k : ℕ, ∃ a ∈ feasSet D, a ∈ Metric.ball z (1 / ((k:ℝ) + 1)) ∧ a ≠ z ∧
          D.F a ≤ D.F z := by
        intro k
        obtain ⟨a, ⟨ha1, ha2⟩, ha3, ha4⟩ := hcon (Metric.ball z (1 / ((k:ℝ) + 1))) (Metric.ball_mem_nhds z (by positivity))
        exact ⟨a, ha1, ha2, ha3, ha4⟩
      choose a ha_feas ha_ball ha_ne ha_F using hseq
      have ha_lim : Filter.Tendsto a Filter.atTop (𝓝 z) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
        refine ⟨N, fun k hk => ?_⟩
        have := ha_ball k
        rw [Metric.mem_ball] at this
        have hk' : (N:ℝ) ≤ k := by exact_mod_cast hk
        calc dist (a k) z < 1 / ((k:ℝ)+1) := this
          _ ≤ 1 / ((N:ℝ)+1) := by gcongr
          _ < ε := hN
      set w : ℕ → E n × Y m := fun k => ‖a k - z‖⁻¹ • (a k - z) with hw
      have hw_sphere : ∀ k, w k ∈ Metric.sphere (0 : E n × Y m) 1 := by
        intro k
        have hne : ‖a k - z‖ ≠ 0 := by rw [norm_ne_zero_iff]; exact sub_ne_zero.mpr (ha_ne k)
        simp [w, norm_smul, hne]
      obtain ⟨d, hd_sphere, ψ, hψ, hψlim⟩ :=
        (isCompact_sphere (0 : E n × Y m) 1).tendsto_subseq hw_sphere
      have hd_ne : d ≠ 0 := by
        intro h; rw [h] at hd_sphere; simp at hd_sphere
      apply hd_ne
      rw [← Set.mem_singleton_iff, ← hpolar]
      set b : ℕ → E n × Y m := a ∘ ψ with hb
      have hb_lim : Filter.Tendsto b Filter.atTop (𝓝 z) := ha_lim.comp hψ.tendsto_atTop
      set c : ℕ → ℝ := fun k => ‖b k - z‖⁻¹ with hc
      have hcd : Filter.Tendsto (fun k => c k • (b k - z)) Filter.atTop (𝓝 d) := hψlim
      have hbz0 : Filter.Tendsto (fun k => b k - z) Filter.atTop (𝓝 0) := by
        have := hb_lim.sub_const z; simpa using this
      have hlim : ∀ h : E n × Y m → ℝ, DifferentiableAt ℝ h z →
          Filter.Tendsto (fun k => c k * (h (b k) - h z)) Filter.atTop (𝓝 (fderiv ℝ h z d)) := by
        intro h hdiff
        have := (hdiff.hasFDerivAt.hasFDerivWithinAt (s := Set.univ)).lim (c := c) hbz0 (by simp) hcd
        simpa using this
      have hle : ∀ h : E n × Y m → ℝ, DifferentiableAt ℝ h z → (∀ k, h (b k) ≤ h z) →
          fderiv ℝ h z d ≤ 0 := by
        intro h hdiff hk
        refine le_of_tendsto' (hlim h hdiff) (fun k => ?_)
        exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) (sub_nonpos.mpr (hk k))
      have hdiff : ∀ h : E n × Y m → ℝ, ContDiff ℝ 2 h → DifferentiableAt ℝ h z :=
        fun h hh => (hh.differentiable (by norm_num)).differentiableAt
      intro ξ hξ
      rcases hξ with ((hξ | ⟨i, hi, rfl⟩) | ⟨ζ, hζ, rfl⟩) | ⟨i, hi, rfl⟩
      · rw [Set.mem_singleton_iff] at hξ; subst hξ
        exact hle _ (hdiff _ hF) (fun k => ha_F (ψ k))
      · exact hle _ (hdiff _ (hG i)) (fun k => by
          rw [show D.G i z = 0 from hi]; exact (ha_feas (ψ k)).1 i)
      · show (fderiv ℝ D.f z - ζ.comp (ContinuousLinearMap.fst ℝ (E n) (Y m))) d ≤ 0
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.coe_fst']
        obtain ⟨v, hv_dir, hv_cl⟩ := hregular d.1
        -- Clarke comparison
        have hT : Filter.Tendsto (fun r : E n × ℝ => (r.1 - r.2 • d.1, r.2))
            ((𝓝 z.1) ×ˢ (𝓝[>] (0:ℝ))) ((𝓝 z.1) ×ˢ (𝓝[>] (0:ℝ))) := by
          refine Filter.Tendsto.prodMk ?_ Filter.tendsto_snd
          have hc : Continuous (fun r : E n × ℝ => r.1 - r.2 • d.1) := by fun_prop
          have h1 := hc.tendsto (z.1, 0)
          simp only [zero_smul, sub_zero] at h1
          exact h1.mono_left (by rw [nhds_prod_eq]; exact Filter.prod_mono le_rfl nhdsWithin_le_nhds)
        have hcl : clarkeDeriv φ z.1 (-d.1) ≤ clarkeDeriv (fun x => -φ x) z.1 d.1 := by
          unfold clarkeDeriv
          have hfun : (fun r : E n × ℝ => (((φ (r.1 + r.2 • -d.1) - φ r.1) / r.2 : ℝ) : EReal)) =
              (fun r : E n × ℝ => ((((fun x => -φ x) (r.1 + r.2 • d.1) - (fun x => -φ x) r.1) / r.2 : ℝ) : EReal))
                ∘ (fun r : E n × ℝ => (r.1 - r.2 • d.1, r.2)) := by
            funext r
            simp only [Function.comp, sub_add_cancel, smul_neg, ← sub_eq_add_neg]
            congr 1
            ring
          rw [hfun, Filter.limsup_comp]
          exact Filter.limsup_le_limsup_of_le hT
        have hζd : -ζ d.1 ≤ v := by
          have h1 := hζ (-d.1)
          rw [map_neg] at h1
          have h2 : ((-ζ d.1 : ℝ) : EReal) ≤ (v : EReal) := h1.trans (hcl.trans hv_cl.le)
          exact_mod_cast h2
        -- value function identity
        have hval : ∀ w ∈ feasSet D, valueFn D w.1 = (D.f w : EReal) := by
          intro w hw
          apply le_antisymm
          · exact iInf₂_le w.2 hw.2.1
          · exact le_iInf₂ fun y hy => by exact_mod_cast hw.2.2 y hy
        have hfx : D.f z = φ z.1 := by
          have h1 := (hval z hfeas).symm.trans hrep.self_of_nhds
          exact_mod_cast h1
        have hb1 : Filter.Tendsto (fun k => (b k).1) Filter.atTop (𝓝 z.1) :=
          (continuous_fst.tendsto z).comp hb_lim
        have hev : ∀ᶠ k in Filter.atTop, D.f (b k) = φ (b k).1 := by
          filter_upwards [hb1.eventually hrep] with k hk
          have h1 := (hval (b k) (ha_feas (ψ k))).symm.trans hk
          exact_mod_cast h1
        have hlimf : Filter.Tendsto (fun k => c k * (φ (b k).1 - φ z.1)) Filter.atTop
            (𝓝 (fderiv ℝ D.f z d)) :=
          (hlim D.f (hdiff _ hf)).congr' (hev.mono fun k hk => by simp only [hk, hfx])
        -- directional limit
        set t : ℕ → ℝ := fun k => ‖b k - z‖ with ht
        have ht_pos : ∀ k, 0 < t k := fun k => by
          simp only [t]; rw [norm_pos_iff]; exact sub_ne_zero.mpr (ha_ne (ψ k))
        have ht0 : Filter.Tendsto t Filter.atTop (𝓝 0) := by
          have := hbz0.norm; simpa using this
        have htw : Filter.Tendsto t Filter.atTop (𝓝[>] 0) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ht0
            (Filter.Eventually.of_forall ht_pos)
        have hA : Filter.Tendsto (fun k => c k * (φ (z.1 + t k • d.1) - φ z.1)) Filter.atTop
            (𝓝 (-v)) := by
          have h1 := (hv_dir.comp htw).neg
          refine h1.congr (fun k => ?_)
          simp only [Function.comp, c, t]
          rw [div_eq_inv_mul]
          ring
        have hcd1 : Filter.Tendsto (fun k => c k • ((b k).1 - z.1)) Filter.atTop (𝓝 d.1) := by
          have h1 := (continuous_fst.tendsto d).comp hcd
          exact h1
        obtain ⟨U, hU, K, hK⟩ := hLip
        have hnorm0 : Filter.Tendsto (fun k => (K:ℝ) * ‖c k • ((b k).1 - z.1) - d.1‖) Filter.atTop
            (𝓝 0) := by
          have h1 := ((hcd1.sub_const d.1).norm).const_mul (K:ℝ)
          simpa using h1
        have hxt : Filter.Tendsto (fun k => z.1 + t k • d.1) Filter.atTop (𝓝 z.1) := by
          have h1 := (ht0.smul_const d.1).const_add z.1
          simpa using h1
        have hE : Filter.Tendsto (fun k => c k * (φ (b k).1 - φ z.1) -
            c k * (φ (z.1 + t k • d.1) - φ z.1)) Filter.atTop (𝓝 0) := by
          refine squeeze_zero_norm' ?_ hnorm0
          filter_upwards [hb1.eventually hU, hxt.eventually hU] with k hk1 hk2
          have hL := hK.dist_le_mul _ hk1 _ hk2
          rw [Real.dist_eq, dist_eq_norm] at hL
          have hck : 0 ≤ c k := inv_nonneg.mpr (norm_nonneg _)
          have hct : c k * t k = 1 := inv_mul_cancel₀ (ht_pos k).ne'
          have heq : c k • ((b k).1 - (z.1 + t k • d.1)) = c k • ((b k).1 - z.1) - d.1 := by
            rw [sub_add_eq_sub_sub, smul_sub, smul_smul, hct, one_smul]
          calc ‖c k * (φ (b k).1 - φ z.1) - c k * (φ (z.1 + t k • d.1) - φ z.1)‖
              = c k * |φ (b k).1 - φ (z.1 + t k • d.1)| := by
                rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg hck]; ring_nf
            _ ≤ c k * ((K:ℝ) * ‖(b k).1 - (z.1 + t k • d.1)‖) := by gcongr
            _ = (K:ℝ) * ‖c k • ((b k).1 - (z.1 + t k • d.1))‖ := by
                rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hck]; ring
            _ = (K:ℝ) * ‖c k • ((b k).1 - z.1) - d.1‖ := by rw [heq]
        have hlimφ : Filter.Tendsto (fun k => c k * (φ (b k).1 - φ z.1)) Filter.atTop (𝓝 (-v)) := by
          have h1 := hE.add hA
          simpa using h1
        have heqv : fderiv ℝ D.f z d = -v := tendsto_nhds_unique hlimf hlimφ
        linarith
      · exact hle _ (hdiff _ (hg i)) (fun k => by
          rw [show D.g i z = 0 from hi]; exact (ha_feas (ψ k)).2.1 i)
