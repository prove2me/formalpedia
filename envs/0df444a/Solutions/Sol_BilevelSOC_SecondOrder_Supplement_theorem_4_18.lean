-- Prove2me | solution 1 for BilevelSOC.SecondOrder.Supplement.theorem_4_18
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:42:57.947747+00:00
-- url     : https://prove2.me/submissions/5d7bdde9-0429-4c69-941b-7ef51a27e606

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_Complementarity
open scoped Topology

open BilevelSOC
open BilevelSOC.SecondOrder
open BilevelSOC.SecondOrder.Supplement

theorem solution {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m)
    (lam : Fin q → ℝ) (hStanding : Standing D) (hfeas : z ∈ feasSet D)
    (hconvexCQ : ConvexKKTExact D) (hlam : lam ∈ multipliers D z)
    (hstrict : StrictMFCQ D z lam)
    (hexclude : ∀ w ∈ kktLinCone D z lam, fderiv ℝ D.F z w.1 ≤ 0 → w = 0) :
    StrictLocalMin D.F (feasSet D) z := by
      classical
      have hS := hStanding
      have hyG : ∀ h : E n × Y m → ℝ, ContDiff ℝ 2 h → ∀ z', yGrad h z' =
          (InnerProductSpace.toDual ℝ (Y m)).symm
            ((fderiv ℝ h z').comp (ContinuousLinearMap.inr ℝ (E n) (Y m))) := by
        intro h hh z'
        unfold yGrad gradient
        congr 1
        have hd : HasFDerivAt h (fderiv ℝ h z') (z'.1, z'.2) :=
          (hh.differentiable (by norm_num) z').hasFDerivAt
        exact (hd.comp z'.2 (hasFDerivAt_prodMk_right z'.1 z'.2)).fderiv
      have hT : Differentiable ℝ
          (fun φ : (Y m →L[ℝ] ℝ) => (InnerProductSpace.toDual ℝ (Y m)).symm φ) := by
        let T : (Y m →L[ℝ] ℝ) →ₗ[ℝ] Y m :=
          { toFun := fun φ => (InnerProductSpace.toDual ℝ (Y m)).symm φ
            map_add' := by intros; simp
            map_smul' := by intros; simp }
        exact (LinearMap.toContinuousLinearMap T).differentiable
      have hyGd : ∀ h : E n × Y m → ℝ, ContDiff ℝ 2 h → Differentiable ℝ (yGrad h) := by
        intro h hh
        rw [funext (hyG h hh)]
        have h1 : Differentiable ℝ (fderiv ℝ h) :=
          (hh.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
        have h2 : Differentiable ℝ (fun z' => (fderiv ℝ h z').comp
            (ContinuousLinearMap.inr ℝ (E n) (Y m))) :=
          fun z' => (h1 z').clm_comp (differentiableAt_const _)
        exact hT.comp h2
      have hLcd : ∀ c : Fin q → ℝ, ContDiff ℝ 2 (lagrangian D c) := by
        intro c
        unfold lagrangian
        exact hS.2.1.add (ContDiff.sum fun i _ => contDiff_const.mul (hS.2.2.2 i))
      have hLin : ∀ (c : Fin q → ℝ) z', yGrad (lagrangian D c) z' =
          yGrad D.f z' + ∑ i, c i • yGrad (D.g i) z' := by
        intro c z'
        have hfd : HasFDerivAt (lagrangian D c)
            (fderiv ℝ D.f z' + ∑ i, c i • fderiv ℝ (D.g i) z') z' := by
          unfold lagrangian
          apply HasFDerivAt.add ((hS.2.1.differentiable (by norm_num) z').hasFDerivAt)
          apply HasFDerivAt.fun_sum
          intro i _
          exact ((hS.2.2.2 i).differentiable (by norm_num) z').hasFDerivAt.const_mul (c i)
        rw [hyG _ (hLcd c), hyG _ hS.2.1, hfd.fderiv]
        simp only [fun i => hyG _ (hS.2.2.2 i) z']
        apply (InnerProductSpace.toDual ℝ (Y m)).injective
        ext v
        simp [map_sum]
      have hdiff : ∀ h : E n × Y m → ℝ, ContDiff ℝ 2 h → DifferentiableAt ℝ h z :=
        fun h hh => hh.differentiable (by norm_num) z
      refine ⟨hfeas, ?_⟩
      by_contra hcon
      push_neg at hcon
      have hball : ∀ k : ℕ, ∃ a, a ∈ feasSet D ∧ dist a z < 1 / ((k:ℝ) + 1) ∧ a ≠ z ∧
          D.F a ≤ D.F z := by
        intro k
        obtain ⟨a, ⟨ha1, ha2⟩, ha3, ha4⟩ :=
          hcon (Metric.ball z (1 / ((k:ℝ)+1))) (Metric.ball_mem_nhds _ (by positivity))
        exact ⟨a, ha1, ha2, ha3, ha4⟩
      choose zs hzF hzd hzne hzle using hball
      have hzt : Filter.Tendsto zs Filter.atTop (𝓝 z) := by
        rw [tendsto_iff_dist_tendsto_zero]
        exact squeeze_zero (fun k => dist_nonneg) (fun k => (hzd k).le)
          tendsto_one_div_add_atTop_nhds_zero_nat
      have hmult : ∀ k, ∃ c, c ∈ multipliers D (zs k) :=
        fun k => ((hconvexCQ.2.2 (zs k).1 (zs k).2).1 (hzF k).2).2
      choose ls hls using hmult
      have hcomp : ∀ (z' : E n × Y m) (c : Fin q → ℝ), (∀ j, D.g j z' ≤ 0) →
          c ∈ multipliers D z' → ∀ i, c i * D.g i z' = 0 := by
        intro z' c hg hc i
        have h0 := hc.2.2
        rw [Finset.sum_eq_zero_iff_of_nonpos
          (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hc.2.1 j) (hg j))] at h0
        exact h0 i (Finset.mem_univ _)
      have hgz : ∀ j, D.g j z ≤ 0 := fun j => hfeas.2.1 j
      have hgk : ∀ k j, D.g j (zs k) ≤ 0 := fun k j => (hzF k).2.1 j
      set τ : ℕ → ℝ := fun k => ‖((zs k - z, ls k - lam) : (E n × Y m) × (Fin q → ℝ))‖ with hτdef
      have hτpos : ∀ k, 0 < τ k := by
        intro k
        apply norm_pos_iff.2
        intro h
        apply hzne k
        have := congrArg Prod.fst h
        simpa [sub_eq_zero] using this
      set v : ℕ → ((E n × Y m) × (Fin q → ℝ)) × ℝ :=
        fun k => ((τ k)⁻¹ • (zs k - z, ls k - lam), min (τ k) 1) with hvdef
      have hv : ∀ k, v k ∈ Metric.closedBall (0 : ((E n × Y m) × (Fin q → ℝ)) × ℝ) 1 := by
        intro k
        rw [mem_closedBall_zero_iff, Prod.norm_def]
        apply max_le
        · simp only [hvdef]
          rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hτpos k),
            inv_mul_cancel₀ (hτpos k).ne']
        · simp only [hvdef]
          rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hτpos k).le zero_le_one)]
          exact min_le_right _ _
      obtain ⟨⟨w, s0⟩, -, φ, hφ, hlim⟩ :=
        (isCompact_closedBall (0 : ((E n × Y m) × (Fin q → ℝ)) × ℝ) 1).tendsto_subseq hv
      have hw : Filter.Tendsto (fun k => (τ (φ k))⁻¹ • (zs (φ k) - z, ls (φ k) - lam))
          Filter.atTop (𝓝 w) := (continuous_fst.tendsto _).comp hlim
      have hs : Filter.Tendsto (fun k => min (τ (φ k)) 1) Filter.atTop (𝓝 s0) :=
        (continuous_snd.tendsto _).comp hlim
      have hw1 : Filter.Tendsto (fun k => (τ (φ k))⁻¹ • (zs (φ k) - z)) Filter.atTop (𝓝 w.1) := by
        have := (continuous_fst.tendsto _).comp hw
        simpa [Function.comp_def] using this
      have hw2i : ∀ i, Filter.Tendsto (fun k => (τ (φ k))⁻¹ * (ls (φ k) i - lam i))
          Filter.atTop (𝓝 (w.2 i)) := by
        intro i
        have := ((continuous_apply i).tendsto _).comp ((continuous_snd.tendsto _).comp hw)
        simpa [Function.comp_def] using this
      have hzφ : Filter.Tendsto (fun k => zs (φ k)) Filter.atTop (𝓝 z) :=
        hzt.comp hφ.tendsto_atTop
      have key : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : E n × Y m → V),
          DifferentiableAt ℝ h z →
          Filter.Tendsto (fun k => (τ (φ k))⁻¹ • (h (zs (φ k)) - h z)) Filter.atTop
            (𝓝 (fderiv ℝ h z w.1)) := by
        intro V _ _ h hd
        have h1 := hd.hasFDerivAt.isLittleO.comp_tendsto hzφ
        have h2 : (fun k => zs (φ k) - z) =O[Filter.atTop] (fun k => τ (φ k)) := by
          apply Asymptotics.IsBigO.of_bound 1
          filter_upwards with k
          rw [one_mul, Real.norm_eq_abs, abs_of_pos (hτpos _)]
          exact norm_fst_le ((zs (φ k) - z, ls (φ k) - lam) : (E n × Y m) × (Fin q → ℝ))
        have h3 := (h1.trans_isBigO h2).norm_left
        have h4 : Filter.Tendsto (fun k => (τ (φ k))⁻¹ •
            (h (zs (φ k)) - h z - fderiv ℝ h z (zs (φ k) - z))) Filter.atTop (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          have := h3.tendsto_div_nhds_zero
          refine this.congr (fun k => ?_)
          simp only [Function.comp_def, norm_smul, norm_inv, Real.norm_eq_abs,
            abs_of_pos (hτpos (φ k))]
          rw [div_eq_inv_mul]
        have h5 : Filter.Tendsto (fun k => fderiv ℝ h z ((τ (φ k))⁻¹ • (zs (φ k) - z)))
            Filter.atTop (𝓝 (fderiv ℝ h z w.1)) :=
          ((fderiv ℝ h z).continuous.tendsto _).comp hw1
        have := h4.add h5
        rw [zero_add] at this
        refine this.congr (fun k => ?_)
        rw [ContinuousLinearMap.map_smul, smul_sub (τ (φ k))⁻¹ (h (zs (φ k)) - h z), sub_add_cancel]
      have hFw : fderiv ℝ D.F z w.1 ≤ 0 := by
        refine le_of_tendsto' (key D.F (hdiff _ hS.1)) (fun k => ?_)
        rw [smul_eq_mul]
        exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (hτpos _).le) (sub_nonpos.2 (hzle _))
      have c1 : ∀ i ∈ actG D z, fderiv ℝ (D.G i) z w.1 ≤ 0 := by
        intro i hi
        have hi' : D.G i z = 0 := hi
        refine le_of_tendsto' (key (D.G i) (hdiff _ (hS.2.2.1 i))) (fun k => ?_)
        rw [smul_eq_mul, hi', sub_zero]
        exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (hτpos _).le) ((hzF _).1 i)
      have gder : ∀ i, D.g i z = 0 → fderiv ℝ (D.g i) z w.1 ≤ 0 := by
        intro i hi'
        refine le_of_tendsto' (key (D.g i) (hdiff _ (hS.2.2.2 i))) (fun k => ?_)
        rw [smul_eq_mul, hi', sub_zero]
        exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (hτpos _).le) (hgk _ i)
      have c3 : ∀ i, lam i = 0 → D.g i z < 0 → w.2 i = 0 := by
        intro i hl hg
        have hev : ∀ᶠ k in Filter.atTop, D.g i (zs (φ k)) < 0 :=
          (((hS.2.2.2 i).continuous.tendsto z).comp hzφ).eventually (gt_mem_nhds hg)
        have hev2 : ∀ᶠ k in Filter.atTop, (τ (φ k))⁻¹ * (ls (φ k) i - lam i) = 0 := by
          filter_upwards [hev] with k hk
          have := hcomp _ _ (hgk (φ k)) (hls (φ k)) i
          rw [mul_eq_zero] at this
          rcases this with h | h
          · rw [h, hl]; simp
          · exact absurd h hk.ne
        exact tendsto_nhds_unique (hw2i i) (tendsto_const_nhds.congr' (hev2.mono fun k hk => hk.symm))
      have c5a : ∀ i, lam i = 0 → 0 ≤ w.2 i := by
        intro i hl
        refine ge_of_tendsto' (hw2i i) (fun k => ?_)
        rw [hl, sub_zero]
        exact mul_nonneg (inv_nonneg.2 (hτpos _).le) ((hls _).2.1 i)
      have c5b : ∀ i, lam i = 0 → D.g i z = 0 → w.2 i * fderiv ℝ (D.g i) z w.1 = 0 := by
        intro i hl hg
        have := (hw2i i).mul (key (D.g i) (hdiff _ (hS.2.2.2 i)))
        refine tendsto_nhds_unique this (tendsto_const_nhds.congr (fun k => ?_))
        rw [smul_eq_mul, hl, hg, sub_zero, sub_zero]
        have := hcomp _ _ (hgk (φ k)) (hls (φ k)) i
        calc (0:ℝ) = (τ (φ k))⁻¹ * (τ (φ k))⁻¹ * (ls (φ k) i * D.g i (zs (φ k))) := by
              rw [this, mul_zero]
          _ = _ := by ring
      have c2 : yHess (lagrangian D lam) z w.1 + (∑ i, w.2 i • yGrad (D.g i) z) = 0 := by
        have hL := key (yGrad (lagrangian D lam)) (hyGd _ (hLcd lam) z)
        have hR : Filter.Tendsto (fun k => -∑ i, ((τ (φ k))⁻¹ * (ls (φ k) i - lam i)) •
            yGrad (D.g i) (zs (φ k))) Filter.atTop (𝓝 (-∑ i, w.2 i • yGrad (D.g i) z)) := by
          apply Filter.Tendsto.neg
          apply tendsto_finset_sum
          intro i _
          exact (hw2i i).smul (((hyGd _ (hS.2.2.2 i)).continuous.tendsto z).comp hzφ)
        have heq : ∀ k, (τ (φ k))⁻¹ • (yGrad (lagrangian D lam) (zs (φ k)) -
            yGrad (lagrangian D lam) z) =
            -∑ i, ((τ (φ k))⁻¹ * (ls (φ k) i - lam i)) • yGrad (D.g i) (zs (φ k)) := by
          intro k
          have h0 := (hls (φ k)).1
          rw [hLin] at h0
          rw [hlam.1, sub_zero, hLin]
          have hf : yGrad D.f (zs (φ k)) = -∑ i, ls (φ k) i • yGrad (D.g i) (zs (φ k)) :=
            eq_neg_of_add_eq_zero_left h0
          rw [hf]
          simp only [mul_smul, sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, smul_sub,
            smul_add, smul_neg]
          abel
        have := tendsto_nhds_unique hL (hR.congr (fun k => (heq k).symm))
        unfold yHess
        rw [this, neg_add_cancel]
      have c4 : ∀ i ∈ iplus0 D z lam, fderiv ℝ (D.g i) z w.1 = 0 := by
        intro i hi
        obtain ⟨hlpos, hgi⟩ := hi
        by_cases hs0 : s0 = 0
        · subst hs0
          have ht : Filter.Tendsto (fun k => τ (φ k)) Filter.atTop (𝓝 0) := by
            refine hs.congr' ?_
            filter_upwards [hs.eventually (gt_mem_nhds zero_lt_one)] with k hk
            apply min_eq_left
            rcases min_lt_iff.1 hk with h | h
            · exact h.le
            · exact absurd h (lt_irrefl _)
          have hli : Filter.Tendsto (fun k => ls (φ k) i) Filter.atTop (𝓝 (lam i)) := by
            have := (ht.mul (hw2i i)).const_add (lam i)
            rw [zero_mul, add_zero] at this
            refine this.congr (fun k => ?_)
            field_simp [(hτpos (φ k)).ne']
            ring
          have hev : ∀ᶠ k in Filter.atTop,
              (τ (φ k))⁻¹ • (D.g i (zs (φ k)) - D.g i z) = 0 := by
            filter_upwards [hli.eventually (lt_mem_nhds hlpos)] with k hk
            have := hcomp _ _ (hgk (φ k)) (hls (φ k)) i
            rw [mul_eq_zero] at this
            rcases this with h | h
            · exact absurd h hk.ne'
            · rw [h, hgi]; simp
          exact tendsto_nhds_unique (key (D.g i) (hdiff _ (hS.2.2.2 i)))
            (tendsto_const_nhds.congr' (hev.mono fun k hk => hk.symm))
        · have hs0pos : 0 < s0 := lt_of_le_of_ne
            (ge_of_tendsto' hs (fun k => le_min (hτpos _).le zero_le_one)) (Ne.symm hs0)
          have hw10 : w.1 = 0 := by
            have hz0 : Filter.Tendsto (fun k => (2 / s0) * ‖zs (φ k) - z‖) Filter.atTop (𝓝 0) := by
              have := ((tendsto_iff_norm_sub_tendsto_zero.1 hzφ).const_mul (2 / s0))
              simpa using this
            have : Filter.Tendsto (fun k => (τ (φ k))⁻¹ • (zs (φ k) - z)) Filter.atTop (𝓝 0) := by
              refine squeeze_zero_norm' ?_ hz0
              filter_upwards [hs.eventually (lt_mem_nhds (half_lt_self hs0pos))] with k hk
              have hk' : s0 / 2 < τ (φ k) := lt_of_lt_of_le hk (min_le_left _ _)
              rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hτpos _)]
              gcongr
              calc (τ (φ k))⁻¹ ≤ (s0 / 2)⁻¹ := inv_anti₀ (by positivity) hk'.le
                _ = 2 / s0 := by rw [inv_div]
            exact tendsto_nhds_unique hw1 this
          rw [hw10, map_zero]
      have hmem : w ∈ kktLinCone D z lam :=
        ⟨c1, c2, fun i hi => c3 i hi.1 hi.2, c4,
          fun i hi => ⟨c5a i hi.1, gder i hi.2, c5b i hi.1 hi.2⟩⟩
      have hw0 := hexclude w hmem hFw
      have hnorm : ‖w‖ = 1 := by
        refine tendsto_nhds_unique hw.norm (tendsto_const_nhds.congr (fun k => ?_))
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hτpos _)]
        exact (inv_mul_cancel₀ (hτpos _).ne').symm
      rw [hw0, norm_zero] at hnorm
      exact zero_ne_one hnorm
