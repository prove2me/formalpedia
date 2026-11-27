-- Prove2me | solution 1 for BilevelSOC.SecondOrder.Supplement.lemma_4_15
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:42:21.028013+00:00
-- url     : https://prove2.me/submissions/8ef7f2e8-1617-4c81-9a48-216c2d21ee5d

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_Complementarity
open scoped Topology

open BilevelSOC
open BilevelSOC.SecondOrder
open BilevelSOC.SecondOrder.Supplement

theorem solution {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m)
    (lam : Fin q → ℝ) (hStanding : Standing D) (hfeas : z ∈ feasSet D)
    (hconvexCQ : ConvexKKTExact D) (hlam : lam ∈ multipliers D z)
    (hstrict : StrictMFCQ D z lam) :
    tangentCone (feasSet D) z ⊆ projection '' kktLinCone D z lam := by
      obtain ⟨-, hf, hG, hg⟩ := hStanding
      obtain ⟨-, -, hKKT⟩ := hconvexCQ
      rintro d ⟨t, dk, htpos, ht0, hdk, hmem⟩
      have htne : ∀ k, t k ≠ 0 := fun k => (htpos k).ne'
      have hyg : ∀ h : E n × Y m → ℝ, ContDiff ℝ 2 h → ∀ w,
          yGrad h w = (InnerProductSpace.toDual ℝ (Y m)).symm
            ((fderiv ℝ h w).comp (ContinuousLinearMap.inr ℝ (E n) (Y m))) := by
        intro h hh w
        have h1 : HasFDerivAt h (fderiv ℝ h w) (w.1, w.2) :=
          (hh.differentiable (by norm_num) w).hasFDerivAt
        have h2 : HasFDerivAt (fun y : Y m => h (w.1, y))
            ((fderiv ℝ h w).comp (ContinuousLinearMap.inr ℝ (E n) (Y m))) w.2 :=
          h1.comp w.2 (hasFDerivAt_prodMk_right w.1 w.2)
        unfold yGrad gradient
        rw [h2.fderiv]
      have hygdiff : ∀ h : E n × Y m → ℝ, ContDiff ℝ 2 h → Differentiable ℝ (yGrad h) := by
        intro h hh
        have e : yGrad h = fun w => (InnerProductSpace.toDual ℝ (Y m)).symm
            ((fderiv ℝ h w).comp (ContinuousLinearMap.inr ℝ (E n) (Y m))) := funext (hyg h hh)
        rw [e]
        have h1 : Differentiable ℝ (fderiv ℝ h) :=
          (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
        have h2 : Differentiable ℝ (fun w => (fderiv ℝ h w).comp
            (ContinuousLinearMap.inr ℝ (E n) (Y m))) :=
          h1.clm_comp (differentiable_const _)
        exact (InnerProductSpace.toDual ℝ (Y m)).symm.toContinuousLinearEquiv.differentiable.comp h2
      have hLc : ∀ l : Fin q → ℝ, ContDiff ℝ 2 (lagrangian D l) := by
        intro l
        unfold lagrangian
        exact hf.add (ContDiff.sum fun i _ => contDiff_const.mul (hg i))
      have hLg : ∀ (l : Fin q → ℝ) w, yGrad (lagrangian D l) w =
          yGrad D.f w + ∑ i, l i • yGrad (D.g i) w := by
        intro l w
        have hd : fderiv ℝ (lagrangian D l) w = fderiv ℝ D.f w + ∑ i, l i • fderiv ℝ (D.g i) w := by
          have hfa : HasFDerivAt D.f (fderiv ℝ D.f w) w :=
            (hf.differentiable (by norm_num) w).hasFDerivAt
          have hga : ∀ i, HasFDerivAt (D.g i) (fderiv ℝ (D.g i) w) w := fun i =>
            ((hg i).differentiable (by norm_num) w).hasFDerivAt
          have : HasFDerivAt (fun w => D.f w + ∑ i, l i * D.g i w)
              (fderiv ℝ D.f w + ∑ i, l i • fderiv ℝ (D.g i) w) w :=
            hfa.add (HasFDerivAt.fun_sum fun i _ => (hga i).const_mul (l i))
          exact this.fderiv
        rw [hyg _ (hLc l), hyg _ hf, hd]
        simp only [fun i => hyg _ (hg i) w]
        rw [ContinuousLinearMap.add_comp, map_add, ContinuousLinearMap.finsetSum_comp, map_sum]
        simp only [ContinuousLinearMap.smul_comp, map_smul]
      -- multipliers along the sequence
      have hk : ∀ k, ∃ l, l ∈ multipliers D (z + t k • dk k) := fun k =>
        ((hKKT (z + t k • dk k).1 (z + t k • dk k).2).1 (hmem k).2).2
      choose l hl using hk
      have hgk : ∀ k i, D.g i (z + t k • dk k) ≤ 0 := fun k i => (hmem k).2.1 i
      have hgz : ∀ i, D.g i z ≤ 0 := fun i => hfeas.2.1 i
      have hcomp : ∀ (w : E n × Y m) (ν : Fin q → ℝ), (∀ i, D.g i w ≤ 0) → ν ∈ multipliers D w →
          ∀ i, ν i * D.g i w = 0 := by
        intro w ν hw hν i
        have h1 : ∀ j ∈ Finset.univ, ν j * D.g j w ≤ 0 := fun j _ =>
          mul_nonpos_of_nonneg_of_nonpos (hν.2.1 j) (hw j)
        exact (Finset.sum_eq_zero_iff_of_nonpos h1).1 hν.2.2 i (Finset.mem_univ i)
      have hck : ∀ k i, l k i * D.g i (z + t k • dk k) = 0 := fun k i =>
        hcomp _ _ (hgk k) (hl k) i
      have hcz : ∀ i, lam i * D.g i z = 0 := fun i => hcomp _ _ hgz hlam i
      have hz : Filter.Tendsto (fun k => z + t k • dk k) Filter.atTop (𝓝 z) := by
        have := (tendsto_const_nhds (x := z) (f := (Filter.atTop : Filter ℕ))).add (ht0.smul hdk)
        simpa using this
      have hc : Filter.Tendsto (fun k => t k • dk k) Filter.atTop (𝓝 0) := by
        simpa using ht0.smul hdk
      have hdk' : Filter.Tendsto (fun k => (t k)⁻¹ • (t k • dk k)) Filter.atTop (𝓝 d) := by
        simpa [smul_smul, htne] using hdk
      have hquot : ∀ (h : E n × Y m → ℝ), ContDiff ℝ 2 h →
          Filter.Tendsto (fun k => (t k)⁻¹ * (h (z + t k • dk k) - h z)) Filter.atTop
            (𝓝 (fderiv ℝ h z d)) := by
        intro h hh
        exact ((hh.differentiable (by norm_num) z).hasFDerivAt.hasFDerivWithinAt (s := Set.univ)).lim
          hc (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hdk'
      have hLquot : Filter.Tendsto (fun k => (t k)⁻¹ • (yGrad (lagrangian D lam) (z + t k • dk k)
          - yGrad (lagrangian D lam) z)) Filter.atTop (𝓝 (yHess (lagrangian D lam) z d)) :=
        ((hygdiff _ (hLc lam) z).hasFDerivAt.hasFDerivWithinAt (s := Set.univ)).lim
          hc (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hdk'
      have hgcont : ∀ i, Filter.Tendsto (fun k => D.g i (z + t k • dk k)) Filter.atTop
          (𝓝 (D.g i z)) := fun i => ((hg i).continuous.tendsto z).comp hz
      have hygcont : ∀ i, Filter.Tendsto (fun k => yGrad (D.g i) (z + t k • dk k)) Filter.atTop
          (𝓝 (yGrad (D.g i) z)) := fun i => ((hygdiff _ (hg i)).continuous.tendsto z).comp hz
      have hkey : ∀ k, (yGrad (lagrangian D lam) (z + t k • dk k) - yGrad (lagrangian D lam) z)
          + ∑ i, (l k i - lam i) • yGrad (D.g i) (z + t k • dk k) = 0 := by
        intro k
        have h1 := (hl k).1
        rw [hLg] at h1
        rw [hlam.1, hLg, sub_zero]
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← h1]
        abel
      have hinact : ∀ i, D.g i z < 0 → lam i = 0 ∧ ∀ᶠ k in Filter.atTop, l k i = 0 := by
        intro i hi
        refine ⟨(mul_eq_zero.1 (hcz i)).resolve_right hi.ne, ?_⟩
        filter_upwards [(hgcont i).eventually_lt_const hi] with k hk
        exact (mul_eq_zero.1 (hck k i)).resolve_right hk.ne
      -- boundedness of the difference quotients
      have hnot : ¬ Filter.Tendsto (fun k => ‖(t k)⁻¹ • (l k - lam)‖) Filter.atTop Filter.atTop := by
        intro htop
        have hbd : ∀ k, (‖l k - lam‖⁻¹ • (l k - lam)) ∈ Metric.closedBall (0 : Fin q → ℝ) 1 := by
          intro k
          rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm]
          exact inv_mul_le_one
        obtain ⟨μ, -, φ, hφ, hμ⟩ := (isCompact_closedBall (0 : Fin q → ℝ) 1).tendsto_subseq hbd
        have hφt := hφ.tendsto_atTop
        have hne : ∀ᶠ k in Filter.atTop, ‖l k - lam‖ ≠ 0 := by
          filter_upwards [htop.eventually_gt_atTop 0] with k hk h0
          rw [norm_smul, h0, mul_zero] at hk
          exact lt_irrefl _ hk
        have hratio : Filter.Tendsto (fun k => ‖l k - lam‖⁻¹ * t k) Filter.atTop (𝓝 0) := by
          have := htop.inv_tendsto_atTop
          refine this.congr fun k => ?_
          simp [norm_smul, abs_of_pos (htpos k)]
        have hμi : ∀ i, Filter.Tendsto (fun k => ‖l (φ k) - lam‖⁻¹ * (l (φ k) i - lam i))
            Filter.atTop (𝓝 (μ i)) := fun i => by
          simpa using (tendsto_pi_nhds.1 hμ i)
        have hμ0 : μ = 0 := by
          apply hstrict
          · have h1 : Filter.Tendsto (fun k => ((‖l (φ k) - lam‖⁻¹ * t (φ k)) •
                ((t (φ k))⁻¹ • (yGrad (lagrangian D lam) (z + t (φ k) • dk (φ k))
                  - yGrad (lagrangian D lam) z))) +
                ∑ i, (‖l (φ k) - lam‖⁻¹ * (l (φ k) i - lam i)) •
                  yGrad (D.g i) (z + t (φ k) • dk (φ k))) Filter.atTop
                (𝓝 ((0:ℝ) • yHess (lagrangian D lam) z d + ∑ i, μ i • yGrad (D.g i) z)) :=
              ((hratio.comp hφt).smul (hLquot.comp hφt)).add
                (tendsto_finsetSum _ fun i _ => (hμi i).smul ((hygcont i).comp hφt))
            have h2 : ∀ k, ((‖l (φ k) - lam‖⁻¹ * t (φ k)) •
                ((t (φ k))⁻¹ • (yGrad (lagrangian D lam) (z + t (φ k) • dk (φ k))
                  - yGrad (lagrangian D lam) z))) +
                ∑ i, (‖l (φ k) - lam‖⁻¹ * (l (φ k) i - lam i)) •
                  yGrad (D.g i) (z + t (φ k) • dk (φ k)) = 0 := by
              intro k
              rw [smul_smul, mul_assoc, mul_inv_cancel₀ (htne _), mul_one]
              simp only [mul_smul, ← Finset.smul_sum]
              rw [← smul_add, hkey, smul_zero]
            simp only [h2] at h1
            simpa using (tendsto_nhds_unique h1 tendsto_const_nhds)
          · intro i hi
            have hi' : D.g i z < 0 := lt_of_le_of_ne (hgz i) hi
            obtain ⟨h0, hev⟩ := hinact i hi'
            refine tendsto_nhds_unique (hμi i) (tendsto_const_nhds.congr' ?_)
            filter_upwards [hφt.eventually hev] with k hk
            rw [hk, h0]; simp
          · intro i hi
            refine ge_of_tendsto' (hμi i) fun k => ?_
            rw [hi.1, sub_zero]
            exact mul_nonneg (inv_nonneg.2 (norm_nonneg _)) ((hl _).2.1 i)
        have hn1 : Filter.Tendsto (fun k => ‖‖l (φ k) - lam‖⁻¹ • (l (φ k) - lam)‖) Filter.atTop
            (𝓝 ‖μ‖) := hμ.norm
        have hn2 : Filter.Tendsto (fun k => ‖‖l (φ k) - lam‖⁻¹ • (l (φ k) - lam)‖) Filter.atTop
            (𝓝 1) := by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [hφt.eventually hne] with k hk
          rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hk]
        have := tendsto_nhds_unique hn1 hn2
        rw [hμ0, norm_zero] at this
        exact zero_ne_one this
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∃ᶠ k in Filter.atTop, ‖(t k)⁻¹ • (l k - lam)‖ < C := by
        rw [Filter.tendsto_atTop] at hnot
        push Not at hnot
        simpa [Filter.Frequently] using hnot
      obtain ⟨η, -, φ, hφ, hη⟩ := tendsto_subseq_of_frequently_bounded
        (s := Metric.closedBall (0 : Fin q → ℝ) C) Metric.isBounded_closedBall
        (x := fun k => (t k)⁻¹ • (l k - lam))
        (hC.mono fun k hk => by rw [mem_closedBall_zero_iff]; exact hk.le)
      have hφt := hφ.tendsto_atTop
      have hηi : ∀ i, Filter.Tendsto (fun k => (t (φ k))⁻¹ * (l (φ k) i - lam i))
          Filter.atTop (𝓝 (η i)) := fun i => by
        simpa using (tendsto_pi_nhds.1 hη i)
      have hli : ∀ i, Filter.Tendsto (fun k => l (φ k) i) Filter.atTop (𝓝 (lam i)) := by
        intro i
        have h1 := (((ht0.comp hφt).mul (hηi i)).add_const (lam i))
        rw [zero_mul, zero_add] at h1
        refine h1.congr fun k => ?_
        have := htne (φ k)
        simp only [Function.comp]
        field_simp
        ring
      refine ⟨(d, η), ⟨?_, ?_, ?_, ?_, ?_⟩, rfl⟩
      · intro i hi
        refine le_of_tendsto' (hquot _ (hG i)) fun k => ?_
        have hi0 : D.G i z = 0 := hi
        rw [hi0, sub_zero]
        exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (htpos k).le) ((hmem k).1 i)
      · have h1 : Filter.Tendsto (fun k =>
              ((t (φ k))⁻¹ • (yGrad (lagrangian D lam) (z + t (φ k) • dk (φ k))
                - yGrad (lagrangian D lam) z)) +
              ∑ i, ((t (φ k))⁻¹ * (l (φ k) i - lam i)) •
                yGrad (D.g i) (z + t (φ k) • dk (φ k))) Filter.atTop
              (𝓝 (yHess (lagrangian D lam) z d + ∑ i, η i • yGrad (D.g i) z)) :=
          (hLquot.comp hφt).add
            (tendsto_finsetSum _ fun i _ => (hηi i).smul ((hygcont i).comp hφt))
        have h2 : ∀ k, ((t (φ k))⁻¹ • (yGrad (lagrangian D lam) (z + t (φ k) • dk (φ k))
                - yGrad (lagrangian D lam) z)) +
              ∑ i, ((t (φ k))⁻¹ * (l (φ k) i - lam i)) •
                yGrad (D.g i) (z + t (φ k) • dk (φ k)) = 0 := by
          intro k
          simp only [mul_smul, ← Finset.smul_sum]
          rw [← smul_add, hkey, smul_zero]
        simp only [h2] at h1
        exact tendsto_nhds_unique h1 tendsto_const_nhds
      · intro i hi
        obtain ⟨h0, hev⟩ := hinact i hi.2
        refine tendsto_nhds_unique (hηi i) (tendsto_const_nhds.congr' ?_)
        filter_upwards [hφt.eventually hev] with k hk
        rw [hk, h0]; simp
      · intro i hi
        refine tendsto_nhds_unique ((hquot _ (hg i)).comp hφt) (tendsto_const_nhds.congr' ?_)
        filter_upwards [(hli i).eventually_const_lt hi.1] with k hk
        have h0 : D.g i (z + t (φ k) • dk (φ k)) = 0 :=
          (mul_eq_zero.1 (hck (φ k) i)).resolve_left hk.ne'
        simp only [Function.comp]
        rw [h0, hi.2]; simp
      · intro i hi
        refine ⟨?_, ?_, ?_⟩
        · refine ge_of_tendsto' (hηi i) fun k => ?_
          rw [hi.1, sub_zero]
          exact mul_nonneg (inv_nonneg.2 (htpos _).le) ((hl _).2.1 i)
        · refine le_of_tendsto' (hquot _ (hg i)) fun k => ?_
          rw [hi.2, sub_zero]
          exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (htpos k).le) (hgk k i)
        · refine tendsto_nhds_unique ((hηi i).mul ((hquot _ (hg i)).comp hφt))
            (tendsto_const_nhds.congr fun k => ?_)
          simp only [Function.comp]
          rw [hi.1, hi.2, sub_zero, sub_zero]
          linear_combination (-(t (φ k))⁻¹ * (t (φ k))⁻¹) * hck (φ k) i
