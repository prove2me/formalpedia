-- Prove2me | solution 1 for ChanceStateCtrl.General.proposition_2_6_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T00:43:58.424164+00:00
-- url     : https://prove2.me/submissions/5ad9a3e1-16e7-42a9-8434-9e17e301f115

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
import Theorems.Thm_ChanceStateCtrl_General_theorem_2_2_lipschitz
import Theorems.Thm_ChanceStateCtrl_General_lemma_2_5
import Theorems.Thm_ChanceStateCtrl_General_convex_optimality_eq_20
import Theorems.Thm_ChanceStateCtrl_General_convex_subdiff_eq_clarke
import Theorems.Thm_ChanceStateCtrl_General_clarke_chain_rule_neg_log
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

open ChanceStateCtrl.General

theorem solution {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U] [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g)
    (hg_jc : ConvexOn ℝ Set.univ (Function.uncurry g))
    (F : U → ℝ) (hF_convex : ConvexOn ℝ Set.univ F) (hF_diff : Differentiable ℝ F)
    (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1) (hslater : ∃ uh : U, p < probFn P ξ g uh)
    (us : U) (hfeas : p ≤ probFn P ξ g us) (h10 : g us 0 < 0)
    (h12 : ModerateGrowth g Sigma us ∨ Bornology.IsBounded {z | g us z ≤ 0}) :
    IsSolution {u | p ≤ probFn P ξ g u} F us ↔
      ∃ lam : ℝ, 0 ≤ lam ∧
        (∃ x ∈ clarkeSubdiff (probFn P ξ g) us, fderiv ℝ F us = lam • x) ∧
        p ≤ probFn P ξ g us ∧ lam * (probFn P ξ g us - p) = 0 := by
  classical
  haveI := hA.isProb
  haveI := hA.complete
  set φ := probFn P ξ g with hφdef
  have hpos : 0 < p := hp.1
  -- closed form of `φ̃` where `φ > 0`
  have hPT : ∀ u, 0 < φ u →
      phiTilde P ξ g p u = ((-Real.log (φ u) + Real.log p : ℝ) : EReal) := by
    intro u hu
    have h1 : P {ω | g u (ξ ω) ≤ 0} = ENNReal.ofReal (φ u) := by
      simp only [hφdef, probFn]; rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    unfold phiTilde
    rw [h1, ENNReal.log_ofReal_of_pos hu, EReal.coe_add, EReal.coe_neg]
  -- Lemma 2.5
  obtain ⟨hfeasEq, hnebot, hconv, hlsc⟩ :=
    lemma_2_5 P ξ Sigma g hA hg_jc.quasiconvexOn p hp
  -- Theorem 2.2: φ is locally Lipschitz around `us`
  obtain ⟨-, K, t, ht, hLip⟩ := theorem_2_2_lipschitz P ξ Sigma g hA us h10 h12
  have hφus : 0 < φ us := lt_of_lt_of_le hpos hfeas
  have hφcont : ContinuousAt φ us := hLip.continuousOn.continuousAt ht
  obtain ⟨K2, t2, ht2, hLip2⟩ :=
    (Real.contDiffAt_log.2 hφus.ne' : ContDiffAt ℝ 1 Real.log (φ us)).exists_lipschitzOnWith
  set V := t ∩ φ ⁻¹' (t2 ∩ Set.Ioi 0) with hVdef
  have hV : V ∈ 𝓝 us :=
    inter_mem ht (hφcont.preimage_mem_nhds (inter_mem ht2 (Ioi_mem_nhds hφus)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hV
  set S := Metric.ball us r with hSdef
  set h : U → ℝ := fun u => -Real.log (φ u) + Real.log p with hhdef
  have hSpos : ∀ u ∈ S, 0 < φ u := fun u hu => (hball hu).2.2
  have hLogLip : LipschitzOnWith (K2 * K) (Real.log ∘ φ) V :=
    hLip2.comp (hLip.mono Set.inter_subset_left) (fun u hu => hu.2.1)
  have hLipV : LipschitzOnWith (K2 * K) h V := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have := hLogLip.dist_le_mul x hx y hy
    simp only [Function.comp, Real.dist_eq] at this
    simp only [hhdef, Real.dist_eq]
    calc |(-Real.log (φ x) + Real.log p) - (-Real.log (φ y) + Real.log p)|
        = |Real.log (φ x) - Real.log (φ y)| := by
          rw [← abs_neg]; congr 1; ring
      _ ≤ _ := this
  have hLocLip : LocLipAt h us := ⟨K2 * K, V, hV, hLipV⟩
  -- convexity of `h = φ̃` on the ball `S`
  have hconvS : ConvexOn ℝ S h := by
    refine ⟨convex_ball us r, ?_⟩
    intro x hx y hy a b ha hb hab
    have hxe : (x, h x) ∈ {q : U × ℝ | phiTilde P ξ g p q.1 ≤ (q.2 : EReal)} := by
      show phiTilde P ξ g p x ≤ ((h x : ℝ) : EReal)
      rw [hPT x (hSpos x hx)]
    have hye : (y, h y) ∈ {q : U × ℝ | phiTilde P ξ g p q.1 ≤ (q.2 : EReal)} := by
      show phiTilde P ξ g p y ≤ ((h y : ℝ) : EReal)
      rw [hPT y (hSpos y hy)]
    have H := hconv hxe hye ha hb hab
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
      Prod.smul_snd] at H
    rw [hPT _ (hSpos _ ((convex_ball us r) hx hy ha hb hab))] at H
    exact EReal.coe_le_coe_iff.1 H
  have hloc := convex_subdiff_eq_clarke S Metric.isOpen_ball h hconvS us
    (Metric.mem_ball_self hr) hLocLip
  have hchain := clarke_chain_rule_neg_log φ us ⟨K, t, ht, hLip⟩ hφus p hpos
  -- the convex subdifferential of `φ̃` equals the Clarke one
  have hsub : convexSubdiffE (phiTilde P ξ g p) us = clarkeSubdiff h us := by
    rw [← hloc]; ext x; constructor
    · intro hx w hw
      have H := hx w
      rw [hPT us hφus, hPT w (hSpos w hw), EReal.toReal_coe] at H
      exact EReal.coe_le_coe_iff.1 H
    · intro hx w
      rw [hPT us hφus, EReal.toReal_coe]
      rcases eq_or_ne (phiTilde P ξ g p w) ⊤ with hw | hw
      · rw [hw]; exact le_top
      set c := (phiTilde P ξ g p w).toReal with hcdef
      have hcw : phiTilde P ξ g p w = (c : EReal) := (EReal.coe_toReal hw (hnebot w)).symm
      rw [hcw]
      apply EReal.coe_le_coe_iff.2
      set d := ‖w - us‖ with hd
      have hd0 : 0 ≤ d := norm_nonneg _
      set t0 := r / (d + r) with ht0
      have ht0pos : 0 < t0 := div_pos hr (by linarith)
      have ht0le : t0 ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
      have hzS : (1 - t0) • us + t0 • w ∈ S := by
        rw [hSdef, Metric.mem_ball, dist_eq_norm]
        have : (1 - t0) • us + t0 • w - us = t0 • (w - us) := by
          simp only [sub_smul, one_smul, smul_sub]; abel
        rw [this, norm_smul, Real.norm_of_nonneg ht0pos.le, ← hd, ht0]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith
      have hue : (us, h us) ∈ {q : U × ℝ | phiTilde P ξ g p q.1 ≤ (q.2 : EReal)} := by
        show phiTilde P ξ g p us ≤ ((h us : ℝ) : EReal)
        rw [hPT us hφus]
      have hwe : (w, c) ∈ {q : U × ℝ | phiTilde P ξ g p q.1 ≤ (q.2 : EReal)} := by
        show phiTilde P ξ g p w ≤ ((c : ℝ) : EReal)
        rw [hcw]
      have H := hconv hue hwe (by linarith : (0:ℝ) ≤ 1 - t0) ht0pos.le (by ring)
      simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
        Prod.smul_snd] at H
      rw [hPT _ (hSpos _ hzS)] at H
      have H1 : h ((1 - t0) • us + t0 • w) ≤ (1 - t0) * h us + t0 * c :=
        EReal.coe_le_coe_iff.1 H
      have H2 := hx _ hzS
      have : (1 - t0) • us + t0 • w - us = t0 • (w - us) := by
        simp only [sub_smul, one_smul, smul_sub]; abel
      rw [this, map_smul, smul_eq_mul] at H2
      have H3 : t0 * (h us + x (w - us)) ≤ t0 * c := by nlinarith
      exact le_of_mul_le_mul_left H3 ht0pos
  have hfeasset : {u | p ≤ φ u} = {u | phiTilde P ξ g p u ≤ 0} :=
    Set.ext fun u => hfeasEq u
  have hslater' : ∃ uh, phiTilde P ξ g p uh < 0 := by
    obtain ⟨uh, huh⟩ := hslater
    refine ⟨uh, ?_⟩
    rw [hPT uh (hpos.trans huh)]
    have : Real.log p < Real.log (φ uh) := Real.log_lt_log hpos huh
    exact_mod_cast (by linarith : -Real.log (φ uh) + Real.log p < 0)
  have hus0 : phiTilde P ξ g p us ≤ 0 := (hfeasEq us).1 hfeas
  have hcont : ∃ t ∈ 𝓝 us, (∀ u ∈ t, phiTilde P ξ g p u ≠ ⊤) ∧
      ContinuousOn (fun u => (phiTilde P ξ g p u).toReal) t := by
    refine ⟨S, Metric.ball_mem_nhds us hr,
      fun u hu => by rw [hPT u (hSpos u hu)]; exact EReal.coe_ne_top _, ?_⟩
    refine (hLipV.continuousOn.mono hball).congr (fun u hu => ?_)
    rw [hPT u (hSpos u hu), EReal.toReal_coe]
  have key := convex_optimality_eq_20 F hF_convex hF_diff (phiTilde P ξ g p) hconv hnebot
    hlsc hslater' us hus0 hcont
  have hT : (phiTilde P ξ g p us).toReal = h us := by rw [hPT us hφus, EReal.toReal_coe]
  rw [hfeasset, key, hsub, hchain, hT]
  constructor
  · rintro ⟨lam, hlam, ⟨x, hx, hxe⟩, hc⟩
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hx
    refine ⟨lam * (φ us)⁻¹, mul_nonneg hlam (inv_nonneg.2 hφus.le), ⟨y, hy, ?_⟩, hfeas, ?_⟩
    · have : fderiv ℝ F us = -(lam • ((-(φ us)⁻¹) • y)) := by rw [← hxe, neg_neg]
      rw [this]
      ext v
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    · rcases mul_eq_zero.1 hc with h0 | h0
      · simp [h0]
      · have h0' : Real.log (φ us) = Real.log p := by
          simp only [hhdef] at h0; linarith
        have := Real.log_injOn_pos (Set.mem_Ioi.2 hφus) (Set.mem_Ioi.2 hpos) h0'
        rw [this]; ring
  · rintro ⟨lam, hlam, ⟨y, hy, hye⟩, -, hc⟩
    refine ⟨lam * φ us, mul_nonneg hlam hφus.le,
      ⟨(-(φ us)⁻¹) • y, Set.smul_mem_smul_set hy, ?_⟩, ?_⟩
    · rw [hye]
      ext v
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      field_simp
    · rcases mul_eq_zero.1 hc with h0 | h0
      · simp [h0]
      · have : φ us = p := by linarith
        simp only [hhdef, this]; ring
