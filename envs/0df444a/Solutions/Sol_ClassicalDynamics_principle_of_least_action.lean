-- Prove2me | solution 1 for ClassicalDynamics.principle_of_least_action
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T08:33:45.483006+00:00
-- url     : https://prove2.me/submissions/24c296f9-ee8f-43fb-8143-848d3fd78399

import Definitions.Def_ClassicalDynamics_core

open ClassicalDynamics

namespace Ag5Aux

/-- Differentiation under the integral sign for a jointly `C¹` integrand. -/
lemma param (G : ℝ × ℝ → ℝ) (hG : ContDiff ℝ 1 G) (a b : ℝ) (hab : a ≤ b) :
    HasDerivAt (fun s => ∫ t in a..b, G (s, t)) (∫ t in a..b, fderiv ℝ G (0, t) (1, 0)) 0 := by
  have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hc : Continuous (fun p : ℝ × ℝ => fderiv ℝ G p (1, 0)) :=
    (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0:ℝ) 1).prod
    (isCompact_Icc (a := a) (b := b))).exists_bound_of_continuousOn hc.continuousOn
  have hdiff : ∀ s t : ℝ, HasDerivAt (fun s => G (s, t)) (fderiv ℝ G (s, t) (1, 0)) s := by
    intro s t
    have hp : HasDerivAt (fun u : ℝ => (u, t)) ((1 : ℝ), (0 : ℝ)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
    exact (hGd (s, t)).hasFDerivAt.comp_hasDerivAt s hp
  have hGc : ∀ s : ℝ, Continuous (fun t => G (s, t)) := fun s =>
    hG.continuous.comp (continuous_const.prodMk continuous_id)
  have hc0 : Continuous (fun t : ℝ => fderiv ℝ G (0, t) (1, 0)) :=
    hc.comp (continuous_const.prodMk continuous_id)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := a) (b := b)
    (F := fun s t => G (s, t)) (F' := fun s t => fderiv ℝ G (s, t) (1, 0)) (x₀ := 0)
    (bound := fun _ => C) (Metric.closedBall_mem_nhds (0:ℝ) one_pos)
    (Filter.Eventually.of_forall fun s => (hGc s).aestronglyMeasurable)
    ((hGc 0).intervalIntegrable a b)
    hc0.aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun t ht s hs => by
      apply hC (s, t)
      refine ⟨hs, ?_⟩
      rw [Set.uIoc_of_le hab] at ht
      exact Set.Ioc_subset_Icc_self ht)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun t _ s _ => hdiff s t)
  exact key.2

/-- Fundamental lemma of the calculus of variations (continuous version). -/
lemma fundamental (g : ℝ → ℝ) (hg : Continuous g) (a b : ℝ)
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → φ a = 0 → φ b = 0 →
      ∫ t in a..b, φ t * g t = 0) :
    ∀ t ∈ Set.Ioo a b, g t = 0 := by
  intro t₀ ht₀
  by_contra hne
  have hU : IsOpen ({t | 0 < g t₀ * g t} ∩ Set.Ioo a b) :=
    (isOpen_lt continuous_const (continuous_const.mul hg)).inter isOpen_Ioo
  have ht₀U : t₀ ∈ {t | 0 < g t₀ * g t} ∩ Set.Ioo a b :=
    ⟨mul_self_pos.mpr hne, ht₀⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU t₀ ht₀U
  have hδpos : 0 < ε / 2 := by positivity
  let φ : ContDiffBump t₀ := ⟨ε / 2 / 2, ε / 2, by positivity, by linarith⟩
  have hφ_out : ∀ t, ε ≤ dist t t₀ → φ t = 0 := fun t ht =>
    φ.zero_of_le_dist (by show ε / 2 ≤ _; linarith)
  have hfar : ∀ t, t ∉ Set.Ioo a b → ε ≤ dist t t₀ := by
    intro t ht
    by_contra hlt
    push_neg at hlt
    exact ht (hball (Metric.mem_ball.mpr hlt)).2
  have hφa : φ a = 0 := hφ_out a (hfar a (fun h => lt_irrefl a h.1))
  have hφb : φ b = 0 := hφ_out b (hfar b (fun h => lt_irrefl b h.2))
  have h0 := h (⇑φ) φ.contDiff hφa hφb
  have hfc : Continuous (fun t => g t₀ * (φ t * g t)) :=
    continuous_const.mul (φ.continuous.mul hg)
  have hf0 : ∫ t in a..b, g t₀ * (φ t * g t) = 0 := by
    rw [intervalIntegral.integral_const_mul, h0, mul_zero]
  have hnonneg : ∀ t, 0 ≤ g t₀ * (φ t * g t) := by
    intro t
    by_cases ht : dist t t₀ < ε
    · have h2 := (hball (Metric.mem_ball.mpr ht)).1
      simp only [Set.mem_setOf_eq] at h2
      have h1 := φ.nonneg (x := t)
      nlinarith
    · push_neg at ht; simp [hφ_out t ht]
  have hpos : ∀ t ∈ Set.Ioo (t₀ - ε / 2) (t₀ + ε / 2), 0 < g t₀ * (φ t * g t) := by
    intro t ht
    have hd : dist t t₀ < ε / 2 := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
    have h1 := φ.pos_of_mem_ball (Metric.mem_ball.mpr hd)
    have h2 := (hball (Metric.mem_ball.mpr (by linarith : dist t t₀ < ε))).1
    simp only [Set.mem_setOf_eq] at h2
    nlinarith
  have hlo : a ≤ t₀ - ε / 2 := by
    have := (hball (Metric.mem_ball.mpr (show dist (t₀ - ε / 2) t₀ < ε by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith))).2
    exact this.1.le
  have hhi : t₀ + ε / 2 ≤ b := by
    have := (hball (Metric.mem_ball.mpr (show dist (t₀ + ε / 2) t₀ < ε by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith))).2
    exact this.2.le
  have hint : 0 < ∫ t in (t₀ - ε / 2)..(t₀ + ε / 2), g t₀ * (φ t * g t) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hfc.intervalIntegrable _ _) hpos
      (by linarith)
  have hmono := intervalIntegral.integral_mono_interval (μ := MeasureTheory.volume)
    (f := fun t => g t₀ * (φ t * g t)) hlo (by linarith) hhi
    (MeasureTheory.ae_of_all _ fun t => hnonneg t) (hfc.intervalIntegrable _ _)
  linarith

lemma vel_eq_deriv {n : ℕ} (q : ℝ → Fin n → ℝ) (hq : Differentiable ℝ q) :
    vel q = deriv q := by
  funext t
  exact (deriv_pi (fun i => differentiableAt_pi.mp (hq t) i)).symm

lemma vel_smooth {n : ℕ} (q : ℝ → Fin n → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ContDiff ℝ (⊤ : ℕ∞) (vel q) := by
  rw [vel_eq_deriv q (hq.differentiable (by simp))]
  exact (contDiff_infty_iff_deriv.mp hq).2

lemma vel_add {n : ℕ} (q h : ℝ → Fin n → ℝ) (hq : Differentiable ℝ q)
    (hh : Differentiable ℝ h) (s : ℝ) :
    vel (fun t => q t + s • h t) = fun t => vel q t + s • vel h t := by
  have hd : Differentiable ℝ (fun t => q t + s • h t) := hq.add (hh.const_smul s)
  rw [vel_eq_deriv _ hd, vel_eq_deriv _ hq, vel_eq_deriv _ hh]
  funext t
  exact ((hq t).hasDerivAt.add ((hh t).hasDerivAt.const_smul s)).deriv

end Ag5Aux

open Ag5Aux in
theorem solution {n : ℕ} (L : Lagrangian n)
    (hL : IsSmoothLagrangian L) (q : ℝ → Fin n → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (t₁ t₂ : ℝ) (ht : t₁ < t₂) :
    (∀ h : ℝ → Fin n → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → h t₁ = 0 → h t₂ = 0 →
        HasDerivAt (fun s : ℝ => action L (fun t => q t + s • h t) t₁ t₂) 0 0)
      ↔ (∀ (i : Fin n), ∀ t ∈ Set.Ioo t₁ t₂,
          HasDerivAt (fun s : ℝ => dLdv L i s (q s) (vel q s))
            (dLdq L i t (q t) (vel q t)) t) := by
  classical
  set Lt : ℝ × (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p => L p.1 p.2.1 p.2.2 with hLtdef
  have hLs : ContDiff ℝ (⊤ : ℕ∞) Lt := hL
  have hLd : Differentiable ℝ Lt := hLs.differentiable (by simp)
  have hL2 : ContDiff ℝ 2 Lt := contDiff_infty.mp hLs 2
  have hDc : Continuous (fderiv ℝ Lt) := hL2.continuous_fderiv (by norm_num)
  have hdq : ∀ j t x v, dLdq L j t x v = fderiv ℝ Lt (t, x, v) (0, Pi.single j 1, 0) := by
    intro j t x v
    unfold dLdq
    have hp : HasDerivAt (fun y : ℝ => (t, Function.update x j y, v))
        ((0 : ℝ), (Pi.single j (1 : ℝ) : Fin n → ℝ), (0 : Fin n → ℝ)) (x j) :=
      (hasDerivAt_const _ t).prodMk ((hasDerivAt_update x j (x j)).prodMk (hasDerivAt_const _ v))
    have hl : HasFDerivAt Lt (fderiv ℝ Lt (t, x, v)) (t, Function.update x j (x j), v) := by
      rw [Function.update_eq_self]; exact (hLd _).hasFDerivAt
    exact (hl.comp_hasDerivAt (x j) hp).deriv
  have hdv : ∀ j t x v, dLdv L j t x v = fderiv ℝ Lt (t, x, v) (0, 0, Pi.single j 1) := by
    intro j t x v
    unfold dLdv
    have hp : HasDerivAt (fun y : ℝ => (t, x, Function.update v j y))
        ((0 : ℝ), (0 : Fin n → ℝ), (Pi.single j (1 : ℝ) : Fin n → ℝ)) (v j) :=
      (hasDerivAt_const _ t).prodMk ((hasDerivAt_const _ x).prodMk (hasDerivAt_update v j (v j)))
    have hl : HasFDerivAt Lt (fderiv ℝ Lt (t, x, v)) (t, x, Function.update v j (v j)) := by
      rw [Function.update_eq_self]; exact (hLd _).hasFDerivAt
    exact (hl.comp_hasDerivAt (v j) hp).deriv
  have hsingle : ∀ w : Fin n → ℝ, w = ∑ j, w j • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
    intro w; ext i; simp [Finset.sum_apply, Pi.single_apply]
  have decq : ∀ p (w : Fin n → ℝ), fderiv ℝ Lt p (0, w, 0) =
      ∑ j, w j * fderiv ℝ Lt p (0, Pi.single j 1, 0) := by
    intro p w
    have e : ((0 : ℝ), w, (0 : Fin n → ℝ)) =
        ∑ j, w j • ((0 : ℝ), (Pi.single j (1 : ℝ) : Fin n → ℝ), (0 : Fin n → ℝ)) := by
      conv_lhs => rw [hsingle w]
      ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
    rw [e, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
  have decv : ∀ p (w : Fin n → ℝ), fderiv ℝ Lt p (0, 0, w) =
      ∑ j, w j * fderiv ℝ Lt p (0, 0, Pi.single j 1) := by
    intro p w
    have e : ((0 : ℝ), (0 : Fin n → ℝ), w) =
        ∑ j, w j • ((0 : ℝ), (0 : Fin n → ℝ), (Pi.single j (1 : ℝ) : Fin n → ℝ)) := by
      conv_lhs => rw [hsingle w]
      ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
    rw [e, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
  have hsplit : ∀ p (w u : Fin n → ℝ), fderiv ℝ Lt p (0, w, u) =
      ∑ j, (w j * fderiv ℝ Lt p (0, Pi.single j 1, 0) +
        u j * fderiv ℝ Lt p (0, 0, Pi.single j 1)) := by
    intro p w u
    have e : ((0:ℝ), w, u) = ((0:ℝ), w, (0 : Fin n → ℝ)) + ((0:ℝ), (0 : Fin n → ℝ), u) := by
      ext <;> simp
    rw [e, map_add, decq, decv, Finset.sum_add_distrib]
  -- the reference path
  have hqd : Differentiable ℝ q := hq.differentiable (by simp)
  have hvq : ContDiff ℝ (⊤ : ℕ∞) (vel q) := vel_smooth q hq
  have hγc : Continuous (fun t => (t, q t, vel q t)) :=
    continuous_id.prodMk (hq.continuous.prodMk hvq.continuous)
  have hDw : ∀ w, Continuous (fun t => fderiv ℝ Lt (t, q t, vel q t) w) := fun w =>
    (hDc.comp hγc).clm_apply continuous_const
  have hAc : ∀ j, Continuous (fun s => dLdq L j s (q s) (vel q s)) := by
    intro j; simp only [hdq]; exact hDw _
  have hBc : ∀ j, Continuous (fun s => dLdv L j s (q s) (vel q s)) := by
    intro j; simp only [hdv]; exact hDw _
  -- first variation
  have hvar : ∀ h : ℝ → Fin n → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      HasDerivAt (fun s : ℝ => action L (fun t => q t + s • h t) t₁ t₂)
        (∫ t in t₁..t₂, fderiv ℝ Lt (t, q t, vel q t) (0, h t, vel h t)) 0 := by
    intro h hh
    have hhd : Differentiable ℝ h := hh.differentiable (by simp)
    have hvh := vel_smooth h hh
    have hq1 : ContDiff ℝ 1 q := contDiff_infty.mp hq 1
    have hh1 : ContDiff ℝ 1 h := contDiff_infty.mp hh 1
    have hvq1 : ContDiff ℝ 1 (vel q) := contDiff_infty.mp hvq 1
    have hvh1 : ContDiff ℝ 1 (vel h) := contDiff_infty.mp hvh 1
    have hGs : ContDiff ℝ 1 (fun p : ℝ × ℝ =>
        Lt (p.2, q p.2 + p.1 • h p.2, vel q p.2 + p.1 • vel h p.2)) := by
      have hΦ : ContDiff ℝ 1 (fun p : ℝ × ℝ =>
          (p.2, q p.2 + p.1 • h p.2, vel q p.2 + p.1 • vel h p.2)) := by
        refine contDiff_snd.prodMk (ContDiff.prodMk ?_ ?_)
        · exact (hq1.comp contDiff_snd).add (contDiff_fst.smul (hh1.comp contDiff_snd))
        · exact (hvq1.comp contDiff_snd).add (contDiff_fst.smul (hvh1.comp contDiff_snd))
      exact (contDiff_infty.mp hLs 1).comp hΦ
    have heq : (fun s : ℝ => action L (fun t => q t + s • h t) t₁ t₂) =
        fun s => ∫ t in t₁..t₂, (fun p : ℝ × ℝ =>
          Lt (p.2, q p.2 + p.1 • h p.2, vel q p.2 + p.1 • vel h p.2)) (s, t) := by
      funext s
      unfold action
      rw [vel_add q h hqd hhd s]
    rw [heq]
    refine (param _ hGs t₁ t₂ ht.le).congr_deriv ?_
    apply intervalIntegral.integral_congr
    intro t _
    have hp : HasDerivAt (fun s : ℝ => (t, q t + s • h t, vel q t + s • vel h t))
        ((0:ℝ), h t, vel h t) 0 := by
      refine (hasDerivAt_const 0 t).prodMk (HasDerivAt.prodMk ?_ ?_)
      · simpa using ((hasDerivAt_id (0:ℝ)).smul_const (h t)).const_add (q t)
      · simpa using ((hasDerivAt_id (0:ℝ)).smul_const (vel h t)).const_add (vel q t)
    have hl : HasFDerivAt Lt (fderiv ℝ Lt (t, q t, vel q t))
        (t, q t + (0:ℝ) • h t, vel q t + (0:ℝ) • vel h t) := by
      simp only [zero_smul, add_zero]; exact (hLd _).hasFDerivAt
    have h1 := hl.comp_hasDerivAt (0:ℝ) hp
    have hp2 : HasDerivAt (fun u : ℝ => (u, t)) ((1 : ℝ), (0 : ℝ)) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 t)
    have h2 := ((hGs.differentiable one_ne_zero) (0, t)).hasFDerivAt.comp_hasDerivAt (0:ℝ) hp2
    exact h2.unique h1
  constructor
  · intro hV i t₀ ht₀
    obtain ⟨B, hB⟩ : ∃ B : ℝ → ℝ, B = fun s => dLdv L i s (q s) (vel q s) := ⟨_, rfl⟩
    obtain ⟨A, hA⟩ : ∃ A : ℝ → ℝ, A = fun s => dLdq L i s (q s) (vel q s) := ⟨_, rfl⟩
    have hB1 : ContDiff ℝ 1 B := by
      have hBe : B = fun s => fderiv ℝ Lt (s, q s, vel q s) (0, 0, Pi.single i 1) := by
        rw [hB]; funext s; exact hdv i s (q s) (vel q s)
      rw [hBe]
      have hD1 : ContDiff ℝ 1 (fderiv ℝ Lt) := hL2.fderiv_right (m := 1) (by norm_num)
      have hγ1 : ContDiff ℝ 1 (fun s => (s, q s, vel q s)) :=
        contDiff_id.prodMk ((contDiff_infty.mp hq 1).prodMk (contDiff_infty.mp hvq 1))
      exact (hD1.comp hγ1).clm_apply contDiff_const
    have hBd : Differentiable ℝ B := hB1.differentiable one_ne_zero
    have hB'c : Continuous (deriv B) := hB1.continuous_deriv le_rfl
    have hAc' : Continuous A := by rw [hA]; exact hAc i
    have hBc' : Continuous B := hBd.continuous
    have key := fundamental (fun t => A t - deriv B t) (hAc'.sub hB'c) t₁ t₂ ?_ t₀ ht₀
    · have key' : A t₀ - deriv B t₀ = 0 := key
      have : deriv B t₀ = A t₀ := by linarith
      have hgoal : HasDerivAt B (A t₀) t₀ := by rw [← this]; exact (hBd t₀).hasDerivAt
      rw [hA, hB] at hgoal
      exact hgoal
    · intro φ hφ hφ1 hφ2
      have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
      have hφc : Continuous φ := hφ.continuous
      have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
      have hh : ContDiff ℝ (⊤ : ℕ∞) (fun t => φ t • (Pi.single i (1:ℝ) : Fin n → ℝ)) :=
        hφ.smul contDiff_const
      have hvel : vel (fun t => φ t • (Pi.single i (1:ℝ) : Fin n → ℝ)) =
          fun t => deriv φ t • (Pi.single i (1:ℝ) : Fin n → ℝ) := by
        funext t; funext j
        simp only [vel, Pi.smul_apply, smul_eq_mul]
        exact deriv_mul_const (hφd t) _
      have h0 := (hvar _ hh).unique (hV _ hh (by simp [hφ1]) (by simp [hφ2]))
      rw [hvel] at h0
      have hint : ∀ t, fderiv ℝ Lt (t, q t, vel q t)
          (0, φ t • (Pi.single i (1:ℝ) : Fin n → ℝ), deriv φ t • (Pi.single i (1:ℝ) : Fin n → ℝ))
          = φ t * A t + deriv φ t * B t := by
        intro t
        have e : ((0:ℝ), φ t • (Pi.single i (1:ℝ) : Fin n → ℝ),
            deriv φ t • (Pi.single i (1:ℝ) : Fin n → ℝ)) =
            φ t • ((0:ℝ), (Pi.single i (1:ℝ) : Fin n → ℝ), (0 : Fin n → ℝ)) +
            deriv φ t • ((0:ℝ), (0 : Fin n → ℝ), (Pi.single i (1:ℝ) : Fin n → ℝ)) := by
          ext <;> simp
        rw [hA, hB]
        dsimp only
        rw [hdq, hdv, e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      simp only [hint] at h0
      have hibp : ∫ t in t₁..t₂, (deriv φ t * B t + φ t * deriv B t) =
          φ t₂ * B t₂ - φ t₁ * B t₁ :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => (hφd t).hasDerivAt.mul (hBd t).hasDerivAt)
          (((hφ'c.mul hBc').add (hφc.mul hB'c)).intervalIntegrable _ _)
      rw [hφ1, hφ2, zero_mul, zero_mul, sub_zero] at hibp
      have hsub : ∫ t in t₁..t₂, φ t * (A t - deriv B t) =
          (∫ t in t₁..t₂, (φ t * A t + deriv φ t * B t)) -
            ∫ t in t₁..t₂, (deriv φ t * B t + φ t * deriv B t) := by
        have i1 : IntervalIntegrable (fun t => φ t * A t + deriv φ t * B t)
            MeasureTheory.volume t₁ t₂ :=
          (((hφc.mul hAc').add (hφ'c.mul hBc')).intervalIntegrable _ _)
        have i2 : IntervalIntegrable (fun t => deriv φ t * B t + φ t * deriv B t)
            MeasureTheory.volume t₁ t₂ :=
          (((hφ'c.mul hBc').add (hφc.mul hB'c)).intervalIntegrable _ _)
        rw [← intervalIntegral.integral_sub i1 i2]
        congr 1; funext t; ring
      show ∫ t in t₁..t₂, φ t * (A t - deriv B t) = 0
      rw [hsub, h0, hibp, sub_zero]
  · intro hEL h hh hh1 hh2
    have hhd : Differentiable ℝ h := hh.differentiable (by simp)
    have hvh := vel_smooth h hh
    refine (hvar h hh).congr_deriv ?_
    have hhj : ∀ j t, HasDerivAt (fun s => h s j) (vel h t j) t := fun j t =>
      (differentiableAt_pi.mp (hhd t) j).hasDerivAt
    have hhjc : ∀ j, Continuous (fun s => h s j) := fun j =>
      (continuous_apply j).comp hh.continuous
    have hvhjc : ∀ j, Continuous (fun s => vel h s j) := fun j =>
      (continuous_apply j).comp hvh.continuous
    have hFTC : ∫ t in t₁..t₂, (∑ j, (vel h t j * dLdv L j t (q t) (vel q t) +
          h t j * dLdq L j t (q t) (vel q t))) =
        (∑ j, h t₂ j * dLdv L j t₂ (q t₂) (vel q t₂)) -
          ∑ j, h t₁ j * dLdv L j t₁ (q t₁) (vel q t₁) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.le
      · exact (continuous_finset_sum _ fun j _ => (hhjc j).mul (hBc j)).continuousOn
      · intro t htt
        apply HasDerivAt.fun_sum
        intro j _
        exact (hhj j t).mul (hEL j t htt)
      · exact (continuous_finset_sum _ fun j _ =>
          ((hvhjc j).mul (hBc j)).add ((hhjc j).mul (hAc j))).intervalIntegrable _ _
    rw [hh1, hh2] at hFTC
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero] at hFTC
    refine Eq.trans (intervalIntegral.integral_congr ?_) hFTC
    intro t _
    dsimp only
    rw [hsplit]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hdq, hdv]
    ring
