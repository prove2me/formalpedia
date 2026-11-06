-- Prove2me | solution 1 for DROOptimal.Predictor.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T10:01:58.993049+00:00
-- url     : https://prove2.me/submissions/f55df2b3-184c-41ab-9adc-4e6ef7c39a3b

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting

open DROOptimal.Predictor Filter Topology

namespace DROm4P2

/-- Π_i (α − g_i)^{p_i}. -/
noncomputable def ψ {d : ℕ} (g p : Fin d → ℝ) (α : ℝ) : ℝ := ∏ i, (α - g i) ^ p i

lemma ψ_nonneg {d : ℕ} (g p : Fin d → ℝ) (α : ℝ) (hα : ∀ i, g i ≤ α) : 0 ≤ ψ g p α :=
  Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (by linarith [hα i]) _)

lemma ψ_cont {d : ℕ} (g p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) : Continuous (ψ g p) := by
  unfold ψ
  refine continuous_finsetProd _ (fun i _ => ?_)
  exact Continuous.rpow_const (continuous_id.sub continuous_const) (fun _ => Or.inr (hp i))

/-- (L): Π y^p ≤ Σ p y. -/
lemma ψ_le {d : ℕ} (g p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (α : ℝ)
    (hα : ∀ i, g i ≤ α) : ψ g p α ≤ α - ∑ i, p i * g i := by
  have := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ) p (fun i => α - g i)
    (fun i _ => hp i) hp1 (fun i _ => by linarith [hα i])
  unfold ψ
  refine this.trans (le_of_eq ?_)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]

/-- (W): for P with I(p, P) ≤ r, e^{-r} Π y^p ≤ Σ P y. -/
lemma weak {d : ℕ} (g : Fin d → ℝ) (P' P : Δ d) (r : ℝ)
    (hI : relEntropy P' P ≤ (r : EReal)) (α : ℝ) (hα : ∀ i, g i ≤ α) :
    Real.exp (-r) * ψ g (P' : Fin d → ℝ) α ≤ ∑ i, (P : Fin d → ℝ) i * (α - g i) := by
  classical
  set p : Fin d → ℝ := (P' : Fin d → ℝ) with hpdef
  set q : Fin d → ℝ := (P : Fin d → ℝ) with hqdef
  have hp : ∀ i, 0 ≤ p i := fun i => P'.2.1 i
  have hq : ∀ i, 0 ≤ q i := fun i => P.2.1 i
  have hp1 : ∑ i, p i = 1 := P'.2.2
  have hy : ∀ i, 0 ≤ α - g i := fun i => by linarith [hα i]
  have hRHS : 0 ≤ ∑ i, q i * (α - g i) := Finset.sum_nonneg (fun i _ => mul_nonneg (hq i) (hy i))
  by_cases hz : ∃ i, p i ≠ 0 ∧ α - g i = 0
  · obtain ⟨i, hpi, hyi⟩ := hz
    have : ψ g p α = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hyi]; exact Real.zero_rpow hpi)
    rw [this, mul_zero]; exact hRHS
  push Not at hz
  unfold relEntropy at hI
  split_ifs at hI with hc
  · have hI' : ∑ i, p i * Real.log (p i / q i) ≤ r := by exact_mod_cast hI
    -- AM-GM with z_i = q_i y_i / p_i
    have amgm := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ) p
      (fun i => q i * (α - g i) / p i) (fun i _ => hp i) hp1
      (fun i _ => div_nonneg (mul_nonneg (hq i) (hy i)) (hp i))
    have hR : ∑ i, p i * (q i * (α - g i) / p i) ≤ ∑ i, q i * (α - g i) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      rcases (hp i).eq_or_lt with h0 | h0
      · rw [← h0]; simp; exact mul_nonneg (hq i) (hy i)
      · rw [mul_div_cancel₀ _ h0.ne']
    have hL : ∏ i, (q i * (α - g i) / p i) ^ p i =
        ψ g p α * Real.exp (∑ i, p i * Real.log (q i / p i)) := by
      unfold ψ
      rw [Real.exp_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rcases (hp i).eq_or_lt with h0 | h0
      · rw [← h0]; simp
      · have hqi : 0 < q i := lt_of_le_of_ne (hq i) (fun h => h0.ne' (hc i h.symm))
        have hyi : 0 < α - g i := lt_of_le_of_ne (hy i) (fun h => hz i h0.ne' h.symm)
        rw [show q i * (α - g i) / p i = (α - g i) * (q i / p i) by ring,
          Real.mul_rpow hyi.le (div_pos hqi h0).le, Real.rpow_def_of_pos (div_pos hqi h0),
          mul_comm (Real.log _) (p i)]
    have hneg : ∑ i, p i * Real.log (q i / p i) = - ∑ i, p i * Real.log (p i / q i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← inv_div, Real.log_inv]; ring
    have hexp : Real.exp (-r) ≤ Real.exp (∑ i, p i * Real.log (q i / p i)) := by
      rw [hneg]; exact Real.exp_le_exp.mpr (by linarith)
    calc Real.exp (-r) * ψ g p α ≤ ψ g p α * Real.exp (∑ i, p i * Real.log (q i / p i)) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hexp (ψ_nonneg g p α hα)
      _ = ∏ i, (q i * (α - g i) / p i) ^ p i := hL.symm
      _ ≤ _ := amgm
      _ ≤ _ := hR
  · exact absurd hI (not_le.mpr (EReal.coe_lt_top r))

lemma ψ_eq_exp {d : ℕ} (g p : Fin d → ℝ) (α : ℝ) (hpos : ∀ i, 0 < p i → 0 < α - g i)
    (hp : ∀ i, 0 ≤ p i) :
    ψ g p α = Real.exp (∑ i, p i * Real.log (α - g i)) := by
  unfold ψ
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rcases (hp i).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · rw [Real.rpow_def_of_pos (hpos i h0), mul_comm]

/-- The primal model built from a dual point. -/
lemma construct {d : ℕ} (g : Fin d → ℝ) (P' : Δ d) (r : ℝ) (α : ℝ)
    (hα : ∀ i, g i ≤ α) (hpos : ∀ i, 0 < (P' : Fin d → ℝ) i → 0 < α - g i) (j : Fin d)
    (hs : Real.exp (-r) * ψ g (P' : Fin d → ℝ) α *
      ∑ i, (P' : Fin d → ℝ) i / (α - g i) ≤ 1)
    (hb : Real.exp (-r) * ψ g (P' : Fin d → ℝ) α * ∑ i, (P' : Fin d → ℝ) i / (α - g i) < 1 →
      g j = α) :
    ∃ P : Δ d, relEntropy P' P ≤ (r : EReal) ∧
      ∑ i, (P : Fin d → ℝ) i * g i = α - Real.exp (-r) * ψ g (P' : Fin d → ℝ) α := by
  classical
  set p : Fin d → ℝ := (P' : Fin d → ℝ) with hpdef
  have hp : ∀ i, 0 ≤ p i := fun i => P'.2.1 i
  have hp1 : ∑ i, p i = 1 := P'.2.2
  set y : Fin d → ℝ := fun i => α - g i with hydef
  have hy : ∀ i, 0 ≤ y i := fun i => by simp only [hydef]; linarith [hα i]
  set L : ℝ := Real.exp (-r) * ψ g p α with hLdef
  set s : ℝ := ∑ i, p i / y i with hsdef
  have hψpos : 0 < ψ g p α := by
    rw [ψ_eq_exp g p α hpos hp]; exact Real.exp_pos _
  have hL : 0 < L := mul_pos (Real.exp_pos _) hψpos
  let Q : Fin d → ℝ := fun i => L * p i / y i + (if i = j then 1 - L * s else 0)
  have hQ0 : ∀ i, 0 ≤ Q i := by
    intro i
    refine add_nonneg (div_nonneg (mul_nonneg hL.le (hp i)) (hy i)) ?_
    split_ifs
    · linarith
    · exact le_rfl
  have hQ1 : ∑ i, Q i = 1 := by
    simp only [Q, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hsdef, Finset.mul_sum]
    have : ∑ i, L * p i / y i = ∑ i, L * (p i / y i) :=
      Finset.sum_congr rfl (fun i _ => mul_div_assoc _ _ _)
    rw [this]; ring
  let P : Δ d := ⟨Q, hQ0, hQ1⟩
  have hPv : ∀ i, (P : Fin d → ℝ) i = Q i := fun i => rfl
  have hQlow : ∀ i, 0 < p i → L * p i / y i ≤ Q i := by
    intro i _
    simp only [Q]
    have : 0 ≤ (if i = j then 1 - L * s else 0) := by split_ifs <;> linarith
    linarith
  refine ⟨P, ?_, ?_⟩
  · -- relative entropy ≤ r
    have hc : ∀ i, (P : Fin d → ℝ) i = 0 → (P' : Fin d → ℝ) i = 0 := by
      intro i hi
      by_contra hne
      have h0 : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hne)
      have := hQlow i h0
      rw [← hPv, hi] at this
      have : 0 < L * p i / y i := div_pos (mul_pos hL h0) (hpos i h0)
      linarith
    simp only [relEntropy, if_pos hc]
    rw [EReal.coe_le_coe_iff]
    have hlogL : Real.log L = -r + ∑ i, p i * Real.log (y i) := by
      rw [hLdef, Real.log_mul (Real.exp_pos _).ne' hψpos.ne', Real.log_exp,
        ψ_eq_exp g p α hpos hp, Real.log_exp]
    calc ∑ i, (P' : Fin d → ℝ) i * Real.log ((P' : Fin d → ℝ) i / (P : Fin d → ℝ) i)
        ≤ ∑ i, p i * (Real.log (y i) - Real.log L) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          change p i * Real.log (p i / Q i) ≤ _
          rcases (hp i).eq_or_lt with h0 | h0
          · rw [← h0]; simp
          · have hyi : 0 < y i := hpos i h0
            have hlow := hQlow i h0
            have hQpos : 0 < Q i := lt_of_lt_of_le (div_pos (mul_pos hL h0) hyi) hlow
            apply mul_le_mul_of_nonneg_left _ h0.le
            rw [← Real.log_div hyi.ne' hL.ne']
            apply Real.log_le_log (div_pos h0 hQpos)
            rw [div_le_div_iff₀ hQpos hL]
            have : L * p i ≤ Q i * y i := by
              have := mul_le_mul_of_nonneg_right hlow hyi.le
              rwa [div_mul_cancel₀ _ hyi.ne'] at this
            linarith
      _ = r := by
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul, hlogL]
          ring
  · -- cost
    have hterm : ∀ i, Q i * g i = (L * (p i / y i)) * α - L * p i +
        (if i = j then (1 - L * s) * g i else 0) := by
      intro i
      simp only [Q, add_mul]
      congr 1
      · rcases (hp i).eq_or_lt with h0 | h0
        · rw [← h0]; simp
        · have hyi : 0 < y i := hpos i h0
          have : g i = α - y i := by simp only [hydef]; ring
          rw [this]; field_simp
      · split_ifs <;> simp
    simp only [hPv, hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, ← Finset.sum_mul, ← Finset.mul_sum, hp1]
    have hj : (1 - L * s) * g j = (1 - L * s) * α := by
      rcases hs.lt_or_eq with hlt | heq
      · rw [hb hlt]
      · rw [heq]; ring
    rw [hj, ← hsdef]
    ring

lemma hasDeriv_φ {d : ℕ} (g p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (r α : ℝ)
    (hpos : ∀ i, 0 < p i → 0 < α - g i) :
    HasDerivAt (fun a => a - Real.exp (-r) * ψ g p a)
      (1 - Real.exp (-r) * ψ g p α * ∑ i, p i / (α - g i)) α := by
  classical
  have hT : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      HasDerivAt (fun a => p i * Real.log (a - g i)) (p i / (α - g i)) α := by
    intro i _
    rcases (hp i).eq_or_lt with h0 | h0
    · have : (fun a => p i * Real.log (a - g i)) = fun _ => (0 : ℝ) := by
        funext a; rw [← h0, zero_mul]
      rw [this, ← h0, zero_div]
      exact hasDerivAt_const α 0
    · have h1 : HasDerivAt (fun a => a - g i) 1 α := (hasDerivAt_id α).sub_const (g i)
      have h2 := (h1.log (hpos i h0).ne').const_mul (p i)
      exact h2.congr_deriv (by rw [mul_one_div])
  have hS := HasDerivAt.fun_sum hT
  have hE := hS.exp
  have hev : (ψ g p) =ᶠ[𝓝 α] (fun a => Real.exp (∑ i, p i * Real.log (a - g i))) := by
    have : ∀ᶠ a in 𝓝 α, ∀ i, 0 < p i → 0 < a - g i := by
      rw [eventually_all]
      intro i
      by_cases h0 : 0 < p i
      · have hc : Continuous (fun a : ℝ => a - g i) := continuous_id.sub continuous_const
        exact (hc.continuousAt.eventually (lt_mem_nhds (hpos i h0))).mono (fun a ha _ => ha)
      · exact Eventually.of_forall (fun a h => absurd h h0)
    filter_upwards [this] with a ha
    exact ψ_eq_exp g p a ha hp
  have hψ := hE.congr_of_eventuallyEq hev
  have := (hasDerivAt_id α).sub (hψ.const_mul (Real.exp (-r)))
  refine this.congr_deriv ?_
  rw [ψ_eq_exp g p α hpos hp]
  ring

lemma deriv_nonneg_of_right {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x)
    (hmin : ∀ t, 0 < t → f x ≤ f (x + t)) : 0 ≤ f' := by
  have h := hf.tendsto_slope_zero_right
  refine ge_of_tendsto h (eventually_nhdsWithin_of_forall (fun t ht => ?_))
  have ht' : 0 < t := ht
  rw [smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr ht'.le) (by linarith [hmin t ht'])

lemma deriv_nonpos_of_left {f : ℝ → ℝ} {f' x δ : ℝ} (hf : HasDerivAt f f' x) (hδ : 0 < δ)
    (hmin : ∀ t, -δ < t → t < 0 → f x ≤ f (x + t)) : f' ≤ 0 := by
  have h := hf.tendsto_slope_zero_left
  refine le_of_tendsto h ?_
  filter_upwards [Ioo_mem_nhdsLT (show -δ < (0 : ℝ) by linarith)] with t ht
  rw [smul_eq_mul]
  exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr ht.2.le) (by linarith [hmin t ht.1 ht.2])

/-- At α = M, if p charges both a maximiser of g and a non-maximiser, moving right strictly
decreases the dual objective. -/
lemma boundary_not_min {d : ℕ} (g : Fin d → ℝ) (P' : Δ d) (r M : ℝ) (hM : ∀ i, g i ≤ M)
    (i₀ : Fin d) (hi₀ : 0 < (P' : Fin d → ℝ) i₀) (hgi₀ : g i₀ = M)
    (k : Fin d) (hk : 0 < (P' : Fin d → ℝ) k) (hgk : g k ≠ M) :
    ∃ h : ℝ, 0 < h ∧ (M + h) - Real.exp (-r) * ψ g (P' : Fin d → ℝ) (M + h) <
      M - Real.exp (-r) * ψ g (P' : Fin d → ℝ) M := by
  classical
  set p : Fin d → ℝ := (P' : Fin d → ℝ) with hpdef
  have hp : ∀ i, 0 ≤ p i := fun i => P'.2.1 i
  have hp1 : ∑ i, p i = 1 := P'.2.2
  have hψM : ψ g p M = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i₀) (by rw [hgi₀, sub_self]; exact Real.zero_rpow hi₀.ne')
  set q : ℝ := ∑ i ∈ Finset.univ.filter (fun i => g i = M), p i with hqdef
  have hq0 : 0 < q := lt_of_lt_of_le hi₀ (Finset.single_le_sum (fun i _ => hp i)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgi₀⟩))
  have hqk : q + p k ≤ 1 := by
    rw [← hp1, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => g i = M)]
    have : p k ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ g i = M), p i :=
      Finset.single_le_sum (fun i _ => hp i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgk⟩)
    linarith
  have hq1 : 0 < 1 - q := by linarith
  set C : ℝ := ∏ i ∈ Finset.univ.filter (fun i => ¬ g i = M), (M - g i) ^ p i with hCdef
  have hC : 0 < C := Finset.prod_pos (fun i hi => by
    have h1 := (Finset.mem_filter.mp hi).2
    exact Real.rpow_pos_of_pos (by have := hM i; have : g i < M := lt_of_le_of_ne this h1; linarith) _)
  have hlow : ∀ h, 0 < h → h ^ q * C ≤ ψ g p (M + h) := by
    intro h hh
    unfold ψ
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => g i = M)]
    apply mul_le_mul
    · rw [hqdef, Real.rpow_sum_of_pos hh]
      exact le_of_eq (Finset.prod_congr rfl (fun i hi => by
        rw [(Finset.mem_filter.mp hi).2]; ring_nf))
    · exact Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (by linarith [hM i]) _)
        (fun i _ => Real.rpow_le_rpow (by linarith [hM i]) (by linarith) (hp i))
    · exact hC.le
    · exact Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (by linarith [hM i]) _)
  -- h^{1-q} → 0 as h → 0⁺
  have htend : Tendsto (fun h : ℝ => h ^ (1 - q)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (1 - q) (Or.inr hq1.le)).tendsto
    rw [Real.zero_rpow hq1.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hK : 0 < Real.exp (-r) * C := mul_pos (Real.exp_pos _) hC
  obtain ⟨h, hh1, hh2⟩ := ((htend.eventually (gt_mem_nhds hK)).and
    self_mem_nhdsWithin).exists
  have hh : 0 < h := hh2
  refine ⟨h, hh, ?_⟩
  rw [hψM, mul_zero, sub_zero]
  have hsplit : h = h ^ (1 - q) * h ^ q := by
    rw [← Real.rpow_add hh]; simp
  have hhq : 0 < h ^ q := Real.rpow_pos_of_pos hh q
  have h3 : h < Real.exp (-r) * (h ^ q * C) := by
    calc h = h ^ (1 - q) * h ^ q := hsplit
      _ < Real.exp (-r) * C * h ^ q := mul_lt_mul_of_pos_right hh1 hhq
      _ = Real.exp (-r) * (h ^ q * C) := by ring
  have h4 := hlow h hh
  have h5 : Real.exp (-r) * (h ^ q * C) ≤ Real.exp (-r) * ψ g p (M + h) :=
    mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
  linarith

lemma relEntropy_self {d : ℕ} (p : Δ d) : relEntropy p p = 0 := by
  classical
  have hc : ∀ i, (p : Fin d → ℝ) i = 0 → (p : Fin d → ℝ) i = 0 := fun _ h => h
  simp only [relEntropy, if_pos hc]
  have : ∑ i, (p : Fin d → ℝ) i * Real.log ((p : Fin d → ℝ) i / (p : Fin d → ℝ) i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : (p : Fin d → ℝ) i = 0
    · simp [h]
    · simp [div_self h]
  rw [this]; rfl

/-- Strong duality at a dual minimiser. -/
lemma strong {d : ℕ} (g : Fin d → ℝ) (P' : Δ d) (r M : ℝ) (hr : 0 < r) (hM : ∀ i, g i ≤ M)
    (j : Fin d) (hj : g j = M) (α : ℝ) (hαM : M ≤ α)
    (hmin : ∀ β, M ≤ β → α - Real.exp (-r) * ψ g (P' : Fin d → ℝ) α ≤
      β - Real.exp (-r) * ψ g (P' : Fin d → ℝ) β) :
    ∃ P : Δ d, relEntropy P' P ≤ (r : EReal) ∧
      ∑ i, (P : Fin d → ℝ) i * g i = α - Real.exp (-r) * ψ g (P' : Fin d → ℝ) α := by
  classical
  set p : Fin d → ℝ := (P' : Fin d → ℝ) with hpdef
  have hp : ∀ i, 0 ≤ p i := fun i => P'.2.1 i
  have hp1 : ∑ i, p i = 1 := P'.2.2
  have hα : ∀ i, g i ≤ α := fun i => (hM i).trans hαM
  by_cases hz : ∃ i, 0 < p i ∧ α - g i = 0
  · obtain ⟨i₀, hi₀, hy₀⟩ := hz
    have hαeq : α = M := le_antisymm (by linarith [hM i₀]) hαM
    subst hαeq
    have hgi₀ : g i₀ = α := by linarith
    by_cases hall : ∀ k, 0 < p k → g k = α
    · refine ⟨P', ?_, ?_⟩
      · rw [relEntropy_self]; exact_mod_cast hr.le
      · have hψ0 : ψ g p α = 0 := Finset.prod_eq_zero (Finset.mem_univ i₀)
          (by rw [hy₀]; exact Real.zero_rpow hi₀.ne')
        rw [hψ0, mul_zero, sub_zero]
        have : ∑ i, p i * g i = ∑ i, p i * α := Finset.sum_congr rfl (fun k _ => by
          rcases (hp k).eq_or_lt with h0 | h0
          · rw [← h0]; simp
          · rw [hall k h0])
        rw [this, ← Finset.sum_mul, hp1, one_mul]
    · push Not at hall
      obtain ⟨k, hk, hgk⟩ := hall
      obtain ⟨h, hh, hlt⟩ := boundary_not_min g P' r α hM i₀ hi₀ hgi₀ k hk hgk
      have := hmin (α + h) (by linarith)
      linarith
  · push Not at hz
    have hpos : ∀ i, 0 < p i → 0 < α - g i := fun i hi =>
      lt_of_le_of_ne (by linarith [hα i]) (fun h => hz i hi h.symm)
    have hD := hasDeriv_φ g p hp r α hpos
    set L := Real.exp (-r) * ψ g p α * ∑ i, p i / (α - g i) with hLdef
    have hs : L ≤ 1 := by
      have := deriv_nonneg_of_right hD (fun t ht => hmin (α + t) (by linarith))
      linarith
    have hb : L < 1 → g j = α := by
      intro hlt
      by_contra hne
      have hgt : M < α := lt_of_le_of_ne hαM (fun h => hne (hj.trans h))
      have := deriv_nonpos_of_left hD (sub_pos.mpr hgt)
        (fun t ht _ => hmin (α + t) (by linarith))
      linarith
    exact construct g P' r α hα hpos j hs hb

end DROm4P2

open DROm4P2 in
theorem solution {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 < r) (x : ↥X) (ℙ' : Δ d) :
    IsLeast {v : ℝ | ∃ α : ℝ, (⨆ i, γ x i) ≤ α ∧
        v = α - Real.exp (-r) * ∏ i, (α - γ x i) ^ ((ℙ' : Fin d → ℝ) i)}
      (drPredictor γ r x ℙ') ∧
    ∃ αstar : ℝ, (⨆ i, γ x i) ≤ αstar ∧
      αstar ≤ ((⨆ i, γ x i) - Real.exp (-r) * cost γ x ℙ') / (1 - Real.exp (-r)) ∧
      drPredictor γ r x ℙ' =
        αstar - Real.exp (-r) * ∏ i, (αstar - γ x i) ^ ((ℙ' : Fin d → ℝ) i) := by
  classical
  set g : Fin d → ℝ := γ x with hgdef
  set p : Fin d → ℝ := (ℙ' : Fin d → ℝ) with hpdef
  have hp : ∀ i, 0 ≤ p i := fun i => ℙ'.2.1 i
  have hp1 : ∑ i, p i = 1 := ℙ'.2.2
  haveI : Nonempty (Fin d) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : ∑ i, p i = 0 := Finset.sum_of_isEmpty _
    linarith
  set M : ℝ := ⨆ i, g i with hMdef
  have hM : ∀ i, g i ≤ M := fun i => le_ciSup (Set.finite_range g).bddAbove i
  obtain ⟨j, hj⟩ : ∃ j, g j = M := exists_eq_ciSup_of_finite
  set φ : ℝ → ℝ := fun a => a - Real.exp (-r) * ψ g p a with hφdef
  have hφ : ∀ a, a - Real.exp (-r) * ∏ i, (a - γ x i) ^ ((ℙ' : Fin d → ℝ) i) = φ a :=
    fun a => rfl
  set c' : ℝ := cost γ x ℙ' with hc'def
  have hc' : c' = ∑ i, p i * g i := rfl
  have he : Real.exp (-r) < 1 := by
    have := Real.exp_lt_exp.mpr (show -r < 0 by linarith); rwa [Real.exp_zero] at this
  have he0 : 0 < Real.exp (-r) := Real.exp_pos _
  have hc'M : c' ≤ M := by
    rw [hc']
    calc ∑ i, p i * g i ≤ ∑ i, p i * M :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hM i) (hp i))
      _ = M := by rw [← Finset.sum_mul, hp1, one_mul]
  -- feasible set, bounds
  set S : Set (Δ d) := {P : Δ d | relEntropy ℙ' P ≤ (r : EReal)} with hSdef
  have hS : ℙ' ∈ S := by
    change relEntropy ℙ' ℙ' ≤ _; rw [relEntropy_self]; exact_mod_cast hr.le
  have hcostP : ∀ P : Δ d, cost γ x P = ∑ i, (P : Fin d → ℝ) i * g i := fun _ => rfl
  have hbdd : BddAbove ((fun P => cost γ x P) '' S) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨P, _, rfl⟩
    change cost γ x P ≤ _
    rw [hcostP]
    calc ∑ i, (P : Fin d → ℝ) i * g i ≤ ∑ i, (P : Fin d → ℝ) i * M :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hM i) (P.2.1 i))
      _ = M := by rw [← Finset.sum_mul, show ∑ i, (P : Fin d → ℝ) i = 1 from P.2.2, one_mul]
  -- weak duality
  have hW : ∀ α, M ≤ α → drPredictor γ r x ℙ' ≤ φ α := by
    intro α hα
    apply csSup_le ((Set.nonempty_of_mem hS).image _)
    rintro _ ⟨P, hP, rfl⟩
    have hw := weak g ℙ' P r hP α (fun i => (hM i).trans hα)
    have : ∑ i, (P : Fin d → ℝ) i * (α - g i) = α - ∑ i, (P : Fin d → ℝ) i * g i := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [show ∑ i, (P : Fin d → ℝ) i = 1 from P.2.2, one_mul]
    rw [this] at hw
    change cost γ x P ≤ _
    rw [hcostP]
    simp only [hφdef]
    linarith
  -- lower bound on φ
  have hL : ∀ α, M ≤ α → α - Real.exp (-r) * (α - c') ≤ φ α := by
    intro α hα
    have := ψ_le g p hp hp1 α (fun i => (hM i).trans hα)
    rw [← hc'] at this
    simp only [hφdef]
    nlinarith
  set B : ℝ := (M - Real.exp (-r) * c') / (1 - Real.exp (-r)) with hBdef
  have h1e : 0 < 1 - Real.exp (-r) := by linarith
  have hBeq : B * (1 - Real.exp (-r)) = M - Real.exp (-r) * c' := div_mul_cancel₀ _ h1e.ne'
  have hMB : M ≤ B := by
    rw [hBdef, le_div_iff₀ h1e]; nlinarith
  have hφM : φ M ≤ M := by
    simp only [hφdef]
    have := ψ_nonneg g p M hM
    nlinarith
  have hcont : Continuous φ := continuous_id.sub (continuous_const.mul (ψ_cont g p hp))
  obtain ⟨α₀, hα₀, hmin₀⟩ := (isCompact_Icc (a := M) (b := B)).exists_isMinOn
    (Set.nonempty_Icc.mpr hMB) hcont.continuousOn
  have hmin : ∀ β, M ≤ β → φ α₀ ≤ φ β := by
    intro β hβ
    by_cases hβB : β ≤ B
    · exact hmin₀ ⟨hβ, hβB⟩
    · push Not at hβB
      have h1 := hL β hβ
      have h2 : φ α₀ ≤ φ M := hmin₀ ⟨le_rfl, hMB⟩
      nlinarith
  obtain ⟨P, hP, hPc⟩ := strong g ℙ' r M hr hM j hj α₀ hα₀.1 hmin
  have hge : φ α₀ ≤ drPredictor γ r x ℙ' := by
    have : cost γ x P ≤ drPredictor γ r x ℙ' := le_csSup hbdd ⟨P, hP, rfl⟩
    rw [hcostP, hPc] at this
    exact this
  have heq : drPredictor γ r x ℙ' = φ α₀ := le_antisymm (hW α₀ hα₀.1) hge
  refine ⟨⟨⟨α₀, hα₀.1, heq⟩, ?_⟩, α₀, hα₀.1, hα₀.2, heq⟩
  rintro v ⟨α, hα, rfl⟩
  exact hW α hα
