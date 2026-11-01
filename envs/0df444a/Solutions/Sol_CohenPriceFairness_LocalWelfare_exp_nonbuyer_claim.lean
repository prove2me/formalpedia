-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.exp_nonbuyer_claim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:59.783184+00:00
-- url     : https://prove2.me/submissions/db9c08bf-08d0-4116-88aa-81459104ea61

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families
import Theorems.Thm_CohenPriceFairness_LocalWelfare_sensitivityClaim_of_local_data
import Theorems.Thm_CohenPriceFairness_LocalWelfare_exp_profit_regular
import Theorems.Thm_ExpLaw_cond_mean_below

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics Real Set

namespace CohenPriceFairness.LocalWelfare.Sol_exp_nonbuyer_claim

/-- `sensitivityClaim_of_local_data`, with the metric's continuity given on `Ioi 0`. -/
theorem eb_claim (m : Market) (b : Prices) (k : Metric) (C : ℝ → Prop) (r mm σ : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → profit m i p ≤ profit m i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p →
      |p - b i| < ε)
    (hRc : ∃ η > 0, ∀ i, ContinuousOn (profit m i) (Set.Icc (b i - η) (b i + η)))
    (hMc : ∀ i, ContinuousOn (metricValue m k i) (Ioi 0))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => profit m i (b i + h) - profit m i (b i) - r i / 2 * h ^ 2)
      =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (metricValue m k i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hSd : ∀ i, HasDerivAt (surplus m i) (σ i) (b i))
    (hgap : metricValue m k 0 (b 0) ≠ metricValue m k 1 (b 1))
    (hC : C (m.population 0 * σ 0 * ((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
        (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      m.population 1 * σ 1 * (-((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
        (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)))) :
    SensitivityClaim m b k C := by
  obtain ⟨η, hη, hRc⟩ := hRc
  refine sensitivityClaim_of_local_data m b k C r mm σ hb hopt hloc ?_ hr hRt hMd hmm hSd hgap hC
  have hm : 0 < min (b 0) (b 1) := lt_min (hb 0) (hb 1)
  refine ⟨min η (min (b 0) (b 1) / 2), lt_min hη (by positivity), fun i => ⟨(hRc i).mono ?_, (hMc i).mono ?_⟩⟩
  · have := min_le_left η (min (b 0) (b 1) / 2)
    exact Set.Icc_subset_Icc (by linarith) (by linarith)
  · intro p hp
    have hmin : min (b 0) (b 1) ≤ b i := by
      fin_cases i
      · exact min_le_left _ _
      · exact min_le_right _ _
    have := min_le_right η (min (b 0) (b 1) / 2)
    simp only [mem_Ioi]; linarith [hp.1]

lemma eb_pos_of_deriv (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x) (h0 : f 0 = 0)
    (hpos : ∀ x > 0, 0 < f' x) : ∀ x > 0, 0 < f x := by
  have hmono : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun x _ => (hf x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hf x).deriv]; exact hpos x hx
  intro x hx
  have := hmono (self_mem_Ici) (le_of_lt hx : (0:ℝ) ≤ x) hx
  rwa [h0] at this

lemma eb_anti_of_deriv (f f' : ℝ → ℝ) (a : ℝ) (hf : ∀ x > a, HasDerivAt f (f' x) x)
    (hneg : ∀ x > a, f' x < 0) : StrictAntiOn f (Ioi a) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi a)
  · exact fun x hx => (hf x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hf x hx).deriv]; exact hneg x hx

lemma eb_A_pos : ∀ x > 0, 0 < x * exp x - exp x + 1 := by
  apply eb_pos_of_deriv (fun x => x * exp x - exp x + 1) (fun x => x * exp x)
  · intro x
    have := (((hasDerivAt_id x).mul (hasDerivAt_exp x)).sub (hasDerivAt_exp x)).add_const 1
    exact this.congr_deriv (by simp)
  · simp
  · intro x hx; positivity

lemma eb_phi_pos : ∀ x > 0, 0 < x * (exp x + 1) - 2 * (exp x - 1) := by
  apply eb_pos_of_deriv _ (fun x => x * exp x - exp x + 1)
  · intro x
    have := ((hasDerivAt_id x).mul ((hasDerivAt_exp x).add_const 1)).sub
      (((hasDerivAt_exp x).sub_const 1).const_mul 2)
    exact this.congr_deriv (by simp; ring)
  · simp
  · exact eb_A_pos

lemma eb_psi1_pos : ∀ x > 0, 0 < exp x - 2 * exp (-x) - 2 * x + 1 := by
  apply eb_pos_of_deriv _ (fun x => exp x + 2 * exp (-x) - 2)
  · intro x
    have h1 := (hasDerivAt_exp x)
    have h2 := (hasDerivAt_neg x).exp
    have := ((h1.sub (h2.const_mul 2)).sub ((hasDerivAt_id x).const_mul 2)).add_const 1
    exact this.congr_deriv (by simp)
  · simp; norm_num
  · intro x hx
    have hts : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
    have h3 : 0 < exp (-x) := exp_pos _
    nlinarith [mul_pos h3 (by positivity : 0 < (exp x - 1)^2 + 1)]

lemma eb_psi_pos : ∀ x > 0, 0 < exp x + 2 * exp (-x) - (x ^ 2 - x + 3) := by
  apply eb_pos_of_deriv _ (fun x => exp x - 2 * exp (-x) - 2 * x + 1)
  · intro x
    have h1 := (hasDerivAt_exp x)
    have h2 := (hasDerivAt_neg x).exp
    have := (h1.add (h2.const_mul 2)).sub ((((hasDerivAt_id x).pow 2).sub (hasDerivAt_id x)).add_const 3)
    exact this.congr_deriv (by simp; ring)
  · simp; norm_num
  · exact eb_psi1_pos

/-! ## Monotonicity facts behind the nonbuyer sign -/

/-- g(x) = (e^x - 1 - x)/((x-1)(e^x-1)) -/
noncomputable def eb_g (x : ℝ) : ℝ := (exp x - 1 - x) / ((x - 1) * (exp x - 1))

/-- h(x) = (x e^x - e^x + 1)/(e^x-1)^2 -/
noncomputable def eb_h (x : ℝ) : ℝ := (x * exp x - exp x + 1) / (exp x - 1) ^ 2

lemma eb_g_anti : StrictAntiOn eb_g (Ioi 1) := by
  apply eb_anti_of_deriv eb_g
    (fun x => ((exp x - 1) * ((x - 1) * (exp x - 1)) - (exp x - 1 - x) * (x * exp x - 1)) /
      ((x - 1) * (exp x - 1)) ^ 2) 1
  · intro x hx
    have hx1 : x - 1 ≠ 0 := by linarith [show (1:ℝ) < x from hx]
    have he : exp x - 1 ≠ 0 := by
      have : 1 < exp x := one_lt_exp_iff.mpr (by linarith [show (1:ℝ) < x from hx])
      linarith
    have := (((hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id x)).div
      (((hasDerivAt_id x).sub_const 1).mul ((hasDerivAt_exp x).sub_const 1)) (mul_ne_zero hx1 he)
    exact this.congr_deriv (by simp only [Pi.mul_apply, Pi.sub_apply, id]; ring)
  · intro x hx
    have hx' : (1:ℝ) < x := hx
    have hts : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
    have hψ := eb_psi_pos x (by linarith)
    have hnum : (exp x - 1) * ((x - 1) * (exp x - 1)) - (exp x - 1 - x) * (x * exp x - 1) =
        -(exp x * (exp x + 2 * exp (-x) - (x ^ 2 - x + 3))) := by
      linear_combination 2 * hts
    rw [hnum]
    apply div_neg_of_neg_of_pos
    · have := exp_pos x; nlinarith
    · have : 1 < exp x := one_lt_exp_iff.mpr (by linarith)
      have : 0 < (x - 1) * (exp x - 1) := mul_pos (by linarith) (by linarith)
      positivity

lemma eb_h_pos : ∀ x > 0, 0 < eb_h x := by
  intro x hx
  unfold eb_h
  have : 1 < exp x := one_lt_exp_iff.mpr hx
  have := eb_A_pos x hx
  have : 0 < (exp x - 1) ^ 2 := by nlinarith
  positivity

lemma eb_h_anti : StrictAntiOn eb_h (Ioi 0) := by
  apply eb_anti_of_deriv eb_h
    (fun x => -(exp x * (x * (exp x + 1) - 2 * (exp x - 1))) / (exp x - 1) ^ 3) 0
  · intro x hx
    have he : exp x - 1 ≠ 0 := by
      have : 1 < exp x := one_lt_exp_iff.mpr hx
      linarith
    have := ((((hasDerivAt_id x).mul (hasDerivAt_exp x)).sub (hasDerivAt_exp x)).add_const 1).div
      (((hasDerivAt_exp x).sub_const 1).pow 2) (pow_ne_zero 2 he)
    exact this.congr_deriv (by simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id]; field_simp; ring)
  · intro x hx
    have : 1 < exp x := one_lt_exp_iff.mpr hx
    have hφ := eb_phi_pos x hx
    apply div_neg_of_neg_of_pos
    · have := exp_pos x; nlinarith [mul_pos this hφ]
    · have : 0 < exp x - 1 := by linarith
      positivity

noncomputable def eb_k (x : ℝ) : ℝ := eb_h x / (x - 1)

lemma eb_k_anti : StrictAntiOn eb_k (Ioi 1) := by
  intro a ha b hb hab
  have ha' : (1:ℝ) < a := ha
  have hb' : (1:ℝ) < b := hb
  unfold eb_k
  have h1 : eb_h b < eb_h a := eb_h_anti (show (0:ℝ) < a by linarith) (show (0:ℝ) < b by linarith) hab
  have h2 : 0 < eb_h b := eb_h_pos b (by linarith)
  calc eb_h b / (b - 1) < eb_h b / (a - 1) := by
        apply div_lt_div_of_pos_left h2 (by linarith) (by linarith)
    _ < eb_h a / (a - 1) := by apply div_lt_div_of_pos_right h1 (by linarith)


lemma eb_K_neg (mm r : Fin 2 → ℝ) (hr : ∀ i, r i < 0) (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0) :
    mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 < 0 := by
  have a0 : mm 0 ^ 2 / r 0 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hr 0).le
  have a1 : mm 1 ^ 2 / r 1 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hr 1).le
  rcases hmm with h | h
  · have : mm 0 ^ 2 / r 0 < 0 := div_neg_of_pos_of_neg (by positivity) (hr 0)
    linarith
  · have : mm 1 ^ 2 / r 1 < 0 := div_neg_of_pos_of_neg (by positivity) (hr 1)
    linarith

lemma eb_D_eq (w σ mm r : Fin 2 → ℝ) (G : ℝ) :
    w 0 * σ 0 * ((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      w 1 * σ 1 * (-((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)) =
    (G * (w 0 * σ 0 * mm 0 / r 0 - w 1 * σ 1 * mm 1 / r 1)) *
      (-(mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)⁻¹) := by
  ring

lemma eb_D_pos (w σ mm r : Fin 2 → ℝ) (G : ℝ) (hr : ∀ i, r i < 0) (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (h : 0 < G * (w 0 * σ 0 * mm 0 / r 0 - w 1 * σ 1 * mm 1 / r 1)) :
    0 < w 0 * σ 0 * ((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      w 1 * σ 1 * (-((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)) := by
  rw [eb_D_eq]
  have := eb_K_neg mm r hr hmm
  exact mul_pos h (neg_pos.mpr (inv_lt_zero.mpr this))


lemma eb_hasDerivAt_of_eq {f F : ℝ → ℝ} {F' p : ℝ} (hp : 0 < p) (heq : ∀ y, 0 < y → f y = F y)
    (hF : HasDerivAt F F' p) : HasDerivAt f F' p :=
  hF.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioi_mem_nhds hp) (fun y hy => heq y hy))

lemma eb_contOn {f f' : ℝ → ℝ} (hf : ∀ p, 0 < p → HasDerivAt f (f' p) p) :
    ContinuousOn f (Ioi 0) :=
  fun p hp => (hf p hp).continuousAt.continuousWithinAt

lemma eb_nonbuyer_eq (m : Market) (rate : Fin 2 → ℝ) (hrate : ∀ i, 0 < rate i)
    (hlaw : ∀ i, m.law i = expMeasure (rate i)) (i : Fin 2) {p : ℝ} (hp : 0 < p) :
    nonbuyer m i p = 1 / rate i - p / (exp (rate i * p) - 1) := by
  unfold nonbuyer; rw [hlaw i, ExpLaw.cond_mean_below (hrate i) hp]

lemma eb_nb_hasDeriv {l p : ℝ} (hl : 0 < l) (hp : 0 < p) :
    HasDerivAt (fun p => 1 / l - p / (exp (l * p) - 1)) (eb_h (l * p)) p := by
  have hne : exp (l * p) - 1 ≠ 0 := by
    have : 1 < exp (l * p) := one_lt_exp_iff.mpr (mul_pos hl hp)
    linarith
  have h1 := ((hasDerivAt_id' p).const_mul l).exp.sub_const 1
  have := (hasDerivAt_const p (1 / l)).sub ((hasDerivAt_id' p).div h1 hne)
  refine this.congr_deriv ?_
  unfold eb_h
  field_simp
  ring

lemma eb_lb {l : ℝ} (c : ℝ) (hl : 0 < l) : l * (c + 1 / l) = 1 + l * c := by
  field_simp; ring

lemma eb_X (d l q mm : Fin 2 → ℝ) (hd : ∀ i, 0 < d i) (hl : ∀ i, 0 < l i) (hq : ∀ i, 0 < q i) :
    d 0 * (-q 0) * mm 0 / (-(d 0 * l 0 * q 0)) - d 1 * (-q 1) * mm 1 / (-(d 1 * l 1 * q 1)) =
      mm 0 / l 0 - mm 1 / l 1 := by
  have := hd 0; have := hd 1; have := hl 0; have := hl 1; have := hq 0; have := hq 1
  field_simp

lemma eb_N_eq {l c : ℝ} (hl : 0 < l) (hc : 0 < c) :
    1 / l - (c + 1 / l) / (exp (l * (c + 1 / l)) - 1) = c * eb_g (1 + l * c) := by
  rw [eb_lb c hl]
  have hne : exp (1 + l * c) - 1 ≠ 0 := by
    have : 1 < exp (1 + l * c) := one_lt_exp_iff.mpr (by positivity)
    linarith
  unfold eb_g
  have : (1 + l * c - 1) = l * c := by ring
  rw [this]
  field_simp
  ring

lemma eb_n_eq {l c : ℝ} (hl : 0 < l) (hc : 0 < c) :
    eb_h (l * (c + 1 / l)) / l = c * eb_k (1 + l * c) := by
  rw [eb_lb c hl]
  unfold eb_k
  have : (1 + l * c - 1) = l * c := by ring
  rw [this]
  field_simp

lemma eb_sq_pos {G : ℝ} (hG : G ≠ 0) : 0 < G ^ 2 :=
  lt_of_le_of_ne (sq_nonneg G) (Ne.symm (pow_ne_zero 2 hG))

lemma eb_Dexp_pos (d l q mm : Fin 2 → ℝ) (G : ℝ) (hd : ∀ i, 0 < d i) (hl : ∀ i, 0 < l i)
    (hq : ∀ i, 0 < q i) (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0) (h : 0 < G * (mm 0 / l 0 - mm 1 / l 1)) :
    0 < d 0 * (-q 0) * ((-G / (mm 0 ^ 2 / (-(d 0 * l 0 * q 0)) + mm 1 ^ 2 / (-(d 1 * l 1 * q 1))))
        * mm 0 / (-(d 0 * l 0 * q 0))) +
      d 1 * (-q 1) * (-((-G / (mm 0 ^ 2 / (-(d 0 * l 0 * q 0)) + mm 1 ^ 2 / (-(d 1 * l 1 * q 1))))
        * mm 1 / (-(d 1 * l 1 * q 1)))) := by
  have hr : ∀ i, (fun i => -(d i * l i * q i)) i < 0 := fun i => by
    have := hd i; have := hl i; have := hq i
    simp only [neg_lt_zero]; positivity
  have := eb_D_pos d (fun i => -q i) mm (fun i => -(d i * l i * q i)) G hr hmm (by
    show 0 < G * (d 0 * (-q 0) * mm 0 / (-(d 0 * l 0 * q 0)) - d 1 * (-q 1) * mm 1 / (-(d 1 * l 1 * q 1)))
    rw [eb_X d l q mm hd hl hq]; exact h)
  exact this


end CohenPriceFairness.LocalWelfare.Sol_exp_nonbuyer_claim

open CohenPriceFairness.LocalWelfare CohenPriceFairness.LocalWelfare.Sol_exp_nonbuyer_claim
open MeasureTheory ProbabilityTheory Filter Topology Asymptotics Real Set

theorem solution (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 ≤ m.cost)
    (rate : Fin 2 → ℝ) (hrate : ∀ i, 0 < rate i) (hne : rate 0 ≠ rate 1)
    (hlaw : ∀ i, m.law i = expMeasure (rate i))
    (b : Prices) (hb : BaselineOptimal m b) :
    SensitivityClaim m b .nonbuyer (fun D => 0 < D) := by
  obtain ⟨hBO, hreg⟩ := exp_profit_regular m hd hc rate hrate hlaw
  obtain ⟨hbpos, hloc, hRc, hRt0, hSd0, hdem0⟩ := hreg b hb
  have hbi := (hBO b).1 hb
  have hopt : ∀ i, ∀ p, 0 ≤ p → profit m i p ≤ profit m i (b i) := fun i => (hb i).2
  obtain ⟨q, hq⟩ : ∃ q : Fin 2 → ℝ, ∀ i, q i = exp (-(1 + rate i * m.cost)) := ⟨_, fun _ => rfl⟩
  have hqpos : ∀ i, 0 < q i := fun i => by rw [hq i]; exact exp_pos _
  have hdem : ∀ i, demand m i (b i) = q i := fun i => by rw [hq i]; exact hdem0 i
  have hRt : ∀ i, (fun h => profit m i (b i + h) - profit m i (b i) -
      (fun i => -(m.population i * rate i * q i)) i / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2) :=
    fun i => by simp only [hq i]; exact hRt0 i
  have hr : ∀ i, (fun i => -(m.population i * rate i * q i)) i < 0 := fun i => by
    have := hd i; have := hrate i; have := hqpos i
    simp only [neg_lt_zero]; positivity
  have hSd : ∀ i, HasDerivAt (surplus m i) ((fun i => -q i) i) (b i) := fun i => by
    have := hSd0 i; rw [hdem i] at this; exact this
  have hNd : ∀ i, ∀ p, 0 < p →
      HasDerivAt (metricValue m .nonbuyer i) (eb_h (rate i * p)) p :=
    fun i p hp => eb_hasDerivAt_of_eq hp (fun y hy => eb_nonbuyer_eq m rate hrate hlaw i hy)
      (eb_nb_hasDeriv (hrate i) hp)
  have hsign : 0 < (metricValue m .nonbuyer 0 (b 0) - metricValue m .nonbuyer 1 (b 1)) *
      (eb_h (rate 0 * b 0) / rate 0 - eb_h (rate 1 * b 1) / rate 1) := by
    rcases hc.eq_or_lt with hzero | hcpos
    · -- c = 0: b i = 1 / rate i
      have hb1 : ∀ i, b i = 1 / rate i := fun i => by rw [hbi i, ← hzero, zero_add]
      have hl1 : ∀ i, rate i * b i = 1 := fun i => by
        rw [hb1 i]; field_simp [(hrate i).ne']
      have hv : ∀ i, metricValue m .nonbuyer i (b i) =
          (1 - 1 / (exp 1 - 1)) * (1 / rate i) := by
        intro i
        show nonbuyer m i (b i) = _
        rw [eb_nonbuyer_eq m rate hrate hlaw i (hbpos i), hl1 i, hb1 i]
        ring
      have he : 0 < 1 - 1 / (exp 1 - 1) := by
        have := exp_one_gt_d9
        rw [sub_pos, div_lt_one (by linarith)]; linarith
      have hh := eb_h_pos 1 one_pos
      have hG : 1 / rate 0 - 1 / rate 1 ≠ 0 := by
        intro h; apply hne
        have : 1 / rate 0 = 1 / rate 1 := by linarith
        simpa using this
      rw [hv 0, hv 1, hl1 0, hl1 1]
      have e : ((1 - 1 / (exp 1 - 1)) * (1 / rate 0) - (1 - 1 / (exp 1 - 1)) * (1 / rate 1)) *
          (eb_h 1 / rate 0 - eb_h 1 / rate 1) =
          ((1 - 1 / (exp 1 - 1)) * eb_h 1) * (1 / rate 0 - 1 / rate 1) ^ 2 := by ring
      rw [e]
      exact mul_pos (mul_pos he hh) (eb_sq_pos hG)
    have hx : ∀ i, 1 < 1 + rate i * m.cost := fun i => by
      have := hrate i; have : 0 < rate i * m.cost := by positivity
      linarith
    have hx01 : 1 + rate 0 * m.cost ≠ 1 + rate 1 * m.cost := by
      intro h; apply hne
      have : rate 0 * m.cost = rate 1 * m.cost := by linarith
      exact mul_right_cancel₀ hcpos.ne' this
    have hv : ∀ i, metricValue m .nonbuyer i (b i) = m.cost * eb_g (1 + rate i * m.cost) := by
      intro i
      show nonbuyer m i (b i) = _
      rw [eb_nonbuyer_eq m rate hrate hlaw i (hbpos i), hbi i]
      exact eb_N_eq (hrate i) hcpos
    have hn : ∀ i, eb_h (rate i * b i) / rate i = m.cost * eb_k (1 + rate i * m.cost) := by
      intro i; rw [hbi i]; exact eb_n_eq (hrate i) hcpos
    have hgk : 0 < (eb_g (1 + rate 0 * m.cost) - eb_g (1 + rate 1 * m.cost)) *
        (eb_k (1 + rate 0 * m.cost) - eb_k (1 + rate 1 * m.cost)) := by
      rcases lt_or_gt_of_ne hx01 with h | h
      · have h1 := eb_g_anti (hx 0) (hx 1) h
        have h2 := eb_k_anti (hx 0) (hx 1) h
        exact mul_pos (by linarith) (by linarith)
      · have h1 := eb_g_anti (hx 1) (hx 0) h
        have h2 := eb_k_anti (hx 1) (hx 0) h
        exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    rw [hv 0, hv 1, hn 0, hn 1]
    have : (m.cost * eb_g (1 + rate 0 * m.cost) - m.cost * eb_g (1 + rate 1 * m.cost)) *
        (m.cost * eb_k (1 + rate 0 * m.cost) - m.cost * eb_k (1 + rate 1 * m.cost)) =
        m.cost ^ 2 * ((eb_g (1 + rate 0 * m.cost) - eb_g (1 + rate 1 * m.cost)) *
        (eb_k (1 + rate 0 * m.cost) - eb_k (1 + rate 1 * m.cost))) := by ring
    rw [this]; positivity
  have hmm : (fun i => eb_h (rate i * b i)) 0 ≠ 0 ∨ (fun i => eb_h (rate i * b i)) 1 ≠ 0 :=
    Or.inl (eb_h_pos _ (mul_pos (hrate 0) (hbpos 0))).ne'
  have hgap : metricValue m .nonbuyer 0 (b 0) ≠ metricValue m .nonbuyer 1 (b 1) := by
    intro h
    rw [h, sub_self, zero_mul] at hsign; exact lt_irrefl _ hsign
  refine eb_claim m b .nonbuyer _ _ (fun i => eb_h (rate i * b i)) _ hbpos hopt hloc hRc
    (fun i => eb_contOn (hNd i)) hr hRt (fun i => hNd i (b i) (hbpos i)) hmm hSd hgap ?_
  exact eb_Dexp_pos m.population rate q (fun i => eb_h (rate i * b i))
    (metricValue m .nonbuyer 0 (b 0) - metricValue m .nonbuyer 1 (b 1)) hd hrate hqpos hmm hsign
