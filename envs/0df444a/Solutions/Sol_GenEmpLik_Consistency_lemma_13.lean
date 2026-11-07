-- Prove2me | solution 1 for GenEmpLik.Consistency.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:22:45.889275+00:00
-- url     : https://prove2.me/submissions/bcedc4cc-7352-48db-8ac8-7f364baeacf0

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet
import Definitions.Def_GenEmpLik_Coverage_AssumptionA

namespace GEL3L13

/-- Local quadratic lower bound near `1`. -/
lemma local_quad (f : ℝ → EReal) (hf : GenEmpLik.Coverage.AssumptionA f) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ u, |u - 1| ≤ δ → (u - 1) ^ 2 / 2 ≤ (f u).toReal := by
  obtain ⟨hphi, -, a, b, ha0, ha1, hb1, hcd, hd1, hd2⟩ := hf
  set g : ℝ → ℝ := fun t => (f t).toReal with hgdef
  have hU : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have h1U : (1 : ℝ) ∈ Set.Ioo a b := ⟨ha1, hb1⟩
  have hg1 : ContDiffOn ℝ 2 (deriv g) (Set.Ioo a b) := hcd.deriv_of_isOpen hU (by norm_num)
  have hg2 : ContDiffOn ℝ 1 (deriv (deriv g)) (Set.Ioo a b) := hg1.deriv_of_isOpen hU (by norm_num)
  have hdg : ∀ u ∈ Set.Ioo a b, HasDerivAt g (deriv g u) u := fun u hu =>
    ((hcd.differentiableOn (by norm_num)) u hu).differentiableAt (hU.mem_nhds hu) |>.hasDerivAt
  have hddg : ∀ u ∈ Set.Ioo a b, HasDerivAt (deriv g) (deriv (deriv g) u) u := fun u hu =>
    ((hg1.differentiableOn (by norm_num)) u hu).differentiableAt (hU.mem_nhds hu) |>.hasDerivAt
  have h2 : deriv (deriv g) 1 = 2 := by
    rw [← hd2, show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hcont : ContinuousAt (deriv (deriv g)) 1 :=
    (hg2.continuousOn).continuousAt (hU.mem_nhds h1U)
  obtain ⟨δ1, hδ1, hδ1'⟩ := Metric.continuousAt_iff.1 hcont 1 one_pos
  set δ := min (δ1 / 2) (min ((1 - a) / 2) ((b - 1) / 2)) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδ1le : δ ≤ δ1 / 2 := min_le_left _ _
  have hδa : δ ≤ (1 - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδb : δ ≤ (b - 1) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hI : ∀ u, |u - 1| ≤ δ → u ∈ Set.Ioo a b ∧ 1 ≤ deriv (deriv g) u := by
    intro u hu
    have hu' := abs_le.1 hu
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    have := hδ1' (x := u) (by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq, h2] at this
    have := (abs_lt.1 this).1
    linarith
  refine ⟨δ, hδpos, by linarith, ?_⟩
  -- k = g' - (u - 1)
  set I := Set.Icc (1 - δ) (1 + δ)
  have hIabs : ∀ u ∈ I, |u - 1| ≤ δ := fun u hu => abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hkmono : MonotoneOn (fun u => deriv g u - (u - 1)) I := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (f' := fun u => deriv (deriv g) u - 1) ?_ ?_ ?_
    · intro u hu
      exact ((hddg u (hI u (hIabs u hu)).1).sub ((hasDerivAt_id u).sub_const 1)).continuousAt.continuousWithinAt
    · intro u hu
      have hu' := interior_subset hu
      have := (hddg u (hI u (hIabs u hu')).1).sub ((hasDerivAt_id u).sub_const 1)
      exact this.hasDerivWithinAt
    · intro u hu
      have := (hI u (hIabs u (interior_subset hu))).2
      show 0 ≤ deriv (deriv g) u - 1; linarith
  have hk1 : deriv g 1 - (1 - 1) = 0 := by rw [hd1]; ring
  have hg10 : g 1 = 0 := by show (f 1).toReal = 0; rw [hphi.map_one]; rfl
  have hhder : ∀ u ∈ Set.Ioo a b, HasDerivAt (fun u => g u - (u - 1) ^ 2 / 2) (deriv g u - (u - 1)) u := by
    intro u hu
    have hq : HasDerivAt (fun x : ℝ => (x - 1) ^ 2 / 2) (u - 1) u :=
      ((((hasDerivAt_id' u).sub_const 1).pow 2).div_const 2).congr_deriv (by norm_num)
    exact (hdg u hu).sub hq
  have hIsub : ∀ u ∈ I, u ∈ Set.Ioo a b := fun u hu => (hI u (hIabs u hu)).1
  intro u hu
  have huI : u ∈ I := ⟨by linarith [(abs_le.1 hu).1], by linarith [(abs_le.1 hu).2]⟩
  have h1I : (1 : ℝ) ∈ I := ⟨by linarith, by linarith⟩
  rcases le_total 1 u with h | h
  · -- right side
    have hmono : MonotoneOn (fun u => g u - (u - 1) ^ 2 / 2) (Set.Icc 1 (1 + δ)) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
        (f' := fun u => deriv g u - (u - 1)) ?_ ?_ ?_
      · intro v hv
        exact (hhder v (hIsub v ⟨by linarith [hv.1], hv.2⟩)).continuousAt.continuousWithinAt
      · intro v hv
        have hv' := interior_subset hv
        exact (hhder v (hIsub v ⟨by linarith [hv'.1], hv'.2⟩)).hasDerivWithinAt
      · intro v hv
        have hv' := interior_subset hv
        have := hkmono h1I ⟨by linarith [hv'.1], hv'.2⟩ hv'.1
        simp only at this ⊢; linarith
    have := hmono ⟨le_rfl, by linarith⟩ ⟨h, huI.2⟩ h
    simp only [hg10] at this
    linarith
  · have hanti : AntitoneOn (fun u => g u - (u - 1) ^ 2 / 2) (Set.Icc (1 - δ) 1) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
        (f' := fun u => deriv g u - (u - 1)) ?_ ?_ ?_
      · intro v hv
        exact (hhder v (hIsub v ⟨hv.1, by linarith [hv.2]⟩)).continuousAt.continuousWithinAt
      · intro v hv
        have hv' := interior_subset hv
        exact (hhder v (hIsub v ⟨hv'.1, by linarith [hv'.2]⟩)).hasDerivWithinAt
      · intro v hv
        have hv' := interior_subset hv
        have := hkmono ⟨hv'.1, by linarith [hv'.2]⟩ h1I hv'.2
        simp only at this ⊢; linarith
    have := hanti ⟨huI.1, h⟩ ⟨by linarith, le_rfl⟩ h
    simp only [hg10] at this
    linarith


lemma global_lower (f : ℝ → EReal) (hf : GenEmpLik.Coverage.AssumptionA f) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ u, 0 ≤ u → f u ≠ ⊤ →
      (|u - 1| ≤ δ → (u - 1) ^ 2 / 2 ≤ (f u).toReal) ∧
      (δ ≤ |u - 1| → δ / 2 * |u - 1| ≤ (f u).toReal) := by
  obtain ⟨δ, hδ0, hδ1, hloc⟩ := local_quad f hf
  have hphi := hf.1
  refine ⟨δ, hδ0, hδ1, fun u hu0 hutop => ⟨hloc u, fun hfar => ?_⟩⟩
  have hfu : f u = ((f u).toReal : EReal) := (EReal.coe_toReal hutop (hphi.ne_bot u)).symm
  rcases le_total 1 u with h1 | h1
  · have hu1 : |u - 1| = u - 1 := abs_of_nonneg (by linarith)
    rw [hu1] at hfar ⊢
    have hne : u - 1 ≠ 0 := (show (0:ℝ) < u - 1 by linarith).ne'
    set θ := δ / (u - 1)
    have hθ0 : 0 ≤ θ := div_nonneg hδ0.le (by linarith)
    have hθ1 : θ ≤ 1 := (div_le_one (by linarith)).2 hfar
    have hconv := hphi.convex u 1 θ hu0 zero_le_one hθ0 hθ1
    rw [hphi.map_one, mul_zero, add_zero] at hconv
    have heq : θ * u + (1 - θ) * 1 = 1 + δ := by
      simp only [θ]; field_simp; ring
    rw [heq, hfu, ← EReal.coe_toReal (hphi.ne_top_of_pos (1 + δ) (by linarith))
      (hphi.ne_bot _), ← EReal.coe_mul, EReal.coe_le_coe_iff] at hconv
    have hq := hloc (1 + δ) (by rw [show 1 + δ - 1 = δ by ring, abs_of_pos hδ0])
    rw [show 1 + δ - 1 = δ by ring] at hq
    have hmul : θ * (f u).toReal * (u - 1) = δ * (f u).toReal := by
      simp only [θ]; field_simp
    have : δ ^ 2 / 2 * (u - 1) ≤ δ * (f u).toReal := by
      rw [← hmul]; exact mul_le_mul_of_nonneg_right (hq.trans hconv) (by linarith)
    nlinarith
  · have hu1 : |u - 1| = 1 - u := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [hu1] at hfar ⊢
    have hne : 1 - u ≠ 0 := (show (0:ℝ) < 1 - u by linarith).ne'
    set θ := δ / (1 - u)
    have hθ0 : 0 ≤ θ := div_nonneg hδ0.le (by linarith)
    have hθ1 : θ ≤ 1 := (div_le_one (by linarith)).2 hfar
    have hconv := hphi.convex u 1 θ hu0 zero_le_one hθ0 hθ1
    rw [hphi.map_one, mul_zero, add_zero] at hconv
    have heq : θ * u + (1 - θ) * 1 = 1 - δ := by
      simp only [θ]; field_simp; ring
    rw [heq, hfu, ← EReal.coe_toReal (hphi.ne_top_of_pos (1 - δ) (by linarith))
      (hphi.ne_bot _), ← EReal.coe_mul, EReal.coe_le_coe_iff] at hconv
    have hq := hloc (1 - δ) (by rw [show 1 - δ - 1 = -δ by ring, abs_neg, abs_of_pos hδ0])
    rw [show 1 - δ - 1 = -δ by ring] at hq
    have hmul : θ * (f u).toReal * (1 - u) = δ * (f u).toReal := by
      simp only [θ]; field_simp
    have : (-δ) ^ 2 / 2 * (1 - u) ≤ δ * (f u).toReal := by
      rw [← hmul]; exact mul_le_mul_of_nonneg_right (hq.trans hconv) (by linarith)
    nlinarith


lemma pointwise (f : ℝ → EReal) (hf : GenEmpLik.Coverage.AssumptionA f) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ u, 0 ≤ u → f u ≠ ⊤ →
      0 ≤ (f u).toReal ∧ ((f u).toReal ≤ ρ → (u - 1) ^ 2 ≤ K * (f u).toReal) := by
  obtain ⟨δ, hδ0, hδ1, hb⟩ := global_lower f hf
  set c := δ / 2 with hc
  have hc0 : 0 < c := by positivity
  refine ⟨max 2 (ρ / c ^ 2), lt_of_lt_of_le two_pos (le_max_left _ _), fun u hu0 hut => ?_⟩
  obtain ⟨hnear, hfar⟩ := hb u hu0 hut
  rcases le_total |u - 1| δ with h | h
  · have h1 := hnear h
    have hg0 : 0 ≤ (f u).toReal := le_trans (by positivity) h1
    refine ⟨hg0, fun _ => ?_⟩
    have := mul_le_mul_of_nonneg_right (le_max_left 2 (ρ / c ^ 2)) hg0
    linarith
  · have h1 := hfar h
    have hg0 : 0 ≤ (f u).toReal := le_trans (by positivity) h1
    refine ⟨hg0, fun hgρ => ?_⟩
    have h2 : c * |u - 1| ≤ ρ := h1.trans hgρ
    have h3 : (c * |u - 1|) * (c * |u - 1|) ≤ (f u).toReal * ρ :=
      mul_le_mul h1 h2 (by positivity) hg0
    have h4 : (u - 1) ^ 2 ≤ ρ / c ^ 2 * (f u).toReal := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), ← sq_abs]
      nlinarith
    exact h4.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hg0)

lemma ereal_sum_coe {n : ℕ} (a : Fin n → ℝ) (s : Finset (Fin n)) :
    ∑ i ∈ s, (a i : EReal) = ((∑ i ∈ s, a i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, ih, EReal.coe_add]

lemma uniform_mem {n : ℕ} (hn : 0 < n) (f : ℝ → EReal) (hf1 : f 1 = 0) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (fun _ : Fin n => (1 : ℝ) / n) ∈
      PhiDivRobust.Counterpart.probUncertaintySet f (fun _ => (1 : ℝ) / n) (ρ / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨fun i => by positivity, ?_, ?_⟩
  · simp [Finset.sum_const, Finset.card_univ]; field_simp
  · unfold PhiDivRobust.Counterpart.phiDiv
    have : ((1 : ℝ) / n) / ((1 : ℝ) / n) = 1 := div_self (by positivity)
    simp only [this, hf1, mul_zero, Finset.sum_const_zero]
    exact_mod_cast (by positivity : (0 : ℝ) ≤ ρ / n)

end GEL3L13

open GEL3L13 in
theorem solution (f : ℝ → EReal) (hf : GenEmpLik.Coverage.AssumptionA f) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ cf Cf : ℝ, 0 < cf ∧ cf ≤ Cf ∧
      (∀ n : ℕ, 0 < n → ∀ p ∈ PhiDivRobust.Counterpart.probUncertaintySet f
          (fun _ : Fin n => (1 : ℝ) / n) (ρ / n),
        Real.sqrt (∑ i, ((n : ℝ) * p i - 1) ^ 2) ≤ Real.sqrt (ρ * Cf)) ∧
      (∃ n : ℕ, 0 < n ∧ ∃ p ∈ PhiDivRobust.Counterpart.probUncertaintySet f
          (fun _ : Fin n => (1 : ℝ) / n) (ρ / n),
        Real.sqrt (ρ * cf) ≤ Real.sqrt (∑ i, ((n : ℝ) * p i - 1) ^ 2)) := by
  have hphi := hf.1
  obtain ⟨K, hK0, hK⟩ := pointwise f hf ρ hρ
  -- the lower witness
  obtain ⟨cf, hcf0, hlow⟩ : ∃ cf : ℝ, 0 < cf ∧ (∃ n : ℕ, 0 < n ∧ ∃ p ∈ PhiDivRobust.Counterpart.probUncertaintySet f
          (fun _ : Fin n => (1 : ℝ) / n) (ρ / n),
        Real.sqrt (ρ * cf) ≤ Real.sqrt (∑ i, ((n : ℝ) * p i - 1) ^ 2)) := by
    rcases hρ.eq_or_lt with h0 | hpos
    · refine ⟨1, one_pos, 1, one_pos, _, uniform_mem one_pos f hphi.map_one ρ hρ, ?_⟩
      rw [← h0]; simp
    · obtain ⟨-, -, a, b, ha0, ha1, hb1, hcd, -, -⟩ := hf
      have hcont : ContinuousAt (fun t => (f t).toReal) 1 :=
        (hcd.continuousOn).continuousAt (isOpen_Ioo.mem_nhds ⟨ha1, hb1⟩)
      obtain ⟨η, hη, hη'⟩ := Metric.continuousAt_iff.1 hcont (ρ / 2) (by positivity)
      set t := min (η / 4) (1 / 4) with ht
      have ht0 : 0 < t := lt_min (by positivity) (by norm_num)
      have htη : t ≤ η / 4 := min_le_left _ _
      have ht4 : t ≤ 1 / 4 := min_le_right _ _
      have hg1 : (f 1).toReal = 0 := by rw [hphi.map_one]; rfl
      have hsmall : ∀ v, |v - 1| < η → (f v).toReal < ρ / 2 := fun v hv => by
        have := hη' (x := v) (by rwa [Real.dist_eq])
        rw [Real.dist_eq, hg1, sub_zero] at this
        exact (abs_lt.1 this).2
      refine ⟨8 * t ^ 2 / ρ, by positivity, 2, two_pos, ![1 / 2 + t, 1 / 2 - t], ⟨?_, ?_, ?_⟩, ?_⟩
      · intro i; fin_cases i <;> simp <;> linarith
      · simp [Fin.sum_univ_two]; norm_num
      · unfold PhiDivRobust.Counterpart.phiDiv
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        have e1 : (1 / 2 + t) / (1 / ((2 : ℕ) : ℝ)) = 1 + 2 * t := by push_cast; field_simp
        have e2 : (1 / 2 - t) / (1 / ((2 : ℕ) : ℝ)) = 1 - 2 * t := by push_cast; field_simp
        rw [e1, e2, ← EReal.coe_toReal (hphi.ne_top_of_pos (1 + 2 * t) (by linarith))
          (hphi.ne_bot _), ← EReal.coe_toReal (hphi.ne_top_of_pos (1 - 2 * t) (by linarith))
          (hphi.ne_bot _), ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
        have h1 := hsmall (1 + 2 * t) (by rw [show 1 + 2 * t - 1 = 2 * t by ring, abs_of_pos (by linarith)]; linarith)
        have h2 := hsmall (1 - 2 * t) (by rw [show 1 - 2 * t - 1 = -(2 * t) by ring, abs_neg, abs_of_pos (by linarith)]; linarith)
        push_cast
        linarith
      · apply Real.sqrt_le_sqrt
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        push_cast
        field_simp
        ring_nf
        exact le_refl _
  refine ⟨cf, max K cf, hcf0, le_max_right _ _, fun n hn p hp => ?_, hlow⟩
  apply Real.sqrt_le_sqrt
  obtain ⟨hp0, hp1, hdiv⟩ := hp
  unfold PhiDivRobust.Counterpart.phiDiv at hdiv
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hu : ∀ i, p i / (1 / (n : ℝ)) = n * p i := fun i => by field_simp
  simp only [hu] at hdiv
  have hu0 : ∀ i, 0 ≤ (n : ℝ) * p i := fun i => mul_nonneg hnR.le (hp0 i)
  have hf0 : ∀ i, 0 ≤ f ((n : ℝ) * p i) := fun i => by
    by_cases htop : f ((n : ℝ) * p i) = ⊤
    · rw [htop]; exact le_top
    · rw [← EReal.coe_toReal htop (hphi.ne_bot _)]
      exact_mod_cast (hK _ (hu0 i) htop).1
  have hterm0 : ∀ i, 0 ≤ (((1 : ℝ) / n : ℝ) : EReal) * f ((n : ℝ) * p i) := fun i =>
    mul_nonneg (by exact_mod_cast (by positivity : (0 : ℝ) ≤ 1 / n)) (hf0 i)
  have hfin : ∀ i, f ((n : ℝ) * p i) ≠ ⊤ := by
    intro i htop
    have := (Finset.single_le_sum (fun j _ => hterm0 j) (Finset.mem_univ i)).trans hdiv
    rw [htop, EReal.mul_top_of_pos (by exact_mod_cast (by positivity : (0 : ℝ) < 1 / n))] at this
    exact absurd this (by simp)
  have hrw : ∀ i, (((1 : ℝ) / n : ℝ) : EReal) * f ((n : ℝ) * p i) =
      (((1 : ℝ) / n * (f ((n : ℝ) * p i)).toReal : ℝ) : EReal) := fun i => by
    rw [EReal.coe_mul, EReal.coe_toReal (hfin i) (hphi.ne_bot _)]
  simp only [hrw] at hdiv
  rw [ereal_sum_coe, EReal.coe_le_coe_iff, ← Finset.mul_sum, div_eq_mul_one_div ρ n,
    mul_comm ρ] at hdiv
  have hS := le_of_mul_le_mul_left hdiv (by positivity)
  have hg0 : ∀ i, 0 ≤ (f ((n : ℝ) * p i)).toReal := fun i => (hK _ (hu0 i) (hfin i)).1
  have hgρ : ∀ i, (f ((n : ℝ) * p i)).toReal ≤ ρ := fun i =>
    (Finset.single_le_sum (fun j _ => hg0 j) (Finset.mem_univ i)).trans hS
  calc ∑ i, ((n : ℝ) * p i - 1) ^ 2 ≤ ∑ i, K * (f ((n : ℝ) * p i)).toReal :=
        Finset.sum_le_sum fun i _ => (hK _ (hu0 i) (hfin i)).2 (hgρ i)
    _ = K * ∑ i, (f ((n : ℝ) * p i)).toReal := by rw [Finset.mul_sum]
    _ ≤ K * ρ := mul_le_mul_of_nonneg_left hS hK0.le
    _ ≤ max K cf * ρ := mul_le_mul_of_nonneg_right (le_max_left _ _) hρ
    _ = ρ * max K cf := mul_comm _ _
