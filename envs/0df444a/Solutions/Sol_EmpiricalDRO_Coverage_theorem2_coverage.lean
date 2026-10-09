-- Prove2me | solution 1 for EmpiricalDRO.Coverage.theorem2_coverage
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T22:02:52.628553+00:00
-- url     : https://prove2.me/submissions/c54ada85-d862-4f61-a8a4-38028e7cc55a

import Mathlib
import Definitions.Def_EmpiricalDRO_Coverage_Setting
open MeasureTheory ProbabilityTheory Filter Topology
set_option autoImplicit false

namespace EDRO

lemma log_cubic (x : ℝ) (hx : |x| ≤ 1/2) :
    |Real.log (1 + x) - x + x ^ 2 / 2| ≤ 2 * |x| ^ 3 := by
  have h1 : |(-x)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have e : (1 : ℝ) - -x = 1 + x := by ring
  rw [e] at h
  have e2 : (0 + (-x) ^ (0 + 1) / ((0 : ℕ) + 1) + (-x) ^ (1 + 1) / ((1 : ℕ) + 1) + Real.log (1 + x))
      = Real.log (1 + x) - x + x ^ 2 / 2 := by push_cast; ring
  rw [e2, abs_neg] at h
  refine h.trans ?_
  have hp : 0 ≤ |x| ^ 3 := by positivity
  have : |x| ^ (2 + 1) / (1 - |x|) ≤ 2 * |x| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    have e3 : |x| ^ (2 + 1) = |x| ^ 3 := by norm_num
    rw [e3]
    nlinarith [hp, mul_nonneg hp (sub_nonneg.2 hx)]
  exact this

lemma ecoe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) :=
  by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

/-- the real-valued ball -/
def RBall (n : ℕ) (ρ : ℝ) : Set (Fin n → ℝ) :=
  {w | (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ -∑ i, Real.log (n * w i) ≤ ρ}

lemma burg_pos {t : ℝ} (ht : 0 < t) :
    EmpiricalDRO.Coverage.burg t = ((-Real.log t + t - 1 : ℝ) : EReal) := by
  simp [EmpiricalDRO.Coverage.burg, ht]

lemma burg_nonneg (t : ℝ) : (0 : EReal) ≤ EmpiricalDRO.Coverage.burg t := by
  unfold EmpiricalDRO.Coverage.burg
  split_ifs with ht
  · have := Real.log_le_sub_one_of_pos ht
    exact_mod_cast (by linarith : (0:ℝ) ≤ -Real.log t + t - 1)
  · exact le_top

lemma ball_eq (n : ℕ) (hn : 0 < n) (ρ : ℝ) :
    PhiDivRobust.Counterpart.probUncertaintySet EmpiricalDRO.Coverage.burg
      (fun _ => (1 : ℝ) / n) (ρ / n) = RBall n ρ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  ext w
  unfold PhiDivRobust.Counterpart.probUncertaintySet RBall PhiDivRobust.Counterpart.phiDiv
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0, hs, hd⟩
    have hpos : ∀ i, 0 < w i := by
      intro i
      by_contra hcon
      have hwi : w i = 0 := le_antisymm (not_lt.mp hcon) (h0 i)
      have hterm : ((1 / n : ℝ) : EReal) * EmpiricalDRO.Coverage.burg (w i / (1 / n)) = ⊤ := by
        have : w i / (1 / (n:ℝ)) = 0 := by rw [hwi]; simp
        rw [this]
        have hb : EmpiricalDRO.Coverage.burg 0 = ⊤ := by simp [EmpiricalDRO.Coverage.burg]
        rw [hb]
        exact EReal.coe_mul_top_of_pos (by positivity)
      have hle : ((1 / n : ℝ) : EReal) * EmpiricalDRO.Coverage.burg (w i / (1 / n)) ≤
          ∑ j, ((1 / n : ℝ) : EReal) * EmpiricalDRO.Coverage.burg (w j / (1 / n)) :=
        Finset.single_le_sum (f := fun j => ((1 / n : ℝ) : EReal) * EmpiricalDRO.Coverage.burg (w j / (1 / n)))
          (fun j _ => mul_nonneg (by exact_mod_cast (by positivity : (0:ℝ) ≤ 1 / n)) (burg_nonneg _))
          (Finset.mem_univ i)
      rw [hterm] at hle
      have := hle.trans hd
      exact absurd this (by simp)
    refine ⟨hpos, hs, ?_⟩
    have hsum : (∑ i, ((1 / n : ℝ) : EReal) * EmpiricalDRO.Coverage.burg (w i / (1 / n)))
        = ((∑ i, (1 / n : ℝ) * (-Real.log (n * w i) + n * w i - 1) : ℝ) : EReal) := by
      rw [ecoe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : w i / (1 / (n:ℝ)) = n * w i := by field_simp
      rw [this, burg_pos (mul_pos hn' (hpos i))]
      exact (EReal.coe_mul _ _).symm
    rw [hsum] at hd
    have hd' := EReal.coe_le_coe_iff.mp hd
    have e : ∑ i, (1 / n : ℝ) * (-Real.log (n * w i) + n * w i - 1)
        = (1 / n) * (-∑ i, Real.log (n * w i)) := by
      have : ∑ i, (1 / n : ℝ) * (-Real.log (n * w i) + n * w i - 1)
          = (1 / n) * (-∑ i, Real.log (n * w i)) + (∑ i, w i) - 1 := by
        simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_neg_distrib]
        field_simp
      rw [this, hs]; ring
    rw [e] at hd'
    have : (1 / (n:ℝ)) * (-∑ i, Real.log (n * w i)) ≤ (1 / (n:ℝ)) * ρ := by
      calc _ ≤ ρ / n := hd'
        _ = _ := by ring
    exact le_of_mul_le_mul_left this (by positivity)
  · rintro ⟨hpos, hs, hd⟩
    refine ⟨fun i => (hpos i).le, hs, ?_⟩
    have hsum : (∑ i, ((1 / n : ℝ) : EReal) * EmpiricalDRO.Coverage.burg (w i / (1 / n)))
        = ((∑ i, (1 / n : ℝ) * (-Real.log (n * w i) + n * w i - 1) : ℝ) : EReal) := by
      rw [ecoe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : w i / (1 / (n:ℝ)) = n * w i := by field_simp
      rw [this, burg_pos (mul_pos hn' (hpos i))]
      exact (EReal.coe_mul _ _).symm
    rw [hsum]
    apply EReal.coe_le_coe_iff.mpr
    have e : ∑ i, (1 / n : ℝ) * (-Real.log (n * w i) + n * w i - 1)
        = (1 / n) * (-∑ i, Real.log (n * w i)) := by
      have : ∑ i, (1 / n : ℝ) * (-Real.log (n * w i) + n * w i - 1)
          = (1 / n) * (-∑ i, Real.log (n * w i)) + (∑ i, w i) - 1 := by
        simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_neg_distrib]
        field_simp
      rw [this, hs]; ring
    rw [e]
    calc (1 / (n:ℝ)) * (-∑ i, Real.log (n * w i)) ≤ (1 / (n:ℝ)) * ρ :=
          mul_le_mul_of_nonneg_left hd (by positivity)
      _ = ρ / n := by ring

lemma RBall_convex (n : ℕ) (ρ : ℝ) : Convex ℝ (RBall n ρ) := by
  intro w1 h1 w2 h2 a b ha hb hab
  obtain ⟨p1, s1, l1⟩ := h1
  obtain ⟨p2, s2, l2⟩ := h2
  have hpos : ∀ i, 0 < (a • w1 + b • w2) i := by
    intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le ha with h | h
    · have hb1 : b = 1 := by linarith
      rw [← h, hb1]; simpa using p2 i
    · have := mul_pos h (p1 i)
      have := mul_nonneg hb (p2 i).le
      linarith
  refine ⟨hpos, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, s1, s2]
    linarith
  · have key : ∀ i, a * Real.log (n * w1 i) + b * Real.log (n * w2 i) ≤
        Real.log (n * (a • w1 + b • w2) i) := by
      intro i
      by_cases hn : (n : ℝ) = 0
      · simp [hn]
      have hn' : 0 < (n : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg n) (Ne.symm hn)
      have hc := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.2 (mul_pos hn' (p1 i)))
        (Set.mem_Ioi.2 (mul_pos hn' (p2 i))) ha hb hab
      simp only [smul_eq_mul] at hc
      have e : (n : ℝ) * (a • w1 + b • w2) i = a * (n * w1 i) + b * (n * w2 i) := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [e]; exact hc
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
    have e1 := mul_le_mul_of_nonneg_left l1 ha
    have e2 := mul_le_mul_of_nonneg_left l2 hb
    have e3 : a * ρ + b * ρ = ρ := by rw [← add_mul, hab, one_mul]
    linarith

lemma lin_sum_isLinear {n : ℕ} (z : Fin n → ℝ) :
    IsLinearMap ℝ (fun p : Fin n → ℝ => ∑ i, p i * z i) := by
  constructor
  · intro x y; simp [add_mul, Finset.sum_add_distrib]
  · intro c x; simp [Finset.mul_sum, mul_assoc]

lemma bdd_image {n : ℕ} (z : Fin n → ℝ) (ρ : ℝ) :
    BddBelow ((fun p : Fin n → ℝ => ∑ i, p i * z i) '' RBall n ρ) ∧
    BddAbove ((fun p : Fin n → ℝ => ∑ i, p i * z i) '' RBall n ρ) := by
  have key : ∀ p ∈ RBall n ρ, |∑ i, p i * z i| ≤ ∑ i, |z i| := by
    rintro p ⟨hp, hs, -⟩
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_pos (hp i)]
    have : p i ≤ 1 := by
      rw [← hs]
      exact Finset.single_le_sum (f := p) (fun j _ => (hp j).le) (Finset.mem_univ i)
    nlinarith [abs_nonneg (z i)]
  constructor
  · refine ⟨-∑ i, |z i|, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    linarith [(abs_le.1 (key p hp)).1]
  · refine ⟨∑ i, |z i|, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    linarith [(abs_le.1 (key p hp)).2]

lemma uniform_mem {n : ℕ} (hn : 0 < n) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (fun _ : Fin n => (1 : ℝ) / n) ∈ RBall n ρ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨fun _ => by positivity, ?_, ?_⟩
  · simp; field_simp
  · have : ∀ i : Fin n, Real.log (n * (1 / (n:ℝ))) = 0 := fun i => by
      rw [mul_one_div_cancel hn'.ne']; simp
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    simpa using hρ

lemma approx_of_mem {n : ℕ} (hn : 0 < n) {ρ : ℝ} (hρ : 0 ≤ ρ) (z : Fin n → ℝ) (μ : ℝ)
    (hlo : sInf ((fun p : Fin n → ℝ => ∑ i, p i * z i) '' RBall n ρ) ≤ μ)
    (hhi : μ ≤ sSup ((fun p : Fin n → ℝ => ∑ i, p i * z i) '' RBall n ρ)) :
    ∀ δ > 0, ∃ w ∈ RBall n ρ, |∑ i, w i * z i - μ| < δ := by
  intro δ hδ
  set I := (fun p : Fin n → ℝ => ∑ i, p i * z i) '' RBall n ρ with hI
  have hne : I.Nonempty := ⟨_, _, uniform_mem hn hρ, rfl⟩
  obtain ⟨hbb, hba⟩ := bdd_image z ρ
  obtain ⟨a, ⟨wa, hwa, rfl⟩, ha⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right (sInf I) hδ)
  obtain ⟨b, ⟨wb, hwb, rfl⟩, hb⟩ := exists_lt_of_lt_csSup hne (sub_lt_self (sSup I) hδ)
  by_cases h1 : μ ≤ ∑ i, wa i * z i
  · refine ⟨wa, hwa, ?_⟩
    rw [abs_of_nonneg (by linarith)]; linarith
  by_cases h2 : ∑ i, wb i * z i ≤ μ
  · refine ⟨wb, hwb, ?_⟩
    rw [abs_of_nonpos (by linarith)]; linarith
  push_neg at h1 h2
  have hconv : Convex ℝ I := (RBall_convex n ρ).is_linear_image (lin_sum_isLinear z)
  have hoc : Set.OrdConnected I := hconv.ordConnected
  have hmem : μ ∈ I := hoc.out ⟨wa, hwa, rfl⟩ ⟨wb, hwb, rfl⟩ ⟨h1.le, h2.le⟩
  obtain ⟨w, hw, hwe⟩ := hmem
  exact ⟨w, hw, by simp only at hwe; rw [hwe]; simpa using hδ⟩

lemma mem_of_exact {n : ℕ} {ρ : ℝ} (z : Fin n → ℝ) (μ : ℝ) (w : Fin n → ℝ) (hw : w ∈ RBall n ρ)
    (he : ∑ i, w i * z i = μ) :
    sInf ((fun p : Fin n → ℝ => ∑ i, p i * z i) '' RBall n ρ) ≤ μ ∧
    μ ≤ sSup ((fun p : Fin n → ℝ => ∑ i, p i * z i) '' RBall n ρ) := by
  obtain ⟨hbb, hba⟩ := bdd_image z ρ
  exact ⟨csInf_le hbb ⟨w, hw, he⟩, le_csSup hba ⟨w, hw, he⟩⟩

lemma up_mem {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ) (q M m S v : ℝ)
    (hm : ∑ i, y i = n * m) (hS : ∑ i, y i ^ 2 = n * S) (hvd : v = S - m ^ 2) (hv : 0 < v)
    (hM : ∀ i, |m / v * (m - y i)| ≤ M) (hM2 : M ≤ 1 / 2)
    (hq : n * m ^ 2 / v * (1 + 4 * M) ≤ q) :
    ∃ w ∈ RBall n (q / 2), ∑ i, w i * y i = 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨t, ht⟩ : ∃ t : Fin n → ℝ, ∀ i, t i = m / v * (m - y i) := ⟨_, fun _ => rfl⟩
  have ht1 : ∀ i, |t i| ≤ M := fun i => by rw [ht]; exact hM i
  have ht2 : ∀ i, 1 / 2 ≤ 1 + t i := fun i => by
    have := (abs_le.1 ((ht1 i).trans hM2)).1; linarith
  have hsum_t : ∑ i, t i = 0 := by
    simp only [ht, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hm]
    ring
  have hsum_ty : ∑ i, t i * y i = -(n * m) := by
    have : ∑ i, t i * y i = m / v * (m * ∑ i, y i - ∑ i, y i ^ 2) := by
      simp only [ht, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, hm, hS]
    field_simp
    rw [hvd]; ring
  have hsum_tt : ∑ i, t i ^ 2 = n * m ^ 2 / v := by
    have e1 : ∀ i, t i ^ 2 = (m / v) ^ 2 * (m ^ 2 - 2 * m * y i + y i ^ 2) := fun i => by
      simp only [ht]; ring
    simp_rw [e1]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hm, hS]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    rw [hvd]; ring
  have hlog : ∀ i, -Real.log (1 + t i) ≤ -t i + (1 / 2 + 2 * M) * t i ^ 2 := by
    intro i
    have h1 := log_cubic (t i) ((ht1 i).trans hM2)
    have h2 := (abs_le.1 h1).1
    have h3 : |t i| ^ 3 ≤ M * t i ^ 2 := by
      have : |t i| ^ 3 = |t i| * t i ^ 2 := by
        rw [pow_succ, sq_abs]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (ht1 i) (sq_nonneg _)
    nlinarith
  refine ⟨fun i => (1 + t i) / n, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    have := ht2 i
    positivity
  · rw [← Finset.sum_div, Finset.sum_add_distrib, hsum_t]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  · have e : ∀ i : Fin n, (n : ℝ) * ((1 + t i) / n) = 1 + t i := fun i => by field_simp
    simp_rw [e]
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlog i)
    rw [Finset.sum_neg_distrib] at this
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, hsum_t, hsum_tt] at this
    have hK : 0 ≤ (n : ℝ) * m ^ 2 / v := by positivity
    nlinarith
  · have e : ∀ i, (1 + t i) / n * y i = (y i + t i * y i) / n := fun i => by ring
    simp_rw [e]
    rw [← Finset.sum_div, Finset.sum_add_distrib, hm, hsum_ty]
    simp

lemma low_bound {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ) (ρ lam : ℝ) (w : Fin n → ℝ) (hw : w ∈ RBall n ρ)
    (hl : ∀ i, |lam * y i| ≤ 1 / 2) (δ : ℝ) (hδ : |∑ i, w i * y i| ≤ δ) :
    ∑ i, Real.log (1 + lam * y i) ≤ ρ + |lam| * n * δ := by
  obtain ⟨hp, hs, hlog⟩ := hw
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ∀ i, Real.log (n * w i) + Real.log (1 + lam * y i) ≤
      n * w i * (1 + lam * y i) - 1 := by
    intro i
    have h1 : 0 < n * w i := mul_pos hn' (hp i)
    have h2 : 0 < 1 + lam * y i := by have := (abs_le.1 (hl i)).1; linarith
    rw [← Real.log_mul h1.ne' h2.ne']
    exact Real.log_le_sub_one_of_pos (mul_pos h1 h2)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  rw [Finset.sum_add_distrib] at hsum
  have e : ∑ i, ((n : ℝ) * w i * (1 + lam * y i) - 1) = n * (∑ i, w i) + lam * n * (∑ i, w i * y i) - n := by
    simp only [Finset.sum_sub_distrib, mul_add, mul_one, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    have : ∀ i, (n : ℝ) * w i * (lam * y i) = lam * n * (w i * y i) := fun i => by ring
    simp_rw [this, ← Finset.mul_sum]
  rw [e, hs] at hsum
  have h3 : lam * n * (∑ i, w i * y i) ≤ |lam| * n * δ := by
    calc lam * n * (∑ i, w i * y i) ≤ |lam * n * (∑ i, w i * y i)| := le_abs_self _
      _ = |lam| * n * |∑ i, w i * y i| := by
        rw [abs_mul, abs_mul, abs_of_pos hn']
      _ ≤ |lam| * n * δ := by
        apply mul_le_mul_of_nonneg_left hδ; positivity
  linarith

lemma lower_eq {n : ℕ} (hn : 0 < n) (ρ : ℝ) (z : Fin n → ℝ) :
    EmpiricalDRO.Coverage.robustLower EmpiricalDRO.Coverage.burg ρ z =
      sInf ((fun p : Fin n → ℝ => ∑ i, p i * z i) '' RBall n ρ) := by
  unfold EmpiricalDRO.Coverage.robustLower
  rw [ball_eq n hn ρ]

lemma upper_eq {n : ℕ} (hn : 0 < n) (ρ : ℝ) (z : Fin n → ℝ) :
    GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg ρ z =
      sSup ((fun p : Fin n → ℝ => ∑ i, p i * z i) '' RBall n ρ) := by
  unfold GenEmpLik.Expansion.robustMean
  rw [ball_eq n hn ρ]

lemma det_up {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (μ q m S v Y : ℝ)
    (hm : ∑ i, (z i - μ) = n * m) (hS : ∑ i, (z i - μ) ^ 2 = n * S) (hvd : v = S - m ^ 2)
    (hv : 0 < v) (hY : ∀ i, |z i - μ| ≤ Y)
    (hM2 : |m| * (|m| + Y) / v ≤ 1 / 2)
    (hq : n * m ^ 2 / v * (1 + 4 * (|m| * (|m| + Y) / v)) ≤ q) :
    EmpiricalDRO.Coverage.robustLower EmpiricalDRO.Coverage.burg (q / 2) z ≤ μ ∧
      μ ≤ GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg (q / 2) z := by
  rw [lower_eq hn, upper_eq hn]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨w, hw, hwy⟩ := up_mem hn (fun i => z i - μ) q (|m| * (|m| + Y) / v) m S v hm hS hvd hv
    (fun i => by
      show |m / v * (m - (z i - μ))| ≤ _
      rw [abs_mul, abs_div, abs_of_pos hv, div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hv.le
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg m)
      calc |m - (z i - μ)| ≤ |m| + |z i - μ| := abs_sub _ _
        _ ≤ |m| + Y := by linarith [hY i])
    hM2 hq
  apply mem_of_exact z μ w hw
  have : ∑ i, w i * (z i - μ) = ∑ i, w i * z i - μ := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw.2.1, one_mul]
  linarith

lemma det_down {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (μ q m S Y : ℝ) (hq : 0 ≤ q)
    (hm : ∑ i, (z i - μ) = n * m) (hS : ∑ i, (z i - μ) ^ 2 = n * S)
    (hSpos : 0 < S) (hY : ∀ i, |z i - μ| ≤ Y)
    (hB : |m| * Y / S ≤ 1 / 2)
    (hlo : EmpiricalDRO.Coverage.robustLower EmpiricalDRO.Coverage.burg (q / 2) z ≤ μ)
    (hhi : μ ≤ GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg (q / 2) z) :
    n * m ^ 2 / S * (1 - 4 * (|m| * Y / S)) ≤ q := by
  rw [lower_eq hn] at hlo
  rw [upper_eq hn] at hhi
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set B := |m| * Y / S with hBdef
  set lam := m / S with hlam
  set y : Fin n → ℝ := fun i => z i - μ with hy
  have hl : ∀ i, |lam * y i| ≤ B := by
    intro i
    rw [abs_mul, hlam, abs_div, abs_of_pos hSpos, hBdef, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hSpos.le
    exact mul_le_mul_of_nonneg_left (hY i) (abs_nonneg m)
  have hl2 : ∀ i, |lam * y i| ≤ 1 / 2 := fun i => (hl i).trans hB
  have hlogle : ∑ i, Real.log (1 + lam * y i) ≤ q / 2 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hd : 0 < ε / (|lam| * n + 1) := by positivity
    obtain ⟨w, hw, hwd⟩ := approx_of_mem hn (by linarith : 0 ≤ q / 2) z μ hlo hhi _ hd
    have hwy : |∑ i, w i * y i| ≤ ε / (|lam| * n + 1) := by
      have : ∑ i, w i * y i = ∑ i, w i * z i - μ := by
        simp only [hy, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw.2.1, one_mul]
      rw [this]; exact hwd.le
    have := low_bound hn y (q / 2) lam w hw hl2 _ hwy
    have h5 : |lam| * n * (ε / (|lam| * n + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg lam]
    linarith
  have hexp : ∀ i, lam * y i - (lam * y i) ^ 2 / 2 - 2 * B * (lam * y i) ^ 2 ≤ Real.log (1 + lam * y i) := by
    intro i
    have h1 := log_cubic (lam * y i) (hl2 i)
    have h2 := (abs_le.1 h1).1
    have h3 : |lam * y i| ^ 3 ≤ B * (lam * y i) ^ 2 := by
      have : |lam * y i| ^ 3 = |lam * y i| * (lam * y i) ^ 2 := by
        rw [pow_succ, sq_abs]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (hl i) (sq_nonneg _)
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hexp i)
  have e2 : ∑ i, (lam * y i) ^ 2 = lam ^ 2 * (n * S) := by
    have : ∀ i, (lam * y i) ^ 2 = lam ^ 2 * (z i - μ) ^ 2 := fun i => by simp only [hy]; ring
    simp_rw [this]; rw [← Finset.mul_sum, hS]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum,
    ← Finset.mul_sum, hm, e2] at hsum
  have e4 : lam ^ 2 * (n * S) = n * m ^ 2 / S := by rw [hlam]; field_simp
  have e5 : lam * (n * m) = n * m ^ 2 / S := by rw [hlam]; ring
  rw [e4, e5] at hsum
  have : n * m ^ 2 / S * (1 - 4 * B) = 2 * (n * m ^ 2 / S - n * m ^ 2 / S / 2 - 2 * B * (n * m ^ 2 / S)) := by ring
  rw [this]
  linarith

lemma bridge_up {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (μ q σ ε K m S Y : ℝ)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (hσ : 0 < σ)
    (hm : ∑ i, (z i - μ) = n * m) (hS : ∑ i, (z i - μ) ^ 2 = n * S)
    (hY : ∀ i, |z i - μ| ≤ Y)
    (G1 : |√n * m| ≤ σ * K)
    (G2 : |σ ^ 2 / (S - m ^ 2) - 1| ≤ ε)
    (G5 : (|m| + Y) / √n / (S - m ^ 2) * (σ * K) ≤ ε / 4)
    (hU : (√n * m / σ) ^ 2 ≤ q / (1 + ε) ^ 2) :
    EmpiricalDRO.Coverage.robustLower EmpiricalDRO.Coverage.burg (q / 2) z ≤ μ ∧
      μ ≤ GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg (q / 2) z := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
  have hsn2 : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn'.le
  set v := S - m ^ 2 with hvdef
  have hr := abs_le.1 G2
  have hv : 0 < v := by
    by_contra hcon
    push_neg at hcon
    have : σ ^ 2 / v ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by positivity) hcon
    linarith [hr.1]
  have hr1 : σ ^ 2 / v ≤ 1 + ε := by linarith [hr.2]
  set M := |m| * (|m| + Y) / v with hMdef
  have hYnn : 0 ≤ Y := (abs_nonneg _).trans (hY ⟨0, hn⟩)
  have hMeq : M = |√n * m| * ((|m| + Y) / √n / v) := by
    rw [hMdef, abs_mul, abs_of_pos hsn]
    field_simp
  have hMle : M ≤ ε / 4 := by
    rw [hMeq]
    have hnn : 0 ≤ (|m| + Y) / √n / v := by positivity
    calc |√n * m| * ((|m| + Y) / √n / v) ≤ σ * K * ((|m| + Y) / √n / v) :=
          mul_le_mul_of_nonneg_right G1 hnn
      _ = (|m| + Y) / √n / v * (σ * K) := by ring
      _ ≤ ε / 4 := G5
  have hU0 : 0 ≤ (√n * m / σ) ^ 2 := sq_nonneg _
  have hUe : (√n * m / σ) ^ 2 = n * m ^ 2 / σ ^ 2 := by
    rw [div_pow, mul_pow, hsn2]
  have hnm : n * m ^ 2 / v = (√n * m / σ) ^ 2 * (σ ^ 2 / v) := by
    rw [hUe]; field_simp
  refine det_up hn z μ q m S v Y hm hS hvdef hv hY (hMle.trans (by linarith)) ?_
  have h1 : n * m ^ 2 / v ≤ (√n * m / σ) ^ 2 * (1 + ε) := by
    rw [hnm]; exact mul_le_mul_of_nonneg_left hr1 hU0
  have h2 : 1 + 4 * M ≤ 1 + ε := by linarith
  have h3 : 0 ≤ n * m ^ 2 / v := by positivity
  calc n * m ^ 2 / v * (1 + 4 * M) ≤ ((√n * m / σ) ^ 2 * (1 + ε)) * (1 + ε) :=
        mul_le_mul h1 h2 (by have : 0 ≤ M := by positivity
                             linarith) (by positivity)
    _ = (√n * m / σ) ^ 2 * (1 + ε) ^ 2 := by ring
    _ ≤ q / (1 + ε) ^ 2 * (1 + ε) ^ 2 := mul_le_mul_of_nonneg_right hU (by positivity)
    _ = q := by field_simp

lemma bridge_down {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (μ q σ ε K m S Y : ℝ)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (hσ : 0 < σ) (hq : 0 ≤ q)
    (hm : ∑ i, (z i - μ) = n * m) (hS : ∑ i, (z i - μ) ^ 2 = n * S)
    (hY : ∀ i, |z i - μ| ≤ Y)
    (G1 : |√n * m| ≤ σ * K)
    (G3 : |σ ^ 2 / S - 1| ≤ ε)
    (G4 : Y / √n / S * (σ * K) ≤ ε / 4)
    (hlo : EmpiricalDRO.Coverage.robustLower EmpiricalDRO.Coverage.burg (q / 2) z ≤ μ)
    (hhi : μ ≤ GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg (q / 2) z) :
    (√n * m / σ) ^ 2 ≤ q / (1 - ε) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
  have hsn2 : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn'.le
  have hr := abs_le.1 G3
  have hSpos : 0 < S := by
    by_contra hcon
    push_neg at hcon
    have : σ ^ 2 / S ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by positivity) hcon
    linarith [hr.1]
  have hr1 : 1 - ε ≤ σ ^ 2 / S := by linarith [hr.1]
  have hYnn : 0 ≤ Y := (abs_nonneg _).trans (hY ⟨0, hn⟩)
  set B := |m| * Y / S with hBdef
  have hBeq : B = |√n * m| * (Y / √n / S) := by
    rw [hBdef, abs_mul, abs_of_pos hsn]
    field_simp
  have hBle : B ≤ ε / 4 := by
    rw [hBeq]
    have hnn : 0 ≤ Y / √n / S := by positivity
    calc |√n * m| * (Y / √n / S) ≤ σ * K * (Y / √n / S) := mul_le_mul_of_nonneg_right G1 hnn
      _ = Y / √n / S * (σ * K) := by ring
      _ ≤ ε / 4 := G4
  have hB0 : 0 ≤ B := by positivity
  have hdown := det_down hn z μ q m S Y hq hm hS hSpos hY (hBle.trans (by linarith)) hlo hhi
  have hU0 : 0 ≤ (√n * m / σ) ^ 2 := sq_nonneg _
  have hUe : (√n * m / σ) ^ 2 = n * m ^ 2 / σ ^ 2 := by
    rw [div_pow, mul_pow, hsn2]
  have hnm : n * m ^ 2 / S = (√n * m / σ) ^ 2 * (σ ^ 2 / S) := by
    rw [hUe]; field_simp
  have h1 : (√n * m / σ) ^ 2 * (1 - ε) ≤ n * m ^ 2 / S := by
    rw [hnm]; exact mul_le_mul_of_nonneg_left hr1 hU0
  have h2 : 1 - ε ≤ 1 - 4 * B := by linarith
  have h3 : (√n * m / σ) ^ 2 * (1 - ε) * (1 - ε) ≤ n * m ^ 2 / S * (1 - 4 * B) :=
    mul_le_mul h1 h2 (by linarith) (by positivity)
  have h4 : (√n * m / σ) ^ 2 * (1 - ε) ^ 2 ≤ q := by nlinarith
  rw [le_div_iff₀ (by nlinarith)]
  linarith



/-- running maximum of |w k| over k < n -/
noncomputable def sup0 (w : ℕ → ℝ) (n : ℕ) : ℝ := (((Finset.range n).sup (fun k => ‖w k‖₊) : NNReal) : ℝ)

lemma le_sup0 (w : ℕ → ℝ) {n k : ℕ} (hk : k < n) : |w k| ≤ sup0 w n := by
  have := Finset.le_sup (f := fun k => ‖w k‖₊) (Finset.mem_range.2 hk)
  have h2 : ((‖w k‖₊ : NNReal) : ℝ) ≤ sup0 w n := by
    unfold sup0; exact_mod_cast this
  simpa using h2

lemma sup0_le (w : ℕ → ℝ) {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ k < n, |w k| ≤ c) : sup0 w n ≤ c := by
  unfold sup0
  have : (Finset.range n).sup (fun k => ‖w k‖₊) ≤ c.toNNReal := by
    refine Finset.sup_le fun k hk => ?_
    have := h k (Finset.mem_range.1 hk)
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hc]
    simpa using this
  have h2 := (NNReal.coe_le_coe.2 this)
  rwa [Real.coe_toNNReal _ hc] at h2

lemma sup0_nonneg (w : ℕ → ℝ) (n : ℕ) : 0 ≤ sup0 w n := NNReal.coe_nonneg _

lemma sq_div_tendsto (w : ℕ → ℝ) (σ2 : ℝ)
    (h : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, w k ^ 2) / n) atTop (𝓝 σ2)) :
    Tendsto (fun n : ℕ => w n ^ 2 / n) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), w k ^ 2) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 σ2) :=
    h.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    simp only [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have h3 := (h2.mul h1).sub h
  simp only [one_mul, sub_self] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_range_succ]
  push_cast
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

lemma maxdiv_tendsto (w : ℕ → ℝ) (σ2 : ℝ)
    (h : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, w k ^ 2) / n) atTop (𝓝 σ2)) :
    Tendsto (fun n : ℕ => sup0 w n / √(n : ℝ)) atTop (𝓝 0) := by
  have hc := sq_div_tendsto w σ2 h
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hc) ((ε / 2) ^ 2) (by positivity)
  set N' := max N 1 with hN'
  have hbound : ∀ k ≥ N', |w k| ≤ ε / 2 * √(k : ℝ) := by
    intro k hk
    have hk1 : 0 < k := lt_of_lt_of_le (by omega) hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk1
    have := hN k (le_trans (le_max_left _ _) hk)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    rw [div_lt_iff₀ hk'] at this
    have h5 : |w k| ^ 2 ≤ (ε / 2 * √(k : ℝ)) ^ 2 := by
      rw [sq_abs, mul_pow, Real.sq_sqrt hk'.le]; linarith
    by_contra hcon
    push_neg at hcon
    have hpos : 0 ≤ ε / 2 * √(k : ℝ) := by positivity
    nlinarith [abs_nonneg (w k)]
  set C := sup0 w N' with hC
  have hC0 : 0 ≤ C := sup0_nonneg _ _
  have hlim : Tendsto (fun n : ℕ => C / √(n : ℝ)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact this.const_div_atTop C
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.1 hlim) (ε / 2) hε2
  refine ⟨max N' N2, fun n hn => ?_⟩
  have hnN' : N' ≤ n := le_trans (le_max_left _ _) hn
  have hnN2 : N2 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : 0 < n := lt_of_lt_of_le (by omega) hnN'
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn0)
  have hsup : sup0 w n ≤ C + ε / 2 * √(n : ℝ) := by
    apply sup0_le w (by positivity)
    intro k hk
    by_cases hkN : k < N'
    · have := le_sup0 w hkN
      have : 0 ≤ ε / 2 * √(n : ℝ) := by positivity
      linarith [le_sup0 w hkN]
    · push_neg at hkN
      have h1 := hbound k hkN
      have h2 : √(k : ℝ) ≤ √(n : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hk.le)
      nlinarith
  have h3 := hN2 n hnN2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h3
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (sup0_nonneg _ _) hsn.le)]
  rw [div_lt_iff₀ hsn] at h3 ⊢
  nlinarith

section Prob
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma ae_limits (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hL2 : MemLp (X 0) 2 P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, (X k ω - P[X 0])) / (n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, (X k ω - P[X 0]) ^ 2) / (n : ℝ)) atTop
        (𝓝 (variance (X 0) P)) := by
  set c := P[X 0] with hc
  have hint : Integrable (X 0) P := hL2.integrable (by norm_num)
  have h1 := strong_law_ae (fun k ω => X k ω - c) (hint.sub (integrable_const c))
    (fun i j hij => (hindep.indepFun hij).comp (measurable_id.sub_const c) (measurable_id.sub_const c))
    (fun i => (hident i).comp (measurable_id.sub_const c))
  have h2 := strong_law_ae (fun k ω => (X k ω - c) ^ 2) (hL2.sub (memLp_const c)).integrable_sq
    (fun i j hij => (hindep.indepFun hij).comp ((measurable_id.sub_const c).pow_const 2)
      ((measurable_id.sub_const c).pow_const 2))
    (fun i => (hident i).comp ((measurable_id.sub_const c).pow_const 2))
  filter_upwards [h1, h2] with ω hω1 hω2
  refine ⟨?_, ?_⟩
  · have e : P[fun ω => X 0 ω - c] = 0 := by
      rw [integral_sub hint (integrable_const c)]; simp [hc]
    rw [e] at hω1
    simpa [smul_eq_mul, div_eq_inv_mul] using hω1
  · have e : P[fun ω => (X 0 ω - c) ^ 2] = variance (X 0) P := by
      rw [variance_eq_integral hL2.aemeasurable]
    rw [e] at hω2
    simpa [smul_eq_mul, div_eq_inv_mul] using hω2

noncomputable def mm (X : ℕ → Ω → ℝ) (c : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ k ∈ Finset.range n, (X k ω - c)) / (n : ℝ)
noncomputable def SS (X : ℕ → Ω → ℝ) (c : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ k ∈ Finset.range n, (X k ω - c) ^ 2) / (n : ℝ)
noncomputable def YY (X : ℕ → Ω → ℝ) (c : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  sup0 (fun k => X k ω - c) n

lemma sup0_succ (w : ℕ → ℝ) (n : ℕ) : sup0 w (n + 1) = max (sup0 w n) |w n| := by
  unfold sup0
  rw [Finset.range_add_one, Finset.sup_insert]
  rw [sup_comm]
  have h1 : ((‖w n‖₊ : NNReal) : ℝ) = |w n| := by simp
  rw [← h1]
  exact NNReal.coe_max _ _

lemma measurable_YY (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (c : ℝ) (n : ℕ) :
    Measurable (YY X c n) := by
  induction n with
  | zero =>
    have : YY X c 0 = fun _ => 0 := by funext ω; simp [YY, sup0]
    rw [this]; exact measurable_const
  | succ n ih =>
    have : YY X c (n + 1) = fun ω => max (YY X c n ω) |X n ω - c| := by
      funext ω; unfold YY; rw [sup0_succ]
    rw [this]
    exact ih.max ((hmeas n).sub_const c).abs

lemma measurable_mm (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (c : ℝ) (n : ℕ) :
    Measurable (mm X c n) := by
  unfold mm
  exact (Finset.measurable_sum _ fun k _ => (hmeas k).sub_const c).div_const _

lemma measurable_SS (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (c : ℝ) (n : ℕ) :
    Measurable (SS X c n) := by
  unfold SS
  exact (Finset.measurable_sum _ fun k _ => ((hmeas k).sub_const c).pow_const 2).div_const _

lemma meas4 (P : Measure Ω) (s t u v : Set Ω) :
    P (s ∪ t ∪ u ∪ v) ≤ P s + P t + P u + P v := by
  calc P (s ∪ t ∪ u ∪ v) ≤ P (s ∪ t ∪ u) + P v := measure_union_le _ _
    _ ≤ (P (s ∪ t) + P u) + P v := by gcongr; exact measure_union_le _ _
    _ ≤ ((P s + P t) + P u) + P v := by gcongr; exact measure_union_le _ _

lemma tim_zero (f : ℕ → Ω → ℝ) (hf : ∀ n, Measurable (f n))
    (h : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 0)) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => P {ω | δ ≤ |f n ω|}) atTop (𝓝 0) := by
  have := tendstoInMeasure_of_tendsto_ae (g := fun _ => (0 : ℝ)) (fun n => (hf n).aestronglyMeasurable) h
  rw [tendstoInMeasure_iff_dist] at this
  simpa [Real.dist_eq] using this δ hδ

lemma bad_tendsto (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hL2 : MemLp (X 0) 2 P)
    (σ : ℝ) (hσ : 0 < σ) (hσ2 : σ ^ 2 = variance (X 0) P) (ε K : ℝ) (hε : 0 < ε) (hK : 0 < K) :
    Tendsto (fun n : ℕ => P {ω | ¬ (
      |σ ^ 2 / (SS X P[X 0] n ω - mm X P[X 0] n ω ^ 2) - 1| ≤ ε ∧
      |σ ^ 2 / SS X P[X 0] n ω - 1| ≤ ε ∧
      YY X P[X 0] n ω / √(n : ℝ) / SS X P[X 0] n ω * (σ * K) ≤ ε / 4 ∧
      (|mm X P[X 0] n ω| + YY X P[X 0] n ω) / √(n : ℝ) / (SS X P[X 0] n ω - mm X P[X 0] n ω ^ 2)
        * (σ * K) ≤ ε / 4)}) atTop (𝓝 0) := by
  set c := P[X 0] with hc
  have hae := ae_limits X hmeas hindep hident hL2
  have hσ2' : σ ^ 2 ≠ 0 := by positivity
  have hae2 : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => YY X c n ω / √(n : ℝ)) atTop (𝓝 0) := by
    filter_upwards [hae] with ω hω
    exact maxdiv_tendsto (fun k => X k ω - c) _ hω.2
  have hinv : Tendsto (fun n : ℕ => 1 / √(n : ℝ)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact this.const_div_atTop 1
  -- limits
  have hVar : variance (X 0) P ≠ 0 := by rw [← hσ2]; exact hσ2'
  have hVar2 : variance (X 0) P - 0 ^ 2 ≠ 0 := by simpa using hVar
  have L2 : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => σ ^ 2 / (SS X c n ω - mm X c n ω ^ 2) - 1) atTop (𝓝 0) := by
    filter_upwards [hae] with ω hω
    have hm' : Tendsto (fun n => mm X c n ω) atTop (𝓝 0) := hω.1
    have hs' : Tendsto (fun n => SS X c n ω) atTop (𝓝 (variance (X 0) P)) := hω.2
    have h1 := ((tendsto_const_nhds (x := σ ^ 2)).div (hs'.sub (hm'.pow 2)) hVar2).sub_const 1
    have e : σ ^ 2 / (variance (X 0) P - 0 ^ 2) - 1 = 0 := by rw [← hσ2]; field_simp; ring
    rwa [e] at h1
  have L3 : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => σ ^ 2 / SS X c n ω - 1) atTop (𝓝 0) := by
    filter_upwards [hae] with ω hω
    have hs' : Tendsto (fun n => SS X c n ω) atTop (𝓝 (variance (X 0) P)) := hω.2
    have h1 := ((tendsto_const_nhds (x := σ ^ 2)).div hs' hVar).sub_const 1
    have e : σ ^ 2 / variance (X 0) P - 1 = 0 := by rw [← hσ2]; field_simp; ring
    rwa [e] at h1
  have L4 : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => YY X c n ω / √(n : ℝ) / SS X c n ω * (σ * K)) atTop (𝓝 0) := by
    filter_upwards [hae, hae2] with ω hω hω2
    have hs' : Tendsto (fun n => SS X c n ω) atTop (𝓝 (variance (X 0) P)) := hω.2
    have h1 := (hω2.div hs' hVar).mul_const (σ * K)
    simpa using h1
  have L5 : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      (|mm X c n ω| + YY X c n ω) / √(n : ℝ) / (SS X c n ω - mm X c n ω ^ 2) * (σ * K)) atTop (𝓝 0) := by
    filter_upwards [hae, hae2] with ω hω hω2
    have hm' : Tendsto (fun n => mm X c n ω) atTop (𝓝 0) := hω.1
    have hs' : Tendsto (fun n => SS X c n ω) atTop (𝓝 (variance (X 0) P)) := hω.2
    have hnum : Tendsto (fun n : ℕ => (|mm X c n ω| + YY X c n ω) / √(n : ℝ)) atTop (𝓝 0) := by
      have h1 := (hm'.abs.mul hinv).add hω2
      simp only [abs_zero, zero_mul, add_zero] at h1
      refine h1.congr fun n => ?_
      ring
    have h1 := (hnum.div (hs'.sub (hm'.pow 2)) hVar2).mul_const (σ * K)
    simpa using h1
  -- measurability
  have mm_m := measurable_mm X hmeas c
  have SS_m := measurable_SS X hmeas c
  have YY_m := measurable_YY X hmeas c
  have T2 := tim_zero (P := P) (fun n ω => σ ^ 2 / (SS X c n ω - mm X c n ω ^ 2) - 1)
    (fun n => ((measurable_const.div ((SS_m n).sub ((mm_m n).pow_const 2))).sub_const 1)) L2 ε hε
  have T3 := tim_zero (P := P) (fun n ω => σ ^ 2 / SS X c n ω - 1)
    (fun n => ((measurable_const.div (SS_m n)).sub_const 1)) L3 ε hε
  have δ4 : 0 < ε / 4 := by positivity
  have T4 := tim_zero (P := P) (fun n ω => YY X c n ω / √(n : ℝ) / SS X c n ω * (σ * K))
    (fun n => ((((YY_m n).div_const _).div (SS_m n)).mul_const _)) L4 (ε / 4) δ4
  have T5 := tim_zero (P := P) (fun n ω => (|mm X c n ω| + YY X c n ω) / √(n : ℝ) /
      (SS X c n ω - mm X c n ω ^ 2) * (σ * K))
    (fun n => ((((((mm_m n).abs).add (YY_m n)).div_const _).div
      ((SS_m n).sub ((mm_m n).pow_const 2))).mul_const _)) L5 (ε / 4) δ4
  have hsum := ((T2.add T3).add T4).add T5
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n => bot_le) (fun n => ?_)
  refine (measure_mono ?_).trans (meas4 P _ _ _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, not_and_or, not_le] at hω
  simp only [Set.mem_union, Set.mem_setOf_eq]
  rcases hω with h | h | h | h
  · left; left; left; exact le_of_lt h
  · left; left; right; exact le_of_lt h
  · left; right
    exact le_trans (le_of_lt h) (le_abs_self _)
  · right
    exact le_trans (le_of_lt h) (le_abs_self _)

noncomputable def ZZ (X : ℕ → Ω → ℝ) (c σ : ℝ) (n : ℕ) (ω : Ω) : ℝ := √(n : ℝ) * mm X c n ω / σ

lemma clt_Z (X : ℕ → Ω → ℝ) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hL2 : MemLp (X 0) 2 P)
    (σ : ℝ) (hσ : 0 < σ) (hσ2 : σ ^ 2 = variance (X 0) P) :
    TendstoInDistribution (fun n ω => ZZ X P[X 0] σ n ω) atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 1) := by
  have hY : HasLaw (fun t : ℝ => σ * t) (gaussianReal 0 (variance (X 0) P).toNNReal) (gaussianReal 0 1) := by
    refine ⟨by fun_prop, ?_⟩
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [← hσ2]
      positivity
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (X := X) (P := P) hY hL2 hindep hident
  have h2 := hclt.continuous_comp (g := fun t : ℝ => t / σ) (continuous_id.div_const σ)
  have e1 : (fun t : ℝ => σ * t) ∘ id = fun t => σ * t := rfl
  have e2 : ((fun t : ℝ => t / σ) ∘ fun t : ℝ => σ * t) = (id : ℝ → ℝ) := by
    funext t; simp [hσ.ne']
  rw [e2] at h2
  convert h2 using 3
  rename_i n ω
  simp only [Function.comp, ZZ, mm]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (n : ℝ) ≠ 0 := by positivity
    have hsn : √(n : ℝ) ≠ 0 := by positivity
    have hsq : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]

lemma port_closed {Y : ℕ → Ω → ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : TendstoInDistribution Y atTop (id : ℝ → ℝ) (fun _ => P) μ) {F : Set ℝ} (hF : IsClosed F) :
    limsup (fun n => P (Y n ⁻¹' F)) atTop ≤ μ F := by
  have := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto hF
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at this
  have e : ∀ n, P.map (Y n) F = P (Y n ⁻¹' F) := fun n =>
    Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hF.measurableSet
  simpa [e] using this

lemma port_open {Y : ℕ → Ω → ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : TendstoInDistribution Y atTop (id : ℝ → ℝ) (fun _ => P) μ) {G : Set ℝ} (hG : IsOpen G) :
    μ G ≤ liminf (fun n => P (Y n ⁻¹' G)) atTop := by
  have := ProbabilityMeasure.le_liminf_measure_open_of_tendsto h.tendsto hG
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at this
  have e : ∀ n, P.map (Y n) G = P (Y n ⁻¹' G) := fun n =>
    Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hG.measurableSet
  simpa [e] using this

end Prob

section Gauss

noncomputable abbrev G : Measure ℝ := gaussianReal 0 1

lemma G_singleton (a : ℝ) : G {a} = 0 := by
  have h := gaussianReal_absolutelyContinuous (0 : ℝ) (one_ne_zero : (1 : NNReal) ≠ 0)
  exact h (by simp)

lemma G_sq_lt_eq {q : ℝ} (hq : 0 < q) : G {t : ℝ | t ^ 2 < q} = G {t : ℝ | t ^ 2 ≤ q} := by
  refine le_antisymm (measure_mono ?_) ?_
  · intro t ht
    exact le_of_lt (by simpa using ht)
  have hsub : {t : ℝ | t ^ 2 ≤ q} ⊆ {t : ℝ | t ^ 2 < q} ∪ ({√q} ∪ {-√q}) := by
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    rcases lt_or_eq_of_le ht with h | h
    · left; exact h
    · right
      have h2 : t ^ 2 = √q ^ 2 := by rw [h, Real.sq_sqrt hq.le]
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h3 | h3
      · left; exact h3
      · right; exact h3
  calc G {t : ℝ | t ^ 2 ≤ q} ≤ G ({t : ℝ | t ^ 2 < q} ∪ ({√q} ∪ {-√q})) := measure_mono hsub
    _ ≤ G {t : ℝ | t ^ 2 < q} + G ({√q} ∪ {-√q}) := measure_union_le _ _
    _ ≤ G {t : ℝ | t ^ 2 < q} + (G {√q} + G {-√q}) := by gcongr; exact measure_union_le _ _
    _ = G {t : ℝ | t ^ 2 < q} := by rw [G_singleton, G_singleton]; simp

lemma eps_tendsto : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 3)) atTop (𝓝 0) := by
  have : Tendsto (fun j : ℕ => (j : ℝ) + 3) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact this.const_div_atTop 1

lemma eps_pos (j : ℕ) : 0 < 1 / ((j : ℝ) + 3) := by positivity
lemma eps_le (j : ℕ) : 1 / ((j : ℝ) + 3) ≤ 1 / 2 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith
lemma eps_anti : Antitone (fun j : ℕ => 1 / ((j : ℝ) + 3)) := by
  intro a b hab
  apply one_div_le_one_div_of_le (by positivity)
  have : (a : ℝ) ≤ b := by exact_mod_cast hab
  linarith

lemma g_upper {q : ℝ} (hq : 0 < q) :
    Tendsto (fun j : ℕ => G {t : ℝ | t ^ 2 ≤ q / (1 - 1 / ((j : ℝ) + 3)) ^ 2}) atTop
      (𝓝 (G {t : ℝ | t ^ 2 ≤ q})) := by
  set c : ℕ → ℝ := fun j => q / (1 - 1 / ((j : ℝ) + 3)) ^ 2 with hc
  have hcl : Tendsto c atTop (𝓝 q) := by
    have h1 : Tendsto (fun j : ℕ => 1 - 1 / ((j : ℝ) + 3)) atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub eps_tendsto
    have h2 : Tendsto (fun j : ℕ => q / (1 - 1 / ((j : ℝ) + 3)) ^ 2) atTop (𝓝 (q / (1 - 0) ^ 2)) :=
      (tendsto_const_nhds (x := q)).div (h1.pow 2) (by norm_num)
    have e : q / (1 - (0:ℝ)) ^ 2 = q := by norm_num
    rwa [e] at h2
  have hcge : ∀ j, q ≤ c j := by
    intro j
    have h0 := eps_pos j
    have h1 := eps_le j
    have : 0 < (1 - 1 / ((j : ℝ) + 3)) ^ 2 := by nlinarith
    rw [hc]; dsimp only
    rw [le_div_iff₀ this]
    have h3 : (1 - 1 / ((j : ℝ) + 3)) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h3 hq.le]
  have hanti : Antitone c := by
    intro a b hab
    have hε := eps_anti hab
    have h0 := eps_pos b
    have h1 := eps_le a
    have h2 := eps_pos a
    have h3 := eps_le b
    have : 0 < (1 - 1 / ((a : ℝ) + 3)) ^ 2 := by nlinarith
    simp only [hc]
    apply div_le_div_of_nonneg_left hq.le this
    simp only at hε
    nlinarith
  have hsets : Antitone (fun j => {t : ℝ | t ^ 2 ≤ c j}) := fun a b hab t ht => le_trans ht (hanti hab)
  have key := tendsto_measure_iInter_atTop (μ := G) (s := fun j => {t : ℝ | t ^ 2 ≤ c j})
    (fun j => (measurableSet_le (by fun_prop) measurable_const).nullMeasurableSet) hsets
    ⟨0, measure_ne_top _ _⟩
  have hint : (⋂ j, {t : ℝ | t ^ 2 ≤ c j}) = {t : ℝ | t ^ 2 ≤ q} := by
    ext t
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h
      exact ge_of_tendsto' hcl h
    · intro h j; exact h.trans (hcge j)
  rw [hint] at key
  exact key

lemma g_lower {q : ℝ} (hq : 0 < q) :
    Tendsto (fun j : ℕ => G {t : ℝ | t ^ 2 < q / (1 + 1 / ((j : ℝ) + 3)) ^ 2}) atTop
      (𝓝 (G {t : ℝ | t ^ 2 ≤ q})) := by
  set c : ℕ → ℝ := fun j => q / (1 + 1 / ((j : ℝ) + 3)) ^ 2 with hc
  have hcl : Tendsto c atTop (𝓝 q) := by
    have h1 : Tendsto (fun j : ℕ => 1 + 1 / ((j : ℝ) + 3)) atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add eps_tendsto
    have h2 : Tendsto (fun j : ℕ => q / (1 + 1 / ((j : ℝ) + 3)) ^ 2) atTop (𝓝 (q / (1 + 0) ^ 2)) :=
      (tendsto_const_nhds (x := q)).div (h1.pow 2) (by norm_num)
    have e : q / (1 + (0:ℝ)) ^ 2 = q := by norm_num
    rwa [e] at h2
  have hcle : ∀ j, c j ≤ q := by
    intro j
    have h0 := eps_pos j
    have : 1 ≤ (1 + 1 / ((j : ℝ) + 3)) ^ 2 := by nlinarith
    rw [hc]; dsimp only
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hmono : Monotone c := by
    intro a b hab
    have hε := eps_anti hab
    have h0 := eps_pos b
    simp only [hc]
    apply div_le_div_of_nonneg_left hq.le (by positivity)
    have := eps_pos a
    nlinarith
  have hsets : Monotone (fun j => {t : ℝ | t ^ 2 < c j}) := fun a b hab t ht => lt_of_lt_of_le ht (hmono hab)
  have key := tendsto_measure_iUnion_atTop (μ := G) (s := fun j => {t : ℝ | t ^ 2 < c j}) hsets
  have hint : (⋃ j, {t : ℝ | t ^ 2 < c j}) = {t : ℝ | t ^ 2 < q} := by
    ext t
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨j, hj⟩; exact lt_of_lt_of_le hj (hcle j)
    · intro h
      have := (hcl.eventually (lt_mem_nhds h)).exists
      obtain ⟨j, hj⟩ := this
      exact ⟨j, hj⟩
  rw [hint, G_sq_lt_eq hq] at key
  exact key

lemma g_tail (q : ℝ) :
    Tendsto (fun j : ℕ => G {t : ℝ | q + 1 + j ≤ |t|}) atTop (𝓝 0) := by
  have hsets : Antitone (fun j : ℕ => {t : ℝ | q + 1 + j ≤ |t|}) := by
    intro a b hab t ht
    simp only [Set.mem_setOf_eq] at *
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have key := tendsto_measure_iInter_atTop (μ := G) (s := fun j : ℕ => {t : ℝ | q + 1 + j ≤ |t|})
    (fun j => (measurableSet_le measurable_const (by fun_prop)).nullMeasurableSet) hsets
    ⟨0, measure_ne_top _ _⟩
  have hint : (⋂ j : ℕ, {t : ℝ | q + 1 + j ≤ |t|}) = ∅ := by
    ext t
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall, not_le]
    obtain ⟨j, hj⟩ := exists_nat_gt (|t| - q - 1)
    exact ⟨j, by linarith⟩
  rw [hint, measure_empty] at key
  exact key

end Gauss


section Main
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

def Ev (X : ℕ → Ω → ℝ) (c q : ℝ) (n : ℕ) : Set Ω :=
  {ω | EmpiricalDRO.Coverage.robustLower EmpiricalDRO.Coverage.burg (q / 2) (fun i : Fin n => X i ω) ≤ c ∧
    c ≤ GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg (q / 2) (fun i : Fin n => X i ω)}

def BadSet (X : ℕ → Ω → ℝ) (c σ ε K : ℝ) (n : ℕ) : Set Ω := {ω | ¬ (
      |σ ^ 2 / (SS X c n ω - mm X c n ω ^ 2) - 1| ≤ ε ∧
      |σ ^ 2 / SS X c n ω - 1| ≤ ε ∧
      YY X c n ω / √(n : ℝ) / SS X c n ω * (σ * K) ≤ ε / 4 ∧
      (|mm X c n ω| + YY X c n ω) / √(n : ℝ) / (SS X c n ω - mm X c n ω ^ 2) * (σ * K) ≤ ε / 4)}

lemma sums_fin (X : ℕ → Ω → ℝ) (c : ℝ) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    ∑ i : Fin n, ((X i ω) - c) = n * mm X c n ω ∧
    ∑ i : Fin n, ((X i ω) - c) ^ 2 = n * SS X c n ω := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  constructor
  · rw [Fin.sum_univ_eq_sum_range (fun k => X k ω - c) n]
    unfold mm; field_simp
  · rw [Fin.sum_univ_eq_sum_range (fun k => (X k ω - c) ^ 2) n]
    unfold SS; field_simp

lemma abs_Z_le (X : ℕ → Ω → ℝ) (c σ K : ℝ) (hσ : 0 < σ) (n : ℕ) (ω : Ω)
    (h : |ZZ X c σ n ω| ≤ K) : |√(n : ℝ) * mm X c n ω| ≤ σ * K := by
  unfold ZZ at h
  rw [abs_div, abs_of_pos hσ, div_le_iff₀ hσ] at h
  linarith

lemma incl_up (X : ℕ → Ω → ℝ) (c q σ ε K : ℝ) (hσ : 0 < σ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    {n : ℕ} (hn : 0 < n) (ω : Ω) (hbad : ω ∉ BadSet X c σ ε K n) (hK : |ZZ X c σ n ω| ≤ K)
    (hU : ZZ X c σ n ω ^ 2 ≤ q / (1 + ε) ^ 2) : ω ∈ Ev X c q n := by
  simp only [BadSet, Set.mem_setOf_eq, not_not] at hbad
  obtain ⟨hs1, hs2⟩ := sums_fin X c hn ω
  exact bridge_up hn (fun i : Fin n => X i ω) c q σ ε K (mm X c n ω) (SS X c n ω) (YY X c n ω)
    hε0 hε hσ hs1 hs2 (fun i => le_sup0 (fun k => X k ω - c) i.isLt) (abs_Z_le X c σ K hσ n ω hK)
    hbad.1 hbad.2.2.2 hU

lemma incl_down (X : ℕ → Ω → ℝ) (c q σ ε K : ℝ) (hσ : 0 < σ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (hq : 0 ≤ q) {n : ℕ} (hn : 0 < n) (ω : Ω) (hbad : ω ∉ BadSet X c σ ε K n)
    (hK : |ZZ X c σ n ω| ≤ K) (hE : ω ∈ Ev X c q n) :
    ZZ X c σ n ω ^ 2 ≤ q / (1 - ε) ^ 2 := by
  simp only [BadSet, Set.mem_setOf_eq, not_not] at hbad
  obtain ⟨hs1, hs2⟩ := sums_fin X c hn ω
  exact bridge_down hn (fun i : Fin n => X i ω) c q σ ε K (mm X c n ω) (SS X c n ω) (YY X c n ω)
    hε0 hε hσ hq hs1 hs2 (fun i => le_sup0 (fun k => X k ω - c) i.isLt) (abs_Z_le X c σ K hσ n ω hK)
    hbad.2.1 hbad.2.2.1 hE.1 hE.2

theorem main_tendsto (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hL2 : MemLp (X 0) 2 P)
    (hvar : 0 < variance (X 0) P) (q : ℝ) (hq : 0 < q) :
    Tendsto (fun n : ℕ => P (Ev X P[X 0] q n)) atTop (𝓝 (G {t : ℝ | t ^ 2 ≤ q})) := by
  set c := P[X 0] with hc
  set σ := √(variance (X 0) P) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hvar
  have hσ2 : σ ^ 2 = variance (X 0) P := Real.sq_sqrt hvar.le
  have hZ := clt_Z X hindep hident hL2 σ hσ hσ2
  set ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 3) with hεdef
  set K : ℕ → ℝ := fun j => q + 1 + j with hKdef
  have hKpos : ∀ j, 0 < K j := fun j => by simp only [hKdef]; positivity
  have hb : ∀ j, Tendsto (fun n => P (BadSet X c σ (ε j) (K j) n)) atTop (𝓝 0) := fun j =>
    bad_tendsto X hmeas hindep hident hL2 σ hσ hσ2 (ε j) (K j) (eps_pos j) (hKpos j)
  -- upper bound
  have hup : ∀ j, limsup (fun n => P (Ev X c q n)) atTop ≤
      G {t : ℝ | t ^ 2 ≤ q / (1 - ε j) ^ 2} + G {t : ℝ | q + 1 + j ≤ |t|} := by
    intro j
    set F : Set ℝ := {t : ℝ | t ^ 2 ≤ q / (1 - ε j) ^ 2} with hF
    set T : Set ℝ := {t : ℝ | q + 1 + j ≤ |t|} with hT
    have hFc : IsClosed F := isClosed_le (by fun_prop) continuous_const
    have hTc : IsClosed T := isClosed_le continuous_const (by fun_prop)
    set x : ℕ → ENNReal := fun n => P ((fun ω => ZZ X c σ n ω) ⁻¹' (F ∪ T)) with hx
    set b : ℕ → ENNReal := fun n => P (BadSet X c σ (ε j) (K j) n) with hbdef
    have hle : (fun n => P (Ev X c q n)) ≤ᶠ[atTop] (x + b) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      show P (Ev X c q n) ≤ x n + b n
      refine (measure_mono ?_).trans (measure_union_le _ _)
      intro ω hω
      by_cases hbad : ω ∈ BadSet X c σ (ε j) (K j) n
      · exact Or.inr hbad
      · left
        by_cases hk : |ZZ X c σ n ω| ≤ K j
        · left
          exact incl_down X c q σ (ε j) (K j) hσ (eps_pos j) (eps_le j) hq.le hn ω hbad hk hω
        · right
          exact (not_le.1 hk).le
    calc limsup (fun n => P (Ev X c q n)) atTop ≤ limsup (x + b) atTop := limsup_le_limsup hle
      _ = limsup x atTop := ENNReal.limsup_add_of_right_tendsto_zero (hb j) _
      _ ≤ G (F ∪ T) := port_closed hZ (hFc.union hTc)
      _ ≤ G F + G T := measure_union_le _ _
  -- lower bound
  have hlow : ∀ j, G {t : ℝ | t ^ 2 < q / (1 + ε j) ^ 2} ≤ liminf (fun n => P (Ev X c q n)) atTop := by
    intro j
    set L : Set ℝ := {t : ℝ | t ^ 2 < q / (1 + ε j) ^ 2} with hL
    have hLo : IsOpen L := isOpen_lt (by fun_prop) continuous_const
    set l : ℕ → ENNReal := fun n => P ((fun ω => ZZ X c σ n ω) ⁻¹' L) with hl
    set u : ℕ → ENNReal := fun n => P (Ev X c q n) with hu
    set b : ℕ → ENNReal := fun n => P (BadSet X c σ (ε j) (K j) n) with hbdef
    have hle : l ≤ᶠ[atTop] (u + b) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      show l n ≤ u n + b n
      refine (measure_mono ?_).trans (measure_union_le _ _)
      intro ω hω
      by_cases hbad : ω ∈ BadSet X c σ (ε j) (K j) n
      · exact Or.inr hbad
      · left
        have hZ2 : ZZ X c σ n ω ^ 2 < q / (1 + ε j) ^ 2 := hω
        have h0 := eps_pos j
        have hq1 : q / (1 + ε j) ^ 2 ≤ q := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [mul_pos hq h0, mul_pos hq (mul_pos h0 h0)]
        have hKj : |ZZ X c σ n ω| ≤ K j := by
          by_contra hcon
          push_neg at hcon
          have h1 : K j ^ 2 < |ZZ X c σ n ω| ^ 2 := by
            have := hKpos j
            nlinarith
          rw [sq_abs] at h1
          have h2 : q ≤ K j ^ 2 := by
            simp only [hKdef]
            have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
            nlinarith
          linarith
        exact incl_up X c q σ (ε j) (K j) hσ h0 (eps_le j) hn ω hbad hKj hZ2.le
    calc G L ≤ liminf l atTop := port_open hZ hLo
      _ ≤ liminf (u + b) atTop := liminf_le_liminf hle
      _ = liminf u atTop := ENNReal.liminf_add_of_right_tendsto_zero (hb j) u
  have hA : limsup (fun n => P (Ev X c q n)) atTop ≤ G {t : ℝ | t ^ 2 ≤ q} := by
    have hlim := (g_upper hq).add (g_tail q)
    rw [add_zero] at hlim
    exact ge_of_tendsto' hlim hup
  have hB : G {t : ℝ | t ^ 2 ≤ q} ≤ liminf (fun n => P (Ev X c q n)) atTop :=
    le_of_tendsto' (g_lower hq) hlow
  exact tendsto_of_le_liminf_of_limsup_le hB hA

end Main

end EDRO

open MeasureTheory ProbabilityTheory Filter Topology EmpiricalDRO.Coverage in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] (ξ : ℕ → Ω → Ξ) (hξ : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P) (hident : ∀ i, IdentDistrib (ξ i) (ξ 0) P P)
    {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → Ξ → ℝ) (x : EuclideanSpace ℝ (Fin m))
    (hhx : Measurable (h x)) (hL2 : MemLp (fun ω => h x (ξ 0 ω)) 2 P)
    (hvar : 0 < variance (fun ω => h x (ξ 0 ω)) P)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (q : ℝ)
    (hq : gaussianReal 0 1 {y : ℝ | y ^ 2 ≤ q} = ENNReal.ofReal (1 - α)) :
    Tendsto (fun n : ℕ => P {ω |
      robustLower burg (q / 2) (fun i : Fin n => h x (ξ i ω)) ≤ ∫ ω', h x (ξ 0 ω') ∂P ∧
        ∫ ω', h x (ξ 0 ω') ∂P ≤
          GenEmpLik.Expansion.robustMean burg (q / 2) (fun i : Fin n => h x (ξ i ω))})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hq0 : 0 < q := by
    by_contra hcon
    push_neg at hcon
    have h0 : EDRO.G {y : ℝ | y ^ 2 ≤ q} = 0 := by
      refine measure_mono_null (t := {0}) ?_ (EDRO.G_singleton 0)
      intro y hy
      have : y ^ 2 ≤ 0 := le_trans hy hcon
      have : y = 0 := by nlinarith [sq_nonneg y]
      simpa using this
    have h1 : EDRO.G {y : ℝ | y ^ 2 ≤ q} = ENNReal.ofReal (1 - α) := hq
    rw [h0] at h1
    have := ENNReal.ofReal_pos.2 (by linarith : 0 < 1 - α)
    rw [← h1] at this
    exact lt_irrefl _ this
  have key := EDRO.main_tendsto (P := P) (fun k ω => h x (ξ k ω))
    (fun k => hhx.comp (hξ k)) (hindep.comp (fun _ => h x) (fun _ => hhx))
    (fun i => (hident i).comp hhx) hL2 hvar q hq0
  have e : EDRO.G {t : ℝ | t ^ 2 ≤ q} = ENNReal.ofReal (1 - α) := hq
  rw [e] at key
  exact key
