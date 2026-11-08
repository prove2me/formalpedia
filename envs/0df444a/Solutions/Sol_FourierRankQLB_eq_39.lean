-- Prove2me | solution 1 for FourierRankQLB.eq_39
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:42:52.004117+00:00
-- url     : https://prove2.me/submissions/691cfa16-dc44-4f7e-811b-407e2c7f8792

import Mathlib
import Definitions.Def_FourierRankQLB_hardBody
import Definitions.Def_FourierRankQLB_rs
import Definitions.Def_FourierRankQLB_Rs__d75a51

open Matrix

namespace FourierRankQLB.Aux_FR

open FourierRankQLB

theorem sum_trunc {n d : ℕ} (hd : d ≤ n) (F : Fin n → ℝ) (hF : ∀ i : Fin n, d ≤ i.1 → F i = 0) :
    ∑ i, F i = ∑ k : Fin d, F (Fin.castLE hd k) := by
  classical
  have h1 : ∑ k : Fin d, F (Fin.castLE hd k) =
      ∑ i ∈ (Finset.univ.map (Fin.castLEEmb hd)), F i := by
    rw [Finset.sum_map]; rfl
  rw [h1]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  apply hF
  by_contra hlt
  push_neg at hlt
  apply hi
  rw [Finset.mem_map]
  exact ⟨⟨i.1, hlt⟩, Finset.mem_univ _, by ext; simp⟩

theorem a_bounds (d : ℕ) (hd : 1 ≤ d) : 0 < ad d ∧ ad d < 1 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hx0 : 0 < alpha / d := by unfold alpha; positivity
  have hx1 : alpha / d ≤ alpha := by
    rw [div_le_iff₀ hdpos]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have ha : 0 < alpha := by unfold alpha; positivity
    nlinarith
  have hxpi : alpha / d < Real.pi / 2 := by
    have : alpha < Real.pi / 2 := by unfold alpha; linarith [Real.pi_pos]
    linarith
  have hcos1 : Real.cos (alpha / d) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith [Real.pi_pos]) hx0
    rwa [Real.cos_zero] at this
  have hcos0 : 0 < Real.cos (alpha / d) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hxpi⟩
  unfold ad gd
  constructor <;> linarith

end FourierRankQLB.Aux_FR

open FourierRankQLB FourierRankQLB.Aux_FR in
theorem solution {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (Q : Od (dn n)) :
    Metric.closedBall (0 : Ambient n) (rs n s) ⊆ hardBody s Q ∧
      hardBody s Q ⊆ Metric.closedBall (0 : Ambient n) (Rs n s) := by
  classical
  have hdn : dn n ≤ n := by unfold dn; omega
  have hd1 : 1 ≤ dn n := by unfold dn; omega
  obtain ⟨ha0, ha1⟩ := a_bounds (dn n) hd1
  set a := ad (dn n) with ha
  set M : Matrix (Fin (dn n)) (Fin (dn n)) ℝ := (Q : Matrix (Fin (dn n)) (Fin (dn n)) ℝ) with hM
  have hMorth : Mᵀ * M = 1 := (Matrix.mem_orthogonalGroup_iff' (n := Fin (dn n)) (R := ℝ)).mp Q.2
  -- the key formula for the quadratic form
  have key : ∀ Y : Fin n → ℝ,
      let u : Fin (dn n) → ℝ := fun k => Y (Fin.castLE hdn k)
      Y ⬝ᵥ (Abar Q *ᵥ Y) = (∑ i, Y i ^ 2) + (a - 1 / 2) * (u ⬝ᵥ u) + (1 / 2) * (u ⬝ᵥ (M *ᵥ u)) := by
    intro Y u
    let q2 : Fin n → Fin n → ℝ := fun i j =>
      if h : i.1 < (dn n) ∧ j.1 < (dn n) then M ⟨i.1, h.1⟩ ⟨j.1, h.2⟩ else 0
    let c : Fin n → ℝ := fun i => if i.1 < (dn n) then 1 / 2 + a else 1
    have hAbar : ∀ i j, Abar Q i j = (if i = j then c i else 0) + (1 / 4) * (q2 i j + q2 j i) := by
      intro i j
      by_cases hi : i.1 < (dn n) <;> by_cases hj : j.1 < (dn n)
      · simp only [Abar, Matrix.of_apply, dif_pos (And.intro hi hj), AQ, Matrix.add_apply,
          Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply, smul_eq_mul, q2,
          dif_pos (And.intro hj hi), c, if_pos hi, ← hM, ha, ad]
        by_cases hij : i = j
        · subst hij; simp
        · have hne : (⟨i.1, hi⟩ : Fin (dn n)) ≠ ⟨j.1, hj⟩ := by
            intro h; exact hij (Fin.ext (Fin.mk.inj_iff.mp h))
          simp [hij, hne]
      · have hij : i ≠ j := fun h => hj (h ▸ hi)
        simp only [Abar, Matrix.of_apply, dif_neg (fun h : i.1 < dn n ∧ j.1 < dn n => hj h.2), q2,
          dif_neg (fun h : i.1 < (dn n) ∧ j.1 < (dn n) => hj h.2),
          dif_neg (fun h : j.1 < (dn n) ∧ i.1 < (dn n) => hj h.1), if_neg hij]
        ring
      · have hij : i ≠ j := fun h => hi (h ▸ hj)
        simp only [Abar, Matrix.of_apply, dif_neg (fun h : i.1 < dn n ∧ j.1 < dn n => hi h.1), q2,
          dif_neg (fun h : i.1 < (dn n) ∧ j.1 < (dn n) => hi h.1),
          dif_neg (fun h : j.1 < (dn n) ∧ i.1 < (dn n) => hi h.2), if_neg hij]
        ring
      · simp only [Abar, Matrix.of_apply, dif_neg (fun h : i.1 < dn n ∧ j.1 < dn n => hi h.1), q2,
          dif_neg (fun h : i.1 < (dn n) ∧ j.1 < (dn n) => hi h.1),
          dif_neg (fun h : j.1 < (dn n) ∧ i.1 < (dn n) => hi h.2), c, if_neg hi]
        split_ifs <;> ring
    have hq : ∑ i, Y i * ∑ j, q2 i j * Y j = u ⬝ᵥ (M *ᵥ u) := by
      rw [sum_trunc hdn]
      · simp only [dotProduct, mulVec, u]
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        rw [sum_trunc hdn]
        · apply Finset.sum_congr rfl
          intro l _
          simp [q2]
        · intro j hj
          simp [q2, show ¬ j.1 < (dn n) from by omega]
      · intro i hi
        simp [q2, show ¬ i.1 < (dn n) from by omega]
    have hq' : ∑ i, Y i * ∑ j, q2 j i * Y j = u ⬝ᵥ (M *ᵥ u) := by
      rw [← hq]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring
    have hc : ∑ i, Y i * ∑ j, (if i = j then c i else 0) * Y j =
        (∑ i, Y i ^ 2) + (a - 1 / 2) * (u ⬝ᵥ u) := by
      have h1 : ∀ i, Y i * ∑ j, (if i = j then c i else 0) * Y j =
          Y i ^ 2 + (a - 1 / 2) * (if i.1 < (dn n) then Y i ^ 2 else 0) := by
        intro i
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, c]
        split_ifs <;> ring
      simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 2
      rw [sum_trunc hdn]
      · simp only [dotProduct, u]
        apply Finset.sum_congr rfl; intro k _
        simp [Fin.coe_castLE, k.2]
        ring
      · intro i hi
        simp [show ¬ i.1 < (dn n) from by omega]
    have hsplit : Y ⬝ᵥ (Abar Q *ᵥ Y) =
        (∑ i, Y i * ∑ j, (if i = j then c i else 0) * Y j) +
          (1 / 4) * (∑ i, Y i * ∑ j, q2 i j * Y j) + (1 / 4) * (∑ i, Y i * ∑ j, q2 j i * Y j) := by
      simp only [dotProduct, mulVec, hAbar, add_mul, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      ring_nf
    rw [hsplit, hc, hq, hq']
    ring
  -- the Cauchy–Schwarz type bound
  have hCS : ∀ u : Fin (dn n) → ℝ, |u ⬝ᵥ (M *ᵥ u)| ≤ u ⬝ᵥ u := by
    intro u
    set v := M *ᵥ u with hv
    have hvv : v ⬝ᵥ v = u ⬝ᵥ u := by
      rw [hv, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hMorth, one_mulVec]
    have hsq : ∀ w : Fin (dn n) → ℝ, 0 ≤ w ⬝ᵥ w := fun w =>
      Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
    have h1 := hsq (u - v)
    have h2 := hsq (u + v)
    simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add] at h1 h2
    rw [dotProduct_comm v u, hvv] at h1 h2
    rw [abs_le]
    constructor <;> linarith
  -- bounds on the quadratic form
  have hbounds : ∀ y : Ambient n,
      a * ‖y‖ ^ 2 ≤ y.ofLp ⬝ᵥ (Abar Q *ᵥ y.ofLp) ∧
        y.ofLp ⬝ᵥ (Abar Q *ᵥ y.ofLp) ≤ (1 + a) * ‖y‖ ^ 2 := by
    intro y
    set Y := y.ofLp with hY
    have hnorm : ‖y‖ ^ 2 = ∑ i, Y i ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      simp [hY]
    have hk := key Y
    simp only at hk
    set u : Fin (dn n) → ℝ := fun k => Y (Fin.castLE hdn k) with hu
    have hCSu := hCS u
    have huu : u ⬝ᵥ u ≤ ∑ i, Y i ^ 2 := by
      have : u ⬝ᵥ u = ∑ i, (if i.1 < (dn n) then Y i ^ 2 else 0) := by
        rw [sum_trunc hdn]
        · simp only [dotProduct, hu]
          apply Finset.sum_congr rfl; intro k _
          simp [Fin.coe_castLE, k.2]
          ring
        · intro i hi
          simp [show ¬ i.1 < (dn n) from by omega]
      rw [this]
      apply Finset.sum_le_sum; intro i _
      split_ifs
      · exact le_refl _
      · exact sq_nonneg _
    have hu0 : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
    rw [abs_le] at hCSu
    rw [hnorm, hk]
    constructor <;> nlinarith
  constructor
  · intro y hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    have hn0 : 0 ≤ ‖y‖ := norm_nonneg _
    have hsq : ‖y‖ ^ 2 * (1 + a) ≤ s ^ 2 := by
      have h1 : ‖y‖ * Real.sqrt (1 + a) ≤ s := by
        unfold rs at hy
        rw [← ha] at hy
        rwa [le_div_iff₀ (Real.sqrt_pos.mpr (by linarith))] at hy
      have h2 : (‖y‖ * Real.sqrt (1 + a)) ^ 2 ≤ s ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hn0 (Real.sqrt_nonneg _)) h1 2
      rwa [mul_pow, Real.sq_sqrt (by linarith)] at h2
    show y.ofLp ⬝ᵥ (Abar Q *ᵥ y.ofLp) ≤ s ^ 2
    have := (hbounds y).2
    nlinarith
  · intro y hy
    have hy' : y.ofLp ⬝ᵥ (Abar Q *ᵥ y.ofLp) ≤ s ^ 2 := hy
    have h1 := (hbounds y).1
    rw [Metric.mem_closedBall, dist_zero_right]
    unfold Rs
    rw [← ha]
    rw [le_div_iff₀ (Real.sqrt_pos.mpr ha0)]
    have hn0 : 0 ≤ ‖y‖ := norm_nonneg _
    have h2 : (‖y‖ * Real.sqrt a) ^ 2 ≤ s ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ha0.le]
      nlinarith
    exact (pow_le_pow_iff_left₀ (mul_nonneg hn0 (Real.sqrt_nonneg _)) hs.le (by norm_num)).mp h2
