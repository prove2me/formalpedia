-- Prove2me | solution 1 for FriendlyShadow.Gaussian.lemma_41
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T12:40:10.140437+00:00
-- url     : https://prove2.me/submissions/22aa847e-ae39-4f92-859a-f05837aa87af

import Mathlib

open MeasureTheory

set_option autoImplicit false

namespace FSL41

noncomputable def g {d : ℕ} (ν : Fin d → ℝ → ℝ) (i j k : Fin d) (x : ℝ) : ℝ :=
  ((if k = i then x else 1) * (if k = j then x else 1)) * ν k x

lemma int_x {d : ℕ} (ν : Fin d → ℝ → ℝ) (hν0 : ∀ i γ, 0 ≤ ν i γ)
    (hνint : ∀ i, Integrable (ν i)) (hν2 : ∀ i, Integrable (fun γ => γ ^ 2 * ν i γ))
    (k : Fin d) : Integrable (fun x => x * ν k x) := by
  refine Integrable.mono' ((hνint k).add (hν2 k))
    (aestronglyMeasurable_id.mul (hνint k).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  have h0 := hν0 k x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
  have : |x| ≤ 1 + x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x, sq_nonneg (|x| - 1)]
  simp only [Pi.add_apply]
  nlinarith

lemma g_int {d : ℕ} (ν : Fin d → ℝ → ℝ) (hν0 : ∀ i γ, 0 ≤ ν i γ)
    (hνint : ∀ i, Integrable (ν i)) (hν2 : ∀ i, Integrable (fun γ => γ ^ 2 * ν i γ))
    (i j k : Fin d) : Integrable (g ν i j k) := by
  have hx := int_x ν hν0 hνint hν2 k
  by_cases hi : k = i <;> by_cases hj : k = j
  · have e : g ν i j k = fun x => x ^ 2 * ν k x := by
      funext x; simp only [g, if_pos hi, if_pos hj]; ring
    rw [e]; exact hν2 k
  · have e : g ν i j k = fun x => x * ν k x := by
      funext x; simp only [g, if_pos hi, if_neg hj]; ring
    rw [e]; exact hx
  · have e : g ν i j k = fun x => x * ν k x := by
      funext x; simp only [g, if_neg hi, if_pos hj]; ring
    rw [e]; exact hx
  · have e : g ν i j k = ν k := by
      funext x; simp only [g, if_neg hi, if_neg hj]; ring
    rw [e]; exact hνint k

lemma prod_g {d : ℕ} (ν : Fin d → ℝ → ℝ) (i j : Fin d) (h : Fin d → ℝ) :
    ∏ k, g ν i j k (h k) = h i * h j * ∏ k, ν k (h k) := by
  simp only [g, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]

lemma gval_ne {d : ℕ} (ν : Fin d → ℝ → ℝ) (hν1 : ∀ i, ∫ γ, ν i γ = 1)
    (i j : Fin d) (hij : i ≠ j) (k : Fin d) :
    ∫ x, g ν i j k x = (if k = i then ∫ x, x * ν k x else 1) *
      (if k = j then ∫ x, x * ν k x else 1) := by
  by_cases hi : k = i
  · have hj : k ≠ j := fun h => hij (hi.symm.trans h)
    simp only [g, if_pos hi, if_neg hj, mul_one]
  · by_cases hj : k = j
    · simp only [g, if_neg hi, if_pos hj, one_mul]
    · simp only [g, if_neg hi, if_neg hj, one_mul, mul_one]; exact hν1 k

lemma gval_eq {d : ℕ} (ν : Fin d → ℝ → ℝ) (hν1 : ∀ i, ∫ γ, ν i γ = 1)
    (i k : Fin d) :
    ∫ x, g ν i i k x = if k = i then ∫ x, x ^ 2 * ν k x else 1 := by
  by_cases hi : k = i
  · simp only [g, if_pos hi]
    congr 1; funext x; ring
  · simp only [g, if_neg hi, one_mul]; exact hν1 k

lemma F_eq {d : ℕ} (ν : Fin d → ℝ → ℝ) (i j : Fin d) :
    (fun h : Fin d → ℝ => h i * h j * ∏ k, ν k (h k)) = fun h => ∏ k, g ν i j k (h k) := by
  funext h; rw [prod_g]

lemma F_int {d : ℕ} (ν : Fin d → ℝ → ℝ) (hν0 : ∀ i γ, 0 ≤ ν i γ)
    (hνint : ∀ i, Integrable (ν i)) (hν2 : ∀ i, Integrable (fun γ => γ ^ 2 * ν i γ))
    (i j : Fin d) :
    Integrable (fun h : Fin d → ℝ => h i * h j * ∏ k, ν k (h k)) := by
  rw [F_eq, volume_pi]
  exact Integrable.fintype_prod (fun k => g_int ν hν0 hνint hν2 i j k)

lemma E_eq {d : ℕ} (ν : Fin d → ℝ → ℝ) (hν1 : ∀ i, ∫ γ, ν i γ = 1) (i j : Fin d) :
    ∫ h : Fin d → ℝ, h i * h j * ∏ k, ν k (h k) =
      if i = j then ∫ x, x ^ 2 * ν i x else (∫ x, x * ν i x) * ∫ x, x * ν j x := by
  rw [F_eq, volume_pi, integral_fintype_prod_eq_prod]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Finset.prod_congr rfl (fun k _ => gval_eq ν hν1 i k)]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]
  · rw [if_neg hij, Finset.prod_congr rfl (fun k _ => gval_ne ν hν1 i j hij k)]
    simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]

lemma p_int {d : ℕ} (ν : Fin d → ℝ → ℝ) (hνint : ∀ i, Integrable (ν i)) :
    Integrable (fun h : Fin d → ℝ => ∏ k, ν k (h k)) := by
  rw [volume_pi]; exact Integrable.fintype_prod hνint

lemma p_integral {d : ℕ} (ν : Fin d → ℝ → ℝ) (hν1 : ∀ i, ∫ γ, ν i γ = 1) :
    ∫ h : Fin d → ℝ, ∏ k, ν k (h k) = 1 := by
  rw [volume_pi, integral_fintype_prod_eq_prod]
  simp only [hν1, Finset.prod_const_one]

lemma sq_expand {d : ℕ} (ν : Fin d → ℝ → ℝ) (z : Fin d → ℝ) (h : Fin d → ℝ) :
    (∑ i, z i * h i) ^ 2 * ∏ k, ν k (h k) =
      ∑ i, ∑ j, z i * z j * (h i * h j * ∏ k, ν k (h k)) := by
  rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- Second moment of `Z = Σ zᵢhᵢ` under the product density. -/
lemma second_moment {d : ℕ} (z : Fin d → ℝ)
    (ν : Fin d → ℝ → ℝ) (hν0 : ∀ i γ, 0 ≤ ν i γ) (hνint : ∀ i, Integrable (ν i))
    (hν1 : ∀ i, ∫ γ, ν i γ = 1) (hν2 : ∀ i, Integrable (fun γ => γ ^ 2 * ν i γ)) :
    Integrable (fun h : Fin d → ℝ => (∑ i, z i * h i) ^ 2 * ∏ k, ν k (h k)) ∧
    ∫ h : Fin d → ℝ, (∑ i, z i * h i) ^ 2 * ∏ k, ν k (h k) =
      (∑ i, z i * ∫ x, x * ν i x) ^ 2 +
        ∑ i, z i ^ 2 * ((∫ x, x ^ 2 * ν i x) - (∫ x, x * ν i x) ^ 2) := by
  have e : (fun h : Fin d → ℝ => (∑ i, z i * h i) ^ 2 * ∏ k, ν k (h k)) =
      fun h => ∑ i, ∑ j, z i * z j * (h i * h j * ∏ k, ν k (h k)) := by
    funext h; exact sq_expand ν z h
  have hint : ∀ i j, Integrable (fun h : Fin d → ℝ => z i * z j * (h i * h j * ∏ k, ν k (h k))) :=
    fun i j => (F_int ν hν0 hνint hν2 i j).const_mul _
  refine ⟨?_, ?_⟩
  · rw [e]
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))
  rw [e, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hint _ j), integral_const_mul, E_eq ν hν1]
  set m1 : Fin d → ℝ := fun i => ∫ x, x * ν i x with hm1
  set m2 : Fin d → ℝ := fun i => ∫ x, x ^ 2 * ν i x with hm2
  have key : ∀ i j, z i * z j * (if i = j then m2 i else m1 i * m1 j) =
      (z i * m1 i) * (z j * m1 j) + (if i = j then z i ^ 2 * (m2 i - m1 i ^ 2) else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp only [if_true]; ring
    · simp only [if_neg hij]; ring
  have key' : ∀ i j, z i * z j * (if i = j then ∫ x, x ^ 2 * ν i x
      else (∫ x, x * ν i x) * ∫ x, x * ν j x) =
      (z i * m1 i) * (z j * m1 j) + (if i = j then z i ^ 2 * (m2 i - m1 i ^ 2) else 0) := key
  simp_rw [key', Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sq, Finset.sum_mul_sum]

end FSL41

open MeasureTheory in
theorem solution {d : ℕ} (hd : 3 ≤ d) (z : Fin d → ℝ) (hz : ∑ i, |z i| = 1)
    (ν : Fin d → ℝ → ℝ) (hν0 : ∀ i γ, 0 ≤ ν i γ) (hνint : ∀ i, Integrable (ν i))
    (hν1 : ∀ i, ∫ γ, ν i γ = 1) (hν2 : ∀ i, Integrable (fun γ => γ ^ 2 * ν i γ))
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hvar : ∀ i, τ ^ 2 ≤ (∫ γ, γ ^ 2 * ν i γ) - (∫ γ, γ * ν i γ) ^ 2) :
    ENNReal.ofReal (τ / (2 * Real.sqrt d)) *
        ∫⁻ h : Fin d → ℝ, ENNReal.ofReal (|∑ i, z i * h i| * ∏ i, ν i (h i)) ≤
      ∫⁻ h : Fin d → ℝ, ENNReal.ofReal ((∑ i, z i * h i) ^ 2 * ∏ i, ν i (h i)) := by
  obtain ⟨hZint, hI⟩ := FSL41.second_moment z ν hν0 hνint hν1 hν2
  set I := ∫ h : Fin d → ℝ, (∑ i, z i * h i) ^ 2 * ∏ k, ν k (h k) with hIdef
  set a := τ / (2 * Real.sqrt d) with ha
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hdpos.le
  have hsqpos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
  have ha0 : 0 ≤ a := by positivity
  -- lower bound on I
  have hzsq : (1 : ℝ) ≤ d * ∑ i, z i ^ 2 := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |z i|)
    simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at hcs
    rw [hz] at hcs; simpa using hcs
  have hIlow : τ ^ 2 * ∑ i, z i ^ 2 ≤ I := by
    rw [hI, Finset.mul_sum]
    have h1 : ∑ i, τ ^ 2 * z i ^ 2 ≤
        ∑ i, z i ^ 2 * ((∫ x, x ^ 2 * ν i x) - (∫ x, x * ν i x) ^ 2) :=
      Finset.sum_le_sum (fun i _ => by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hvar i) (sq_nonneg _))
    nlinarith [sq_nonneg (∑ i, z i * ∫ x, x * ν i x)]
  have ha2 : a ^ 2 ≤ I := by
    have e : a ^ 2 = τ ^ 2 / (4 * d) := by
      rw [ha, div_pow, mul_pow, hsq]; ring
    rw [e]
    have hτd : τ ^ 2 / (4 * d) ≤ τ ^ 2 * ∑ i, z i ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg τ]
    linarith
  -- pointwise AM-GM
  have hp0 : ∀ h : Fin d → ℝ, 0 ≤ ∏ k, ν k (h k) :=
    fun h => Finset.prod_nonneg (fun k _ => hν0 k (h k))
  have hpint := FSL41.p_int ν hνint
  have hp1 := FSL41.p_integral ν hν1
  have hGint : Integrable (fun h : Fin d → ℝ =>
      ((∑ i, z i * h i) ^ 2 * ∏ k, ν k (h k) + a ^ 2 * ∏ k, ν k (h k)) / 2) :=
    (hZint.add (hpint.const_mul (a ^ 2))).div_const 2
  have hG : ∫ h : Fin d → ℝ,
      ((∑ i, z i * h i) ^ 2 * ∏ k, ν k (h k) + a ^ 2 * ∏ k, ν k (h k)) / 2 = (I + a ^ 2) / 2 := by
    rw [integral_div, integral_add hZint (hpint.const_mul _), integral_const_mul, hp1, mul_one]
  have step1 : ENNReal.ofReal a *
      ∫⁻ h : Fin d → ℝ, ENNReal.ofReal (|∑ i, z i * h i| * ∏ i, ν i (h i)) =
      ∫⁻ h : Fin d → ℝ, ENNReal.ofReal (a * (|∑ i, z i * h i| * ∏ i, ν i (h i))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1; funext h; rw [ENNReal.ofReal_mul ha0]
  rw [step1]
  calc ∫⁻ h : Fin d → ℝ, ENNReal.ofReal (a * (|∑ i, z i * h i| * ∏ i, ν i (h i)))
      ≤ ∫⁻ h : Fin d → ℝ, ENNReal.ofReal
          (((∑ i, z i * h i) ^ 2 * ∏ k, ν k (h k) + a ^ 2 * ∏ k, ν k (h k)) / 2) := by
        refine lintegral_mono (fun h => ENNReal.ofReal_le_ofReal ?_)
        have hp := hp0 h
        have hZ2 : (∑ i, z i * h i) ^ 2 = |∑ i, z i * h i| ^ 2 := (sq_abs _).symm
        rw [hZ2]
        nlinarith [mul_nonneg (sq_nonneg (|∑ i, z i * h i| - a)) hp]
    _ = ENNReal.ofReal ((I + a ^ 2) / 2) := by
        rw [← hG, ofReal_integral_eq_lintegral_ofReal hGint
          (Filter.Eventually.of_forall (fun h => by
            have := hp0 h; positivity))]
    _ ≤ ENNReal.ofReal I := ENNReal.ofReal_le_ofReal (by linarith)
    _ = ∫⁻ h : Fin d → ℝ, ENNReal.ofReal ((∑ i, z i * h i) ^ 2 * ∏ i, ν i (h i)) := by
        rw [hIdef, ofReal_integral_eq_lintegral_ofReal hZint
          (Filter.Eventually.of_forall (fun h => by
            have := hp0 h; positivity))]
