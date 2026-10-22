-- Prove2me | solution 1 for DemandSubstitution.Comparison.proposition6_ii_some_product_competitive_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T12:17:25.825293+00:00
-- url     : https://prove2.me/submissions/357c9489-6abc-4361-84d1-41f7478e2eca

import Mathlib
import Definitions.Def_DemandSubstitution_Comparison_Setting

set_option autoImplicit false

open MeasureTheory

namespace P2MD63893B2

open DemandSubstitution.Comparison

variable {n : ℕ}

/-- Newsvendor profit of product `k` at stock `q` and effective demand `D`. -/
def phi (M : Model n) (k : Fin n) (q D : ℝ) : ℝ :=
  (M.r k - M.s k) * min D q - M.o k * q

lemma firm_integrand (M : Model n) (k : Fin n) (q D : ℝ) :
    M.u k * D - M.u k * max (D - q) 0 - M.o k * max (q - D) 0 = phi M k q D := by
  unfold phi Model.u Model.o
  rcases le_total D q with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith), min_eq_left h]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), min_eq_right h]; ring

lemma central_integrand (M : Model n) (k : Fin n) (q D : ℝ) :
    M.r k * min D q - M.c k * q + M.s k * max (q - D) 0 = phi M k q D := by
  unfold phi Model.o
  rcases le_total D q with h | h
  · rw [max_eq_left (by linarith), min_eq_left h]; ring
  · rw [max_eq_right (by linarith), min_eq_right h]; ring

lemma ds_update (M : Model n) (Q x : Fin n → ℝ) (i : Fin n) (q : ℝ) :
    Ds M (Function.update Q i q) x i = Ds M Q x i := by
  unfold Ds
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma ds_ge (M : Model n) (Q x : Fin n → ℝ) (k : Fin n) : x k ≤ Ds M Q x k := by
  unfold Ds
  have : 0 ≤ ∑ j ∈ Finset.univ.erase k, M.a j k * max (x j - Q j) 0 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (M.ha_nonneg j k) (le_max_right _ _)
  linarith

lemma ds_anti (M : Model n) (Q Q' x : Fin n → ℝ) (k : Fin n) (h : ∀ j, Q j ≤ Q' j) :
    Ds M Q' x k ≤ Ds M Q x k := by
  unfold Ds
  have : ∑ j ∈ Finset.univ.erase k, M.a j k * max (x j - Q' j) 0 ≤
      ∑ j ∈ Finset.univ.erase k, M.a j k * max (x j - Q j) 0 :=
    Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (max_le_max (by linarith [h j]) le_rfl) (M.ha_nonneg j k)
  linarith

lemma ds_continuous (M : Model n) (Q : Fin n → ℝ) (k : Fin n) :
    Continuous fun x => Ds M Q x k := by
  unfold Ds
  exact (continuous_apply k).add (continuous_finsetSum _ fun j _ =>
    continuous_const.mul (((continuous_apply j).sub continuous_const).max continuous_const))

lemma phi_integrable (M : Model n) (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : DemandSubstitution.Competitive.IsDemandLaw μ) (Q : Fin n → ℝ) (k : Fin n) (q : ℝ) :
    Integrable (fun x => phi M k q (Ds M Q x k)) μ := by
  have hrs : 0 < M.r k - M.s k := by linarith [M.hrc k, M.hcs k]
  refine Integrable.mono' (((hμ.2.2 k).abs.const_mul (M.r k - M.s k)).add
    (integrable_const ((M.r k - M.s k) * |q| + |M.o k * q|))) ?_ ?_
  · unfold phi
    exact (((continuous_const.mul ((ds_continuous M Q k).min continuous_const)).sub
      continuous_const)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    have h1 := ds_ge M Q x k
    have h2 : |min (Ds M Q x k) q| ≤ |x k| + |q| := by
      rw [abs_le]
      constructor
      · have := le_min (show -(|x k| + |q|) ≤ Ds M Q x k by linarith [neg_abs_le (x k), abs_nonneg q])
          (show -(|x k| + |q|) ≤ q by linarith [neg_abs_le q, abs_nonneg (x k)])
        exact this
      · linarith [min_le_right (Ds M Q x k) q, le_abs_self q, abs_nonneg (x k)]
    unfold phi
    simp only [Real.norm_eq_abs, Pi.add_apply]
    calc |(M.r k - M.s k) * min (Ds M Q x k) q - M.o k * q|
        ≤ |(M.r k - M.s k) * min (Ds M Q x k) q| + |M.o k * q| := abs_sub _ _
      _ = (M.r k - M.s k) * |min (Ds M Q x k) q| + |M.o k * q| := by
          rw [abs_mul, abs_of_pos hrs]
      _ ≤ (M.r k - M.s k) * (|x k| + |q|) + |M.o k * q| := by gcongr
      _ = (M.r k - M.s k) * |x k| + ((M.r k - M.s k) * |q| + |M.o k * q|) := by ring

lemma firm_eq (M : Model n) (μ : Measure (Fin n → ℝ)) (Q : Fin n → ℝ) (k : Fin n) :
    firmProfit M μ Q k = ∫ x, phi M k (Q k) (Ds M Q x k) ∂μ := by
  unfold firmProfit
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => firm_integrand M k (Q k) _)

lemma central_eq (M : Model n) (μ : Measure (Fin n → ℝ)) (Q : Fin n → ℝ) :
    centralProfit M μ Q = ∫ x, ∑ k, phi M k (Q k) (Ds M Q x k) ∂μ := by
  unfold centralProfit
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact Finset.sum_congr rfl fun k _ => central_integrand M k (Q k) _

lemma phi_mono (M : Model n) (k : Fin n) (q D D' : ℝ) (h : D ≤ D') :
    phi M k q D ≤ phi M k q D' := by
  unfold phi
  have hrs : 0 ≤ M.r k - M.s k := by linarith [M.hrc k, M.hcs k]
  have := min_le_min_right q h
  nlinarith

lemma key (a b D D' : ℝ) (hab : a < b) (hD : D ≤ D') :
    0 ≤ (min D' ((a + b) / 2) - min D' a) + (min D ((a + b) / 2) - min D b) := by
  simp only [min_def]
  split_ifs <;> linarith

lemma key_strict (a b D D' : ℝ) (hab : a < b) (hD : D ≤ D') (h1 : a < D) (h2 : D < b) :
    0 < (min D' ((a + b) / 2) - min D' a) + (min D ((a + b) / 2) - min D b) := by
  simp only [min_def]
  split_ifs <;> linarith

theorem main {n : ℕ} [NeZero n] (M : Model n)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] (hμ : DemandSubstitution.Competitive.IsDemandLaw μ)
    (hf : DemandSubstitution.Competitive.HasPositiveDensity μ) (Qc Qd : Fin n → ℝ)
    (hc : IsCentralOptimal M μ Qc) (hd : IsNash M μ Qd) :
    ∃ i, Qc i ≤ Qd i := by
  by_contra hcon
  push_neg at hcon
  set i : Fin n := 0 with hi
  set a := Qd i with ha_def
  set b := Qc i with hb_def
  set m := (a + b) / 2 with hm_def
  have hab : a < b := hcon i
  have ha0 : 0 ≤ a := hd.1 i
  have hm0 : 0 ≤ m := by rw [hm_def]; linarith
  have hrs : 0 < M.r i - M.s i := by linarith [M.hrc i, M.hcs i]
  -- Nash inequality
  have hN := (hd.2 i).2 m hm0
  rw [Function.update_eq_self, firm_eq, firm_eq] at hN
  simp only [Function.update_self, ds_update] at hN
  -- central inequality
  set Q' := Function.update Qc i m with hQ'
  have hQ'0 : ∀ j, 0 ≤ Q' j := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [hQ', Function.update_self]; exact hm0
    · rw [hQ', Function.update_of_ne hj]; exact hc.1 j
  have hC := hc.2 Q' hQ'0
  rw [central_eq, central_eq] at hC
  have hQ'le : ∀ j, Q' j ≤ Qc j := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [hQ', Function.update_self]; rw [hm_def]; linarith
    · rw [hQ', Function.update_of_ne hj]
  have hint : ∀ Q : Fin n → ℝ, Integrable (fun x => ∑ k, phi M k (Q k) (Ds M Q x k)) μ :=
    fun Q => integrable_finsetSum _ fun k _ => phi_integrable M μ hμ Q k (Q k)
  have hpt : ∀ x, phi M i m (Ds M Qc x i) - phi M i b (Ds M Qc x i) ≤
      (∑ k, phi M k (Q' k) (Ds M Q' x k)) - ∑ k, phi M k (Qc k) (Ds M Qc x k) := by
    intro x
    rw [← Finset.sum_sub_distrib, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hQ'i : Q' i = m := by rw [hQ', Function.update_self]
    rw [hQ'i, hQ', ds_update, ← hQ']
    have : 0 ≤ ∑ k ∈ Finset.univ.erase i,
        (phi M k (Q' k) (Ds M Q' x k) - phi M k (Qc k) (Ds M Qc x k)) := by
      refine Finset.sum_nonneg fun k hk => ?_
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      have hQk : Q' k = Qc k := by rw [hQ', Function.update_of_ne hki]
      rw [hQk]
      have := phi_mono M k (Qc k) _ _ (ds_anti M Q' Qc x k hQ'le)
      linarith
    linarith
  have hC2 : ∫ x, (phi M i m (Ds M Qc x i) - phi M i b (Ds M Qc x i)) ∂μ ≤ 0 := by
    have h1 : ∫ x, (phi M i m (Ds M Qc x i) - phi M i b (Ds M Qc x i)) ∂μ ≤
        ∫ x, ((∑ k, phi M k (Q' k) (Ds M Q' x k)) - ∑ k, phi M k (Qc k) (Ds M Qc x k)) ∂μ :=
      integral_mono ((phi_integrable M μ hμ Qc i m).sub (phi_integrable M μ hμ Qc i b))
        ((hint Q').sub (hint Qc)) hpt
    rw [integral_sub (hint Q') (hint Qc)] at h1
    linarith
  have hN2 : ∫ x, (phi M i m (Ds M Qd x i) - phi M i a (Ds M Qd x i)) ∂μ ≤ 0 := by
    rw [integral_sub (phi_integrable M μ hμ Qd i m) (phi_integrable M μ hμ Qd i a)]
    linarith
  -- the combined integrand
  set Φ : (Fin n → ℝ) → ℝ := fun x =>
    (phi M i m (Ds M Qd x i) - phi M i a (Ds M Qd x i)) +
      (phi M i m (Ds M Qc x i) - phi M i b (Ds M Qc x i)) with hΦ
  have hΦint : Integrable Φ μ :=
    ((phi_integrable M μ hμ Qd i m).sub (phi_integrable M μ hμ Qd i a)).add
      ((phi_integrable M μ hμ Qc i m).sub (phi_integrable M μ hμ Qc i b))
  have hΦeq : ∀ x, Φ x = (M.r i - M.s i) *
      ((min (Ds M Qd x i) m - min (Ds M Qd x i) a) +
        (min (Ds M Qc x i) m - min (Ds M Qc x i) b)) := by
    intro x
    simp only [hΦ, phi, hm_def]
    ring
  have hle : ∀ j, Qd j ≤ Qc j := fun j => (hcon j).le
  have hΦnn : 0 ≤ Φ := by
    intro x
    rw [hΦeq]
    exact mul_nonneg hrs.le (key a b _ _ hab (ds_anti M Qd Qc x i hle))
  have hΦle : ∫ x, Φ x ∂μ ≤ 0 := by
    have h2 : ∫ x, Φ x ∂μ = ∫ x, (phi M i m (Ds M Qd x i) - phi M i a (Ds M Qd x i)) ∂μ +
        ∫ x, (phi M i m (Ds M Qc x i) - phi M i b (Ds M Qc x i)) ∂μ :=
      integral_add ((phi_integrable M μ hμ Qd i m).sub (phi_integrable M μ hμ Qd i a))
        ((phi_integrable M μ hμ Qc i m).sub (phi_integrable M μ hμ Qc i b))
    linarith
  -- the box
  set S : Set (Fin n → ℝ) := Set.pi Set.univ fun j => Set.Ioo (Qd j) (Qc j) with hS
  have hSopen : IsOpen S := isOpen_set_pi Set.finite_univ fun j _ => isOpen_Ioo
  have hSne : S.Nonempty := by
    refine ⟨fun j => (Qd j + Qc j) / 2, ?_⟩
    simp only [hS, Set.mem_pi, Set.mem_univ, Set.mem_Ioo, forall_const]
    intro j
    constructor <;> linarith [hcon j]
  have hSsupp : S ⊆ Function.support Φ := by
    intro x hx
    simp only [hS, Set.mem_pi, Set.mem_univ, Set.mem_Ioo, forall_const] at hx
    have hDc : Ds M Qc x i = x i := by
      unfold Ds
      have : ∑ j ∈ Finset.univ.erase i, M.a j i * max (x j - Qc j) 0 = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [max_eq_right (by linarith [(hx j).2])]; ring
      rw [this, add_zero]
    rw [Function.mem_support, hΦeq]
    refine (mul_pos hrs (key_strict a b _ _ hab (ds_anti M Qd Qc x i hle) ?_ ?_)).ne'
    · rw [hDc]; exact (hx i).1
    · rw [hDc]; exact (hx i).2
  have hSpos : 0 < μ S := by
    obtain ⟨f, hfm, hμf, hfpos⟩ := hf
    rw [hμf, withDensity_apply _ hSopen.measurableSet, lintegral_pos_iff_support hfm,
      Measure.restrict_apply (measurableSet_support hfm)]
    have hsub : S ⊆ Function.support f ∩ S := by
      intro x hx
      refine ⟨(hfpos x fun j => ?_).ne', hx⟩
      simp only [hS, Set.mem_pi, Set.mem_univ, Set.mem_Ioo, forall_const] at hx
      linarith [(hx j).1, hd.1 j]
    exact lt_of_lt_of_le (hSopen.measure_pos volume hSne) (measure_mono hsub)
  have hpos : 0 < ∫ x, Φ x ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hΦnn hΦint]
    exact lt_of_lt_of_le hSpos (measure_mono hSsupp)
  linarith

end P2MD63893B2

open MeasureTheory DemandSubstitution.Comparison in
theorem solution {n : ℕ} [NeZero n] (M : Model n)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] (hμ : DemandSubstitution.Competitive.IsDemandLaw μ)
    (hf : DemandSubstitution.Competitive.HasPositiveDensity μ) (Qc Qd : Fin n → ℝ)
    (hc : IsCentralOptimal M μ Qc) (hd : IsNash M μ Qd) :
    ∃ i, Qc i ≤ Qd i := by
  exact P2MD63893B2.main M μ hμ hf Qc Qd hc hd
