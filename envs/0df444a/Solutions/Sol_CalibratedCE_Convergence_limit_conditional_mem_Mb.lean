-- Prove2me | solution 1 for CalibratedCE.Convergence.limit_conditional_mem_Mb
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:08:57.521608+00:00
-- url     : https://prove2.me/submissions/946b1100-4e72-45b0-aa8a-50c78edae1b5

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_BestReply
import Definitions.Def_CalibratedCE_Convergence_EmpDist

open Filter Topology

namespace CalibratedCE.Convergence

lemma aux_lcm_N_rho {k : ℕ} (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k) (p : Fin k → ℝ) (j : Fin k)
    (t : ℕ) :
    (Shared.N f p t : ℝ) * Shared.rho f z p j t =
      (((Finset.range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ) := by
  unfold Shared.rho
  split_ifs with h
  · have h1 : ((Finset.range t).filter (fun s => f s = p ∧ z s = j)).card ≤ Shared.N f p t := by
      unfold Shared.N
      apply Finset.card_le_card
      intro s hs
      simp only [Finset.mem_filter] at hs ⊢
      exact ⟨hs.1, hs.2.1⟩
    rw [h] at h1
    have h2 : ((Finset.range t).filter (fun s => f s = p ∧ z s = j)).card = 0 := by omega
    rw [h2, h]
    simp
  · have hN : (Shared.N f p t : ℝ) ≠ 0 := by exact_mod_cast h
    field_simp

lemma aux_lcm_card_decomp {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (f : ℕ → Fin n → ℝ)
    (y : ℕ → Fin n) (t : ℕ) (a : Fin m) (b : Fin n) :
    (((Finset.range t).filter (fun s => R₁ (f s) = a ∧ y s = b)).card : ℝ) =
      ∑ p ∈ (Finset.range t).image f,
        if R₁ p = a then (Shared.N f p t : ℝ) * Shared.rho f y p b t else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := (Finset.range t).image f)]
  · push_cast
    apply Finset.sum_congr rfl
    intro p _
    rw [aux_lcm_N_rho]
    split_ifs with h
    · congr 2
      ext s
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hs, _, hy⟩, hf⟩
        exact ⟨hs, hf, hy⟩
      · rintro ⟨hs, hf, hy⟩
        refine ⟨⟨hs, ?_, hy⟩, hf⟩
        rw [hf]
        exact h
    · rw [Nat.cast_eq_zero, Finset.card_eq_zero]
      ext s
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨⟨_, ha, _⟩, hf⟩
      apply h
      rw [← hf]
      exact ha
  · intro s hs
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hs
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem f hs.1)

lemma aux_lcm_main_ineq {m n : ℕ} (u₁ : Fin m → Fin n → ℝ)
    (R₁ : (Fin n → ℝ) → Fin m) (hR₁ : IsBestReply₁ u₁ R₁)
    (f₁ : ℕ → Fin n → ℝ) (hf₁ : ∀ s, IsDist (f₁ s)) (y : ℕ → Fin n) (t : ℕ)
    (a a' : Fin m) :
    ∑ b, (((Finset.range t).filter (fun s => R₁ (f₁ s) = a ∧ y s = b)).card : ℝ) *
        (u₁ a' b - u₁ a b) ≤
      ∑ b, |u₁ a' b - u₁ a b| *
        ∑ p ∈ (Finset.range t).image f₁,
          |Shared.rho f₁ y p b t - p b| * (Shared.N f₁ p t : ℝ) := by
  simp_rw [aux_lcm_card_decomp R₁ f₁ y t a, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p hp
  have hpd : IsDist p := by
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hp
    exact hf₁ s
  have hN : (0:ℝ) ≤ Shared.N f₁ p t := Nat.cast_nonneg _
  by_cases h : R₁ p = a
  · simp only [h, if_true]
    have hbr := hR₁ p hpd a'
    rw [h] at hbr
    have h1 : ∑ b, p b * (u₁ a' b - u₁ a b) ≤ 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      linarith
    have h2 : ∀ b, (Shared.N f₁ p t : ℝ) * Shared.rho f₁ y p b t * (u₁ a' b - u₁ a b) ≤
        (Shared.N f₁ p t : ℝ) * (p b * (u₁ a' b - u₁ a b)) +
          |u₁ a' b - u₁ a b| * (|Shared.rho f₁ y p b t - p b| * (Shared.N f₁ p t : ℝ)) := by
      intro b
      have h3 : (Shared.rho f₁ y p b t - p b) * (u₁ a' b - u₁ a b) ≤
          |Shared.rho f₁ y p b t - p b| * |u₁ a' b - u₁ a b| := by
        rw [← abs_mul]
        exact le_abs_self _
      have h4 := mul_le_mul_of_nonneg_left h3 hN
      nlinarith [h4]
    calc ∑ b, (Shared.N f₁ p t : ℝ) * Shared.rho f₁ y p b t * (u₁ a' b - u₁ a b)
        ≤ ∑ b, ((Shared.N f₁ p t : ℝ) * (p b * (u₁ a' b - u₁ a b)) +
          |u₁ a' b - u₁ a b| * (|Shared.rho f₁ y p b t - p b| * (Shared.N f₁ p t : ℝ))) :=
          Finset.sum_le_sum (fun b _ => h2 b)
      _ = (Shared.N f₁ p t : ℝ) * ∑ b, p b * (u₁ a' b - u₁ a b) +
          ∑ b, |u₁ a' b - u₁ a b| *
            (|Shared.rho f₁ y p b t - p b| * (Shared.N f₁ p t : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ b, |u₁ a' b - u₁ a b| *
            (|Shared.rho f₁ y p b t - p b| * (Shared.N f₁ p t : ℝ)) := by
        have := mul_nonpos_of_nonneg_of_nonpos hN h1
        linarith
  · simp only [h, if_false, zero_mul, Finset.sum_const_zero]
    apply Finset.sum_nonneg
    intro b _
    positivity

end CalibratedCE.Convergence

open CalibratedCE CalibratedCE.Convergence

open Filter Topology

theorem solution {m n : ℕ} (u₁ : Fin m → Fin n → ℝ)
    (R₁ : (Fin n → ℝ) → Fin m) (hR₁ : IsBestReply₁ u₁ R₁)
    (f₁ : ℕ → Fin n → ℝ) (hf₁ : ∀ s, IsDist (f₁ s)) (y : ℕ → Fin n)
    (hcal : Shared.Calibrated f₁ y) (φ : ℕ → ℕ) (hφ : StrictMono φ) (D : Fin m → Fin n → ℝ)
    (hD : ∀ a b, Tendsto (fun i => empDist (fun s => R₁ (f₁ s)) y (φ i) a b) atTop
      (𝓝 (D a b)))
    (a : Fin m) (ha : 0 < ∑ c, D a c) :
    (fun b => D a b / ∑ c, D a c) ∈ Mb u₁ a := by
  have key : ∀ a' : Fin m, ∑ b, D a b * (u₁ a' b - u₁ a b) ≤ 0 := by
    intro a'
    have hineq : ∀ t, ∑ b, empDist (fun s => R₁ (f₁ s)) y t a b * (u₁ a' b - u₁ a b) ≤
        ∑ b, |u₁ a' b - u₁ a b| * CalibratedCE.Shared.calibScore f₁ y b t := by
      intro t
      have h := aux_lcm_main_ineq u₁ R₁ hR₁ f₁ hf₁ y t a a'
      have e1 : ∑ b, empDist (fun s => R₁ (f₁ s)) y t a b * (u₁ a' b - u₁ a b) =
          (∑ b, (((Finset.range t).filter (fun s => R₁ (f₁ s) = a ∧ y s = b)).card : ℝ) *
            (u₁ a' b - u₁ a b)) / (t : ℝ) := by
        unfold empDist
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun b _ => by ring)
      have e2 : ∑ b, |u₁ a' b - u₁ a b| * CalibratedCE.Shared.calibScore f₁ y b t =
          (∑ b, |u₁ a' b - u₁ a b| *
            ∑ p ∈ (Finset.range t).image f₁,
              |CalibratedCE.Shared.rho f₁ y p b t - p b| *
                (CalibratedCE.Shared.N f₁ p t : ℝ)) / (t : ℝ) := by
        unfold CalibratedCE.Shared.calibScore
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
        exact Finset.sum_congr rfl (fun p _ => by ring)
      rw [e1, e2]
      exact div_le_div_of_nonneg_right h (Nat.cast_nonneg t)
    have hlim1 : Tendsto (fun i => ∑ b, empDist (fun s => R₁ (f₁ s)) y (φ i) a b *
        (u₁ a' b - u₁ a b)) atTop (𝓝 (∑ b, D a b * (u₁ a' b - u₁ a b))) :=
      tendsto_finsetSum _ (fun b _ => (hD a b).mul_const _)
    have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
    have hlim2 : Tendsto (fun i => ∑ b, |u₁ a' b - u₁ a b| *
        CalibratedCE.Shared.calibScore f₁ y b (φ i)) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset (Fin n))
        (fun b _ => ((hcal b).comp hφt).const_mul |u₁ a' b - u₁ a b|)
      simpa [Function.comp_def] using this
    exact le_of_tendsto_of_tendsto' hlim1 hlim2 (fun i => hineq (φ i))
  have hnn : ∀ b, 0 ≤ D a b := fun b =>
    ge_of_tendsto' (hD a b) (fun i => by unfold empDist; positivity)
  simp only [Mb, IsDist, Set.mem_ofPred_eq]
  refine ⟨⟨fun b => div_nonneg (hnn b) ha.le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div]
    exact div_self ha.ne'
  · intro a'
    have hk := key a'
    simp only [mul_sub, Finset.sum_sub_distrib, sub_nonpos] at hk
    have e : ∀ c : Fin m, ∑ b, D a b / (∑ c, D a c) * u₁ c b =
        (∑ b, D a b * u₁ c b) / (∑ c, D a c) := by
      intro c
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [e, e]
    exact div_le_div_of_nonneg_right hk ha.le
