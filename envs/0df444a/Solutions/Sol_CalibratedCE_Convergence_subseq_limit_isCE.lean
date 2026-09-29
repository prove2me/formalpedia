-- Prove2me | solution 1 for CalibratedCE.Convergence.subseq_limit_isCE
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:41:19.158826+00:00
-- url     : https://prove2.me/submissions/b6dc39d3-e708-4754-af76-d9418f6f03c8

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_BestReply
import Definitions.Def_CalibratedCE_Convergence_EmpDist

open Filter Topology

namespace CalibratedCE.Convergence

theorem aux_slce_rhoN {k : ℕ} (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k) (p : Fin k → ℝ) (j : Fin k)
    (t : ℕ) :
    Shared.rho f z p j t * (Shared.N f p t : ℝ) =
      (((Finset.range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ) := by
  unfold Shared.rho
  split_ifs with h
  · have h0 : ((Finset.range t).filter (fun s => f s = p ∧ z s = j)).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      calc ((Finset.range t).filter (fun s => f s = p ∧ z s = j)).card
          ≤ Shared.N f p t := by
            unfold Shared.N
            apply Finset.card_le_card
            intro s hs
            simp only [Finset.mem_filter] at hs ⊢
            exact ⟨hs.1, hs.2.1⟩
        _ = 0 := h
    simp [h0]
  · have : (Shared.N f p t : ℝ) ≠ 0 := by exact_mod_cast h
    field_simp

theorem aux_slce_calib {k : ℕ} (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k) (j : Fin k) (t : ℕ) :
    Shared.calibScore f z j t = ∑ p ∈ (Finset.range t).image f,
      |(((Finset.range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ)
        - p j * (Shared.N f p t : ℝ)| / (t : ℝ) := by
  unfold Shared.calibScore
  apply Finset.sum_congr rfl
  intro p _
  rw [← aux_slce_rhoN f z p j t, ← sub_mul, abs_mul, Nat.abs_cast]

theorem aux_slce_cntA {k l : ℕ} (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k)
    (c : (Fin k → ℝ) → Fin l) (a : Fin l) (j : Fin k) (t : ℕ) :
    (((Finset.range t).filter (fun s => c (f s) = a ∧ z s = j)).card : ℝ)
      = ∑ p ∈ (Finset.range t).image f,
          if c p = a then (((Finset.range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ)
          else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := (Finset.range t).image f)]
  · push_cast
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.filter_filter]
    split_ifs with hp
    · congr 2
      apply Finset.filter_congr
      intro s _
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩; exact ⟨⟨h3 ▸ hp, h2⟩, h3⟩
    · rw [Finset.card_eq_zero.mpr]
      · simp
      · rw [Finset.filter_eq_empty_iff]
        rintro s _ ⟨⟨h1, _⟩, h3⟩
        exact hp (h3 ▸ h1)
  · intro s hs
    exact Finset.mem_image_of_mem f (Finset.mem_filter.mp hs).1

theorem aux_slce_main {k l : ℕ} (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k)
    (c : (Fin k → ℝ) → Fin l)
    (a : Fin l) (v : Fin k → ℝ) (hv : ∀ s, c (f s) = a → ∑ j, f s j * v j ≤ 0) (t : ℕ) :
    ∑ j, (((Finset.range t).filter (fun s => c (f s) = a ∧ z s = j)).card : ℝ) / (t : ℝ) * v j
      ≤ ∑ j, |v j| * Shared.calibScore f z j t := by
  have key : ∑ j, (((Finset.range t).filter (fun s => c (f s) = a ∧ z s = j)).card : ℝ) * v j
      ≤ ∑ j, |v j| * ∑ p ∈ (Finset.range t).image f,
        |(((Finset.range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ)
          - p j * (Shared.N f p t : ℝ)| := by
    simp_rw [aux_slce_cntA f z c a _ t, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
    apply Finset.sum_le_sum
    intro p hp
    split_ifs with hcp
    · obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hp
      have h1 := hv s hcp
      have hN : (0 : ℝ) ≤ (Shared.N f (f s) t : ℝ) := Nat.cast_nonneg _
      have hsplit : ∑ j, (((Finset.range t).filter (fun s' => f s' = f s ∧ z s' = j)).card : ℝ)
            * v j
          = ∑ j, ((((Finset.range t).filter (fun s' => f s' = f s ∧ z s' = j)).card : ℝ)
              - f s j * (Shared.N f (f s) t : ℝ)) * v j
            + (Shared.N f (f s) t : ℝ) * ∑ j, f s j * v j := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hsplit]
      have h2 : (Shared.N f (f s) t : ℝ) * ∑ j, f s j * v j ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hN h1
      have h3 : ∑ j, ((((Finset.range t).filter (fun s' => f s' = f s ∧ z s' = j)).card : ℝ)
              - f s j * (Shared.N f (f s) t : ℝ)) * v j
          ≤ ∑ j, |v j| * |(((Finset.range t).filter (fun s' => f s' = f s ∧ z s' = j)).card : ℝ)
              - f s j * (Shared.N f (f s) t : ℝ)| := by
        apply Finset.sum_le_sum
        intro j _
        rw [mul_comm (|v j|), ← abs_mul]
        exact le_abs_self _
      linarith
    · simp only [zero_mul, Finset.sum_const_zero]
      apply Finset.sum_nonneg
      intro j _
      positivity
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
  have lhs_eq : ∑ j, (((Finset.range t).filter (fun s => c (f s) = a ∧ z s = j)).card : ℝ)
      / (t : ℝ) * v j
      = (∑ j, (((Finset.range t).filter (fun s => c (f s) = a ∧ z s = j)).card : ℝ) * v j)
        / (t : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have rhs_eq : ∑ j, |v j| * Shared.calibScore f z j t
      = (∑ j, |v j| * ∑ p ∈ (Finset.range t).image f,
        |(((Finset.range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ)
          - p j * (Shared.N f p t : ℝ)|) / (t : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [aux_slce_calib, mul_div_assoc, Finset.sum_div]
  rw [lhs_eq, rhs_eq]
  exact div_le_div_of_nonneg_right key ht

theorem aux_slce_sum_one {m n : ℕ} (x : ℕ → Fin m) (y : ℕ → Fin n) (t : ℕ) :
    ∑ a, ∑ b, (((Finset.range t).filter (fun s => x s = a ∧ y s = b)).card : ℝ) = (t : ℝ) := by
  have h : ∀ a, ∑ b, (((Finset.range t).filter (fun s => x s = a ∧ y s = b)).card : ℝ)
      = (((Finset.range t).filter (fun s => x s = a)).card : ℝ) := by
    intro a
    rw [Finset.card_eq_sum_card_fiberwise (f := y) (t := Finset.univ)
      (s := (Finset.range t).filter (fun s => x s = a)) (fun _ _ => Finset.mem_univ _)]
    push_cast
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.filter_filter]
  simp_rw [h]
  rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _),
    Finset.card_range]

end CalibratedCE.Convergence

open CalibratedCE.Convergence

open Filter Topology

theorem solution {m n : ℕ}
    (u₁ u₂ : Fin m → Fin n → ℝ)
    (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (hR₁ : IsBestReply₁ u₁ R₁) (hR₂ : IsBestReply₂ u₂ R₂)
    (f₁ : ℕ → Fin n → ℝ) (f₂ : ℕ → Fin m → ℝ)
    (hf₁ : ∀ t, IsDist (f₁ t)) (hf₂ : ∀ t, IsDist (f₂ t))
    (hcal₁ : CalibratedCE.Shared.Calibrated f₁ (fun s => R₂ (f₂ s)))
    (hcal₂ : CalibratedCE.Shared.Calibrated f₂ (fun s => R₁ (f₁ s)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (D : Fin m → Fin n → ℝ)
    (hD : ∀ a b, Tendsto (fun i => empDist (fun s => R₁ (f₁ s)) (fun s => R₂ (f₂ s)) (φ i) a b)
      atTop (𝓝 (D a b))) :
    IsCE u₁ u₂ D := by
  set x : ℕ → Fin m := fun s => R₁ (f₁ s) with hx
  set y : ℕ → Fin n := fun s => R₂ (f₂ s) with hy
  -- player 1 inequality
  have h1 : ∀ a a' : Fin m, ∑ b, D a b * (u₁ a' b - u₁ a b) ≤ 0 := by
    intro a a'
    set v : Fin n → ℝ := fun b => u₁ a' b - u₁ a b with hv_def
    have hv : ∀ s, R₁ (f₁ s) = a → ∑ j, f₁ s j * v j ≤ 0 := by
      intro s hs
      have := hR₁ (f₁ s) (hf₁ s) a'
      rw [hs] at this
      simp only [v, mul_sub, Finset.sum_sub_distrib]
      linarith
    have hlim : Tendsto (fun i => ∑ b, empDist x y (φ i) a b * v b) atTop
        (𝓝 (∑ b, D a b * v b)) :=
      tendsto_finsetSum _ (fun b _ => (hD a b).mul_const _)
    have hlim2 : Tendsto (fun i => ∑ b, |v b| * CalibratedCE.Shared.calibScore f₁ y b (φ i))
        atTop (𝓝 0) := by
      have : Tendsto (fun i => ∑ b, |v b| * CalibratedCE.Shared.calibScore f₁ y b (φ i))
          atTop (𝓝 (∑ b : Fin n, |v b| * 0)) :=
        tendsto_finsetSum _ (fun b _ => ((hcal₁ b).comp hφ.tendsto_atTop).const_mul _)
      simpa using this
    have hle : ∀ i, ∑ b, empDist x y (φ i) a b * v b
        ≤ ∑ b, |v b| * CalibratedCE.Shared.calibScore f₁ y b (φ i) := by
      intro i
      exact aux_slce_main f₁ y R₁ a v hv (φ i)
    exact le_of_tendsto_of_tendsto' hlim hlim2 hle
  -- player 2 inequality
  have h2 : ∀ b b' : Fin n, ∑ a, D a b * (u₂ a b' - u₂ a b) ≤ 0 := by
    intro b b'
    set v : Fin m → ℝ := fun a => u₂ a b' - u₂ a b with hv_def
    have hv : ∀ s, R₂ (f₂ s) = b → ∑ j, f₂ s j * v j ≤ 0 := by
      intro s hs
      have := hR₂ (f₂ s) (hf₂ s) b'
      rw [hs] at this
      simp only [v, mul_sub, Finset.sum_sub_distrib]
      linarith
    have hlim : Tendsto (fun i => ∑ a, empDist x y (φ i) a b * v a) atTop
        (𝓝 (∑ a, D a b * v a)) :=
      tendsto_finsetSum _ (fun a _ => (hD a b).mul_const _)
    have hlim2 : Tendsto (fun i => ∑ a, |v a| * CalibratedCE.Shared.calibScore f₂ x a (φ i))
        atTop (𝓝 0) := by
      have : Tendsto (fun i => ∑ a, |v a| * CalibratedCE.Shared.calibScore f₂ x a (φ i))
          atTop (𝓝 (∑ a : Fin m, |v a| * 0)) :=
        tendsto_finsetSum _ (fun a _ => ((hcal₂ a).comp hφ.tendsto_atTop).const_mul _)
      simpa using this
    have hle : ∀ i, ∑ a, empDist x y (φ i) a b * v a
        ≤ ∑ a, |v a| * CalibratedCE.Shared.calibScore f₂ x a (φ i) := by
      intro i
      have := aux_slce_main f₂ x R₂ b v hv (φ i)
      convert this using 3 with a _
      unfold empDist
      congr 3
      apply Finset.filter_congr
      intro s _
      exact And.comm
    exact le_of_tendsto_of_tendsto' hlim hlim2 hle
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro a b
    exact ge_of_tendsto' (hD a b) (fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · have hlim : Tendsto (fun i => ∑ a, ∑ b, empDist x y (φ i) a b) atTop
        (𝓝 (∑ a, ∑ b, D a b)) :=
      tendsto_finsetSum _ (fun a _ => tendsto_finsetSum _ (fun b _ => hD a b))
    have hev : (fun i => ∑ a, ∑ b, empDist x y (φ i) a b) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with i hi
      have hpos : (0 : ℝ) < (φ i : ℝ) := by
        have : 1 ≤ φ i := le_trans hi (hφ.id_le i)
        exact_mod_cast this
      unfold empDist
      simp_rw [← Finset.sum_div]
      rw [aux_slce_sum_one x y (φ i)]
      exact div_self hpos.ne'
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)
  · intro Φ
    have : ∑ a, ∑ b, D a b * u₁ (Φ a) b - ∑ a, ∑ b, D a b * u₁ a b
        = ∑ a, ∑ b, D a b * (u₁ (Φ a) b - u₁ a b) := by
      simp [mul_sub, Finset.sum_sub_distrib]
    have h' : ∑ a, ∑ b, D a b * (u₁ (Φ a) b - u₁ a b) ≤ 0 :=
      Finset.sum_nonpos (fun a _ => h1 a (Φ a))
    linarith
  · intro Φ
    have : ∑ a, ∑ b, D a b * u₂ a (Φ b) - ∑ a, ∑ b, D a b * u₂ a b
        = ∑ b, ∑ a, D a b * (u₂ a (Φ b) - u₂ a b) := by
      have hc : ∑ b, ∑ a, D a b * (u₂ a (Φ b) - u₂ a b)
          = ∑ a, ∑ b, D a b * (u₂ a (Φ b) - u₂ a b) := Finset.sum_comm
      rw [hc]
      simp [mul_sub, Finset.sum_sub_distrib]
    have h' : ∑ b, ∑ a, D a b * (u₂ a (Φ b) - u₂ a b) ≤ 0 :=
      Finset.sum_nonpos (fun b _ => h2 b (Φ b))
    linarith
