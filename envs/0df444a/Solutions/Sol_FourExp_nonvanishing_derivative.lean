-- Prove2me | solution 1 for FourExp.nonvanishing_derivative
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-14T19:31:33.743203+00:00
-- url     : https://prove2.me/submissions/4215fb5b-ac2b-49d1-857d-043b255cc1a7

import Mathlib
import Theorems.Thm_FourExp_expPoly_zero_count
import Theorems.Thm_FourExp_expPoly_ne_zero

open Finset

theorem solution
    (x₁ x₂ y₁ y₂ : ℂ) (hx : LinearIndependent ℚ ![x₁, x₂]) (hy : LinearIndependent ℚ ![y₁, y₂])
    (S T R₁ R₂ S' : ℕ) (c : Fin S → Fin T → Fin T → ℂ) (hc : ∃ i j k, c i j k ≠ 0)
    (lam : ℝ) (hlam : 0 < lam)
    (hcount : (((S * T * T : ℕ) : ℝ) / lam
              + 2 * (1 + ((S * T * T : ℕ) : ℝ) ^ lam) / (lam * Real.log ((S * T * T : ℕ) : ℝ))
                * (1 + ((R₁ : ℝ) * ‖y₁‖ + (R₂ : ℝ) * ‖y₂‖) * ((T : ℝ) * (‖x₁‖ + ‖x₂‖)))
            ≤ ((R₁ * R₂ * S' : ℕ) : ℝ))) :
    ∃ a b s : ℕ, a < R₁ ∧ b < R₂ ∧ s < S' ∧
      iteratedDeriv s (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              c i j k * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
        ((a : ℂ) * y₁ + (b : ℂ) * y₂) ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨i₀, j₀, k₀, hc₀⟩ := hc
  have hT : 0 < T := j₀.pos
  have hS : 0 < S := i₀.pos
  set G : ℂ → ℂ := (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
      c i j k * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z)) with hGdef
  -- index the frequencies by `Fin (T * T)`
  let e : Fin T × Fin T ≃ Fin (T * T) := finProdFinEquiv
  let ω : Fin (T * T) → ℂ := fun m =>
    (((e.symm m).1 : ℕ) : ℂ) * x₁ + (((e.symm m).2 : ℕ) : ℂ) * x₂
  let q : Fin (T * T) → ℕ := fun _ => S
  let b : (m : Fin (T * T)) → Fin (q m) → ℂ := fun m i => c i (e.symm m).1 (e.symm m).2
  have hG : ∀ w, G w = ∑ m, ∑ i : Fin (q m), b m i * w ^ (i : ℕ) * Complex.exp (ω m * w) := by
    intro w
    rw [← e.sum_comp]
    simp only [q, b, ω, Equiv.symm_apply_apply, Fintype.sum_prod_type, hGdef]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_comm]
  -- the frequencies are distinct
  have hω : Function.Injective ω := by
    intro m m' h
    apply e.symm.injective
    have h' := (LinearIndependent.pair_iff.mp hx)
      ((((e.symm m).1 : ℕ) : ℚ) - (((e.symm m').1 : ℕ) : ℚ))
      ((((e.symm m).2 : ℕ) : ℚ) - (((e.symm m').2 : ℕ) : ℚ))
      (by simp only [ω] at h; rw [Rat.smul_def, Rat.smul_def]; push_cast; linear_combination h)
    obtain ⟨h1, h2⟩ := h'
    have e1 : (((e.symm m).1 : ℕ)) = (((e.symm m').1 : ℕ)) := by exact_mod_cast sub_eq_zero.mp h1
    have e2 : (((e.symm m).2 : ℕ)) = (((e.symm m').2 : ℕ)) := by exact_mod_cast sub_eq_zero.mp h2
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  have hb : ∃ m i, b m i ≠ 0 := ⟨e (j₀, k₀), i₀, by simpa [b] using hc₀⟩
  -- `G` is entire and not identically zero
  have hdiff : Differentiable ℂ G := by
    rw [hGdef]; fun_prop
  obtain ⟨w, hw⟩ := FourExp.expPoly_ne_zero q ω hω b hb
  have hw' : G w ≠ 0 := by rw [hG w]; exact hw
  have hfin : ∀ z, analyticOrderAt G z ≠ ⊤ := by
    intro z htop
    have hev : G =ᶠ[nhds z] 0 := by
      filter_upwards [analyticOrderAt_eq_top.mp htop] with u hu
      simpa using hu
    have := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun u _ => hdiff.analyticAt u) isPreconnected_univ (Set.mem_univ z) hev
    exact hw' (by simpa using this (Set.mem_univ w))
  -- every grid point is a zero of order at least `S'`
  have hord : ∀ a < R₁, ∀ b' < R₂,
      S' ≤ analyticOrderNatAt G ((a : ℂ) * y₁ + (b' : ℂ) * y₂) := by
    intro a ha b' hb'
    have h1 : (S' : ℕ∞) ≤ analyticOrderAt G ((a : ℂ) * y₁ + (b' : ℂ) * y₂) :=
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hdiff.analyticAt _)).2
        (fun i hi => hcon a b' i ha hb' hi)
    have hne := hfin ((a : ℂ) * y₁ + (b' : ℂ) * y₂)
    rw [← ENat.coe_toNat hne] at h1
    exact_mod_cast h1
  -- the grid has `R₁ * R₂` distinct points
  let grid : Finset ℂ :=
    (Finset.range R₁ ×ˢ Finset.range R₂).image (fun p : ℕ × ℕ => (p.1 : ℂ) * y₁ + (p.2 : ℂ) * y₂)
  have hinj : Set.InjOn (fun p : ℕ × ℕ => (p.1 : ℂ) * y₁ + (p.2 : ℂ) * y₂)
      ↑(Finset.range R₁ ×ˢ Finset.range R₂) := by
    intro p _ p' _ h
    obtain ⟨h1, h2⟩ := (LinearIndependent.pair_iff.mp hy) ((p.1 : ℚ) - p'.1) ((p.2 : ℚ) - p'.2)
      (by simp only at h; rw [Rat.smul_def, Rat.smul_def]; push_cast; linear_combination h)
    exact Prod.ext (by exact_mod_cast sub_eq_zero.mp h1) (by exact_mod_cast sub_eq_zero.mp h2)
  have hcard : grid.card = R₁ * R₂ := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range, Finset.card_range]
  have hlow : (((R₁ * R₂ * S' : ℕ)) : ℝ) ≤ ∑ z ∈ grid, (analyticOrderNatAt G z : ℝ) := by
    calc (((R₁ * R₂ * S' : ℕ)) : ℝ) = ∑ z ∈ grid, (S' : ℝ) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring
      _ ≤ ∑ z ∈ grid, (analyticOrderNatAt G z : ℝ) := by
          apply Finset.sum_le_sum
          intro z hz
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
          simp only [Finset.mem_product, Finset.mem_range] at hp
          exact_mod_cast hord p.1 hp.1 p.2 hp.2
  -- the zero estimate
  set ρ : ℝ := (R₁ : ℝ) * ‖y₁‖ + (R₂ : ℝ) * ‖y₂‖ with hρdef
  have hρ : 0 ≤ ρ := by positivity
  have hdisc : ∀ z ∈ grid, ‖z - 0‖ ≤ ρ := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    simp only [Finset.mem_product, Finset.mem_range] at hp
    have ha : (p.1 : ℝ) ≤ R₁ := by exact_mod_cast hp.1.le
    have hb' : (p.2 : ℝ) ≤ R₂ := by exact_mod_cast hp.2.le
    calc ‖(p.1 : ℂ) * y₁ + (p.2 : ℂ) * y₂ - 0‖ ≤ ‖(p.1 : ℂ) * y₁‖ + ‖(p.2 : ℂ) * y₂‖ := by
          rw [sub_zero]; exact norm_add_le _ _
      _ = (p.1 : ℝ) * ‖y₁‖ + (p.2 : ℝ) * ‖y₂‖ := by simp [norm_mul]
      _ ≤ ρ := by rw [hρdef]; gcongr
  have hB := FourExp.expPoly_zero_count q ω hω b hb 0 ρ hρ lam hlam grid hdisc
  have hn : (∑ m, q m : ℕ) = S * T * T := by
    simp only [q, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
  have hsum : ∑ z ∈ grid, (analyticOrderNatAt
      (fun w : ℂ => ∑ m, ∑ i : Fin (q m), b m i * w ^ (i : ℕ) * Complex.exp (ω m * w)) z : ℝ)
      = ∑ z ∈ grid, (analyticOrderNatAt G z : ℝ) := by
    have : (fun w : ℂ => ∑ m, ∑ i : Fin (q m), b m i * w ^ (i : ℕ) * Complex.exp (ω m * w)) = G :=
      funext (fun w => (hG w).symm)
    rw [this]
  rw [hsum, hn] at hB
  have hΩ : (⨆ m, ‖ω m‖) ≤ (T : ℝ) * (‖x₁‖ + ‖x₂‖) := by
    haveI : Nonempty (Fin (T * T)) := ⟨⟨0, Nat.mul_pos hT hT⟩⟩
    apply ciSup_le
    intro m
    have hj : (((e.symm m).1 : ℕ) : ℝ) ≤ T := by exact_mod_cast (e.symm m).1.is_lt.le
    have hk : (((e.symm m).2 : ℕ) : ℝ) ≤ T := by exact_mod_cast (e.symm m).2.is_lt.le
    calc ‖ω m‖ ≤ ‖(((e.symm m).1 : ℕ) : ℂ) * x₁‖ + ‖(((e.symm m).2 : ℕ) : ℂ) * x₂‖ :=
          norm_add_le _ _
      _ = (((e.symm m).1 : ℕ) : ℝ) * ‖x₁‖ + (((e.symm m).2 : ℕ) : ℝ) * ‖x₂‖ := by simp [norm_mul]
      _ ≤ (T : ℝ) * ‖x₁‖ + (T : ℝ) * ‖x₂‖ := by gcongr
      _ = (T : ℝ) * (‖x₁‖ + ‖x₂‖) := by ring
  have hn1 : (1 : ℝ) ≤ ((S * T * T : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hK : 0 ≤ 2 * (1 + ((S * T * T : ℕ) : ℝ) ^ lam) / (lam * Real.log ((S * T * T : ℕ) : ℝ)) :=
    div_nonneg (by positivity) (mul_nonneg hlam.le (Real.log_nonneg hn1))
  have hmono : 2 * (1 + ((S * T * T : ℕ) : ℝ) ^ lam) / (lam * Real.log ((S * T * T : ℕ) : ℝ))
        * (1 + ρ * ⨆ m, ‖ω m‖)
      ≤ 2 * (1 + ((S * T * T : ℕ) : ℝ) ^ lam) / (lam * Real.log ((S * T * T : ℕ) : ℝ))
        * (1 + ρ * ((T : ℝ) * (‖x₁‖ + ‖x₂‖))) :=
    mul_le_mul_of_nonneg_left (by gcongr) hK
  linarith
