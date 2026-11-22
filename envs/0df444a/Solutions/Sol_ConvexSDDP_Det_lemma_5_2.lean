-- Prove2me | solution 1 for ConvexSDDP.Det.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T02:57:27.797668+00:00
-- url     : https://prove2.me/submissions/feb4b04e-ddde-4d0a-a2c6-80e110b737f9

import Mathlib

open Filter Topology

/-- `ConvexSDDP.Det.lemma_5_2`: along any compactly supported sequence, the convergence to zero
of the approximation defects `f (xs k) - fk k (xs k)` is equivalent to the convergence to zero of
the lagged defects `f (xs k) - fk (k - κ) (xs k)`. -/
theorem solution {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (hX : IsCompact X)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (fk : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (α : NNReal)
    (hfk : ∀ k, ConvexOn ℝ Set.univ (fk k) ∧ LipschitzWith α (fk k))
    (κ : ℕ) (hmono : ∀ k, κ ≤ k → ∀ y ∈ X, fk (k - κ) y ≤ fk k y)
    (hle : ∀ k, ∀ y ∈ X, fk k y ≤ f y)
    (xs : ℕ → EuclideanSpace ℝ (Fin d)) (hxs : ∀ k, xs k ∈ X) :
    Tendsto (fun k => f (xs k) - fk k (xs k)) atTop (𝓝 0) ↔
      Tendsto (fun k => f (xs k) - fk (k - κ) (xs k)) atTop (𝓝 0) := by
  -- Pointwise: the lagged increments of the monotone (with lag `κ`) bounded family tend to 0.
  have key : ∀ y ∈ X, Tendsto (fun k => fk k y - fk (k - κ) y) atTop (𝓝 0) := by
    intro y hy
    have hmono_y : ∀ k, fk k y ≤ fk (k + κ) y := by
      intro k
      have h := hmono (k + κ) (by omega) y hy
      simpa using h
    let a : ℕ → ℝ := fun k => fk (k + κ) y - fk k y
    have ha_nonneg : ∀ k, 0 ≤ a k := fun k => sub_nonneg.mpr (hmono_y k)
    let P : ℕ → ℝ := fun N => ∑ k ∈ Finset.range N, a k
    -- telescoping bound for the partial sums
    have hstep : ∀ N, (∑ j ∈ Finset.range κ, (fk (N + j) y - fk j y)) + (fk (N + κ) y - fk N y)
        = ∑ j ∈ Finset.range κ, (fk (N + 1 + j) y - fk j y) := by
      intro N
      have e1 : (∑ j ∈ Finset.range κ, fk (N + j) y) + fk (N + κ) y
          = (∑ j ∈ Finset.range κ, fk (N + 1 + j) y) + fk N y := by
        have h1 : (∑ j ∈ Finset.range κ, fk (N + (j + 1)) y)
            = ∑ j ∈ Finset.range κ, fk (N + 1 + j) y := by
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          omega
        rw [← Finset.sum_range_succ (fun j => fk (N + j) y) κ,
          Finset.sum_range_succ' (fun j => fk (N + j) y) κ, h1]
        simp
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      linarith
    have hP_eq : ∀ N, P N = ∑ j ∈ Finset.range κ, (fk (N + j) y - fk j y) := by
      intro N
      induction N with
      | zero =>
        show (∑ k ∈ Finset.range 0, a k) = ∑ j ∈ Finset.range κ, (fk (0 + j) y - fk j y)
        rw [Finset.range_zero, Finset.sum_empty]
        refine (Finset.sum_eq_zero ?_).symm
        intro j _
        simp
      | succ N ih =>
        show (∑ k ∈ Finset.range (N + 1), a k) = ∑ j ∈ Finset.range κ, (fk (N + 1 + j) y - fk j y)
        have ih' : (∑ x ∈ Finset.range N, a x) = ∑ j ∈ Finset.range κ, (fk (N + j) y - fk j y) := ih
        rw [Finset.sum_range_succ, ih']
        have h2 : a N = fk (N + κ) y - fk N y := rfl
        rw [h2]
        exact hstep N
    have hPmono : Monotone P := by
      intro N M hNM
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hNM)
        (fun x _ _ => ha_nonneg x)
    have hPbdd : BddAbove (Set.range P) := by
      refine ⟨∑ j ∈ Finset.range κ, (f y - fk j y), ?_⟩
      rintro _ ⟨N, rfl⟩
      rw [hP_eq N]
      exact Finset.sum_le_sum (fun j _ => by
        have := hle (N + j) y hy
        linarith)
    have hPconv : Tendsto P atTop (𝓝 (⨆ N, P N)) := tendsto_atTop_ciSup hPmono hPbdd
    have hdif : Tendsto (fun N => P (N + 1) - P N) atTop (𝓝 0) := by
      have h := (hPconv.comp (tendsto_add_atTop_nat 1)).sub hPconv
      simpa using h
    have ha : Tendsto a atTop (𝓝 0) :=
      Tendsto.congr (fun N => by simp only [P, a, Finset.sum_range_succ]; ring) hdif
    have hashift : Tendsto (fun k => a (k - κ)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat κ (f := fun k => a (k - κ))).mp (by simpa using ha)
    refine Tendsto.congr' (f₁ := fun k => a (k - κ)) (f₂ := fun k => fk k y - fk (k - κ) y) ?_ hashift
    filter_upwards [eventually_ge_atTop κ] with k hk
    simp only [a]
    rw [Nat.sub_add_cancel hk]
  constructor
  · -- forward direction: `A → 0` gives `B → 0`
    intro hA
    rw [Metric.tendsto_atTop] at hA ⊢
    intro ε hε
    have hε4 : (0:ℝ) < ε / 4 := by linarith
    have hαnn : (0:ℝ) ≤ (α:ℝ) := α.coe_nonneg
    set δ : ℝ := ε / (8 * ((α:ℝ) + 1)) with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; positivity
    have hαδ : (α:ℝ) * δ ≤ ε / 8 := by
      rw [hδdef, mul_div_assoc']
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 8 * ((α:ℝ) + 1))]
      nlinarith
    -- finite δ-net of `X` with centres in `X`
    obtain ⟨t, htcover⟩ := hX.elim_finite_subcover
      (fun i : X => Metric.ball (i : EuclideanSpace ℝ (Fin d)) δ)
      (fun i => Metric.isOpen_ball)
      (fun x hx => by
        refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
        rw [Metric.mem_ball]
        simpa using hδpos)
    have hev : ∀ᶠ k in atTop, ∀ i ∈ t,
        fk k (i : EuclideanSpace ℝ (Fin d)) - fk (k - κ) (i : EuclideanSpace ℝ (Fin d)) < ε / 4 := by
      rw [Finset.eventually_all]
      intro i _
      exact (key (i : EuclideanSpace ℝ (Fin d)) i.2).eventually (eventually_lt_nhds hε4)
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hev
    obtain ⟨N₁, hN₁⟩ := hA (ε / 4) hε4
    refine ⟨max (max N₁ N₂) κ, fun k hk => ?_⟩
    have hkN₁ : N₁ ≤ k := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left (max N₁ N₂) κ)) hk
    have hkN₂ : N₂ ≤ k := le_trans (le_trans (le_max_right N₁ N₂) (le_max_left (max N₁ N₂) κ)) hk
    have hAabs : dist (f (xs k) - fk k (xs k)) 0 < ε / 4 := hN₁ k hkN₁
    have hAnonneg : 0 ≤ f (xs k) - fk k (xs k) := by
      have h := hle k (xs k) (hxs k)
      linarith
    have hAnear : f (xs k) - fk k (xs k) < ε / 4 := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hAnonneg] at hAabs
      exact hAabs
    -- the increment is small, using the net
    have hinc : fk k (xs k) - fk (k - κ) (xs k) < ε / 2 := by
      have hmem : xs k ∈ ⋃ i ∈ t, Metric.ball (i : EuclideanSpace ℝ (Fin d)) δ := htcover (hxs k)
      simp only [Set.mem_iUnion, exists_prop, Metric.mem_ball] at hmem
      obtain ⟨i, hit, hdist⟩ := hmem
      have h1 : fk k (xs k) - fk k (i : EuclideanSpace ℝ (Fin d)) ≤ (α:ℝ) * dist (xs k) (i : EuclideanSpace ℝ (Fin d)) := by
        have h := (hfk k).2.dist_le_mul (xs k) (i : EuclideanSpace ℝ (Fin d))
        rw [Real.dist_eq] at h
        have hle1 : fk k (xs k) - fk k (i : EuclideanSpace ℝ (Fin d))
            ≤ |fk k (xs k) - fk k (i : EuclideanSpace ℝ (Fin d))| := le_abs_self _
        linarith
      have h2 : fk (k - κ) (i : EuclideanSpace ℝ (Fin d)) - fk (k - κ) (xs k)
          ≤ (α:ℝ) * dist (xs k) (i : EuclideanSpace ℝ (Fin d)) := by
        have h := (hfk (k - κ)).2.dist_le_mul (i : EuclideanSpace ℝ (Fin d)) (xs k)
        rw [Real.dist_eq, dist_comm] at h
        have hle2 : fk (k - κ) (i : EuclideanSpace ℝ (Fin d)) - fk (k - κ) (xs k)
            ≤ |fk (k - κ) (i : EuclideanSpace ℝ (Fin d)) - fk (k - κ) (xs k)| := le_abs_self _
        linarith
      have h3 : fk k (i : EuclideanSpace ℝ (Fin d)) - fk (k - κ) (i : EuclideanSpace ℝ (Fin d)) < ε / 4 :=
        hN₂ k hkN₂ i hit
      have h4 : (α:ℝ) * dist (xs k) (i : EuclideanSpace ℝ (Fin d)) ≤ (α:ℝ) * δ :=
        mul_le_mul_of_nonneg_left (le_of_lt hdist) hαnn
      linarith
    have hBnonneg : 0 ≤ f (xs k) - fk (k - κ) (xs k) := by
      have h := hle (k - κ) (xs k) (hxs k)
      linarith
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hBnonneg]
    have hsplit : f (xs k) - fk (k - κ) (xs k)
        = (f (xs k) - fk k (xs k)) + (fk k (xs k) - fk (k - κ) (xs k)) := by ring
    rw [hsplit]
    linarith
  · -- backward direction: squeeze `0 ≤ A ≤ B`
    intro hB
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB ?_ ?_
    · filter_upwards [eventually_ge_atTop κ] with k hk
      have h := hle k (xs k) (hxs k)
      linarith
    · filter_upwards [eventually_ge_atTop κ] with k hk
      have h := hmono k hk (xs k) (hxs k)
      linarith
