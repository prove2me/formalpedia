-- Prove2me | solution 1 for FuzzyGames.Values.theorem_8_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T03:16:30.365693+00:00
-- url     : https://prove2.me/submissions/5a88d755-b5ad-42e6-93ca-16a62184d05b

import Mathlib
import Definitions.Def_FuzzyGames_Values_Basic
import Theorems.Thm_FuzzyGames_Values_diag_linear_continuous
import Theorems.Thm_FuzzyGames_Values_diag_axioms
import Theorems.Thm_FuzzyGames_Values_monomials_dense
import Theorems.Thm_FuzzyGames_Values_monomial_value
import Theorems.Thm_FuzzyGames_Values_homogeneous_value

open FuzzyGames.Values

theorem solution :
    (∃ ψ : (n : ℕ) → Vn n →ₗ[ℝ] (Fin n → ℝ), IsSequenceOfFuzzyValues ψ ∧
        ∀ n : ℕ, 0 < n → ∀ v : Vn n, ψ n v = diagValue v.1) ∧
    (∀ ψ : (n : ℕ) → Vn n →ₗ[ℝ] (Fin n → ℝ), IsSequenceOfFuzzyValues ψ →
        ∀ n : ℕ, 0 < n → ∀ v : Vn n, ψ n v = diagValue v.1) ∧
    (∀ (n m : ℕ) (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)), A 1 = 1 →
        ∀ (v : Vn n) (w : Vn m), (∀ σ : Fin m → ℝ, w.1 σ = v.1 (A σ)) →
          ∀ j : Fin m, diagValue w.1 j = ∑ i, A (Pi.single j 1) i * diagValue v.1 i) ∧
    (∀ (n : ℕ) (v : Vn n), ConcaveOn ℝ (Set.Ici 0) v.1 → IsPosHomogeneous v.1 →
        FuzzyGames.TUCore.fuzzyCore v.1 = {diagValue v.1}) := by
  obtain ⟨D, hD, hDc, hD5⟩ := diag_linear_continuous
  obtain ⟨hP, hS, hA⟩ := diag_axioms
  have hDfun : (fun n => ⇑(D n)) = fun n (v : Vn n) => diagValue v.1 := by
    funext n v; exact hD n v
  -- part (i)
  have hDseq : IsSequenceOfFuzzyValues D := by
    refine ⟨fun n _ => hDc n, ?_, ?_, ?_⟩
    · rw [hDfun]; exact hP
    · rw [hDfun]; exact hS
    · rw [hDfun]; exact hA
  -- the C¹ seminorm is nonnegative
  have hsemi : ∀ {n : ℕ} (f : (Fin n → ℝ) → ℝ), 0 ≤ c1seminorm f := by
    intro n f
    unfold c1seminorm
    exact add_nonneg (Real.iSup_nonneg fun _ => abs_nonneg _)
      (Real.iSup_nonneg fun _ => norm_nonneg _)
  -- monomials with `k ≠ 0` lie in `V^n`
  have hmono : ∀ {n : ℕ} (k : Fin n → ℕ), k ≠ 0 → monomial k ∈ Vn n := by
    intro n k hk
    refine ⟨?_, ?_⟩
    · unfold monomial
      exact contDiff_prod fun i _ => (contDiff_apply ℝ ℝ i).pow _
    · obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
        by_contra h; push Not at h; exact hk (funext h)
      unfold monomial
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [zero_pow hi])
  -- part (ii): uniqueness
  have huniq : ∀ ψ : (n : ℕ) → Vn n →ₗ[ℝ] (Fin n → ℝ), IsSequenceOfFuzzyValues ψ →
      ∀ n : ℕ, 0 < n → ∀ v : Vn n, ψ n v = diagValue v.1 := by
    intro ψ hψ n hn v
    obtain ⟨hψc, hψP, hψS, hψA⟩ := hψ
    obtain ⟨C₁, hC₁⟩ := hψc n hn
    obtain ⟨C₂, hC₂⟩ := hDc n
    -- the two maps agree on every monomial
    let mk : (Fin n → ℕ) → Vn n := fun k =>
      if h : k = 0 then 0 else ⟨monomial k, hmono k h⟩
    have hagree : ∀ k : Fin n → ℕ, k ≠ 0 → ψ n (mk k) = D n (mk k) := by
      intro k hk
      have hmk : (mk k).1 = monomial k := by simp [mk, hk]
      funext i
      have h := monomial_value (fun n => ⇑(ψ n)) hψP hψS hψA n k hk (mk k)
        (fun τ => by rw [hmk]) i
      rw [hD n (mk k), h.1, h.2]
    rw [← hD n v]
    set x := ψ n v - D n v with hx
    suffices hx0 : ‖x‖ = 0 by
      have := norm_eq_zero.1 hx0
      exact sub_eq_zero.1 this
    have key : ∀ ε : ℝ, 0 < ε → ‖x‖ ≤ (|C₁| + |C₂|) * ε := by
      intro ε hε
      obtain ⟨K, a, hK0, hKε⟩ := monomials_dense n v ε hε
      let p : Vn n := ∑ k ∈ K, a k • mk k
      have hp : ∀ τ, p.1 τ = ∑ k ∈ K, a k * monomial k τ := by
        intro τ
        simp only [p, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≠ 0 := fun h => hK0 (h ▸ hk)
        simp [mk, hk']
      have hψp : ψ n p = D n p := by
        simp only [p, map_sum, map_smul]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≠ 0 := fun h => hK0 (h ▸ hk)
        rw [hagree k hk']
      have hxeq : x = ψ n (v - p) - D n (v - p) := by
        rw [hx, map_sub, map_sub, hψp]; abel
      have hs : c1seminorm (v - p).1 < ε := by
        have : (v - p).1 = fun τ => v.1 τ - ∑ k ∈ K, a k * monomial k τ := by
          funext τ; simp only [Submodule.coe_sub, Pi.sub_apply, hp]
        rw [this]; exact hKε
      have hs0 := hsemi (v - p).1
      rw [hxeq]
      calc ‖ψ n (v - p) - D n (v - p)‖ ≤ ‖ψ n (v - p)‖ + ‖D n (v - p)‖ := norm_sub_le _ _
        _ ≤ C₁ * c1seminorm (v - p).1 + C₂ * c1seminorm (v - p).1 :=
            add_le_add (hC₁ _) (hC₂ _)
        _ ≤ |C₁| * c1seminorm (v - p).1 + |C₂| * c1seminorm (v - p).1 :=
            add_le_add (mul_le_mul_of_nonneg_right (le_abs_self _) hs0)
              (mul_le_mul_of_nonneg_right (le_abs_self _) hs0)
        _ = (|C₁| + |C₂|) * c1seminorm (v - p).1 := by ring
        _ ≤ (|C₁| + |C₂|) * ε :=
            mul_le_mul_of_nonneg_left hs.le (add_nonneg (abs_nonneg _) (abs_nonneg _))
    by_contra hne
    have hpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    set M := |C₁| + |C₂| with hM
    have hM0 : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
    have := key (‖x‖ / (M + 1)) (div_pos hpos (by linarith))
    have h2 : M * (‖x‖ / (M + 1)) < ‖x‖ := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  refine ⟨⟨D, hDseq, fun n _ v => hD n v⟩, huniq, ?_, ?_⟩
  -- part (iii)
  · intro n m A hA1 v w hw j
    have := hD5 n m A hA1 v w hw j
    rw [hD m w, hD n v] at this
    simpa using this
  -- part (iv)
  · intro n v hconc hhom
    have hdiag := (homogeneous_value n v hhom).2
    rw [hdiag]
    set g : Fin n → ℝ := fun i => fderiv ℝ v.1 1 (Pi.single i 1) with hg
    have hdiff : Differentiable ℝ v.1 := v.2.1.differentiable (by norm_num)
    -- linear functionals on `ℝ^n` in coordinates
    have hlin : ∀ (L : (Fin n → ℝ) →L[ℝ] ℝ) (x : Fin n → ℝ),
        L x = ∑ i, x i * L (Pi.single i 1) := by
      intro L x
      have := L.toLinearMap.pi_apply_eq_sum_univ x
      refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
      rw [smul_eq_mul]
      have hs : (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
        funext j; simp [Pi.single_apply, eq_comm]
      rw [hs]; rfl
    -- Euler's identity
    have heuler : fderiv ℝ v.1 1 1 = v.1 1 := by
      have h1 : HasDerivAt (fun t : ℝ => v.1 (t • (1 : Fin n → ℝ))) (fderiv ℝ v.1 1 1) 1 := by
        have hid : HasDerivAt (fun t : ℝ => t • (1 : Fin n → ℝ)) (1 : Fin n → ℝ) 1 := by
          simpa using (hasDerivAt_id (1 : ℝ)).smul_const (1 : Fin n → ℝ)
        have hv : HasFDerivAt v.1 (fderiv ℝ v.1 1) ((1 : ℝ) • (1 : Fin n → ℝ)) := by
          rw [one_smul]; exact (hdiff 1).hasFDerivAt
        exact hv.comp_hasDerivAt (1 : ℝ) hid
      have h2 : HasDerivAt (fun t : ℝ => v.1 (t • (1 : Fin n → ℝ))) (v.1 1) 1 := by
        have h3 : HasDerivAt (fun t : ℝ => t * v.1 1) (v.1 1) 1 := by
          simpa using (hasDerivAt_id (1 : ℝ)).mul_const (v.1 1)
        refine h3.congr_of_eventuallyEq ?_
        filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
        exact hhom t ht 1 (by intro i; simp)
      exact h1.unique h2
    have hsum : ∑ i, g i = v.1 1 := by
      rw [← heuler, hlin (fderiv ℝ v.1 1) 1]; simp [g]
    have hcoal : FuzzyGames.NTUCore.coal (Finset.univ : Finset (Fin n)) = 1 := by
      funext i; simp [FuzzyGames.NTUCore.coal]
    ext c
    simp only [FuzzyGames.TUCore.fuzzyCore, Set.mem_setOf_eq, Set.mem_singleton_iff, hcoal]
    constructor
    · -- a core element is the gradient at `τ^N`
      rintro ⟨hc1, hc2⟩
      -- the core inequality extends to the orthant by homogeneity
      have hext : ∀ τ : Fin n → ℝ, 0 ≤ τ → v.1 τ ≤ ∑ i, τ i * c i := by
        intro τ hτ
        set t : ℝ := 1 + ∑ i, τ i with ht
        have hsum0 : 0 ≤ ∑ i, τ i := Finset.sum_nonneg fun i _ => hτ i
        have htpos : 0 < t := by linarith
        have hcube : t⁻¹ • τ ∈ FuzzyGames.NTUCore.cube n := by
          constructor
          · intro i; simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
            exact mul_nonneg (inv_nonneg.2 htpos.le) (hτ i)
          · intro i; simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply]
            rw [inv_mul_le_iff₀ htpos, mul_one]
            have : τ i ≤ ∑ j, τ j :=
              Finset.single_le_sum (fun j _ => hτ j) (Finset.mem_univ i)
            linarith
        have h1 := hc2 _ hcube
        have h2 : v.1 τ = t * v.1 (t⁻¹ • τ) := by
          rw [← hhom t htpos _ (fun i => by
            simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
            exact mul_nonneg (inv_nonneg.2 htpos.le) (hτ i)), smul_smul,
            mul_inv_cancel₀ htpos.ne', one_smul]
        rw [h2]
        have h3 : ∑ i, (t⁻¹ • τ) i * c i = t⁻¹ * ∑ i, τ i * c i := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Pi.smul_apply, smul_eq_mul]; ring
        rw [h3] at h1
        calc t * v.1 (t⁻¹ • τ) ≤ t * (t⁻¹ * ∑ i, τ i * c i) :=
              mul_le_mul_of_nonneg_left h1 htpos.le
          _ = ∑ i, τ i * c i := by rw [← mul_assoc, mul_inv_cancel₀ htpos.ne', one_mul]
      -- so `τ ↦ ∑ τ_i c_i - v τ` has a local minimum at `τ^N`
      let L : (Fin n → ℝ) →L[ℝ] ℝ :=
        ∑ i, c i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i
      have hL : ∀ τ, L τ = ∑ i, τ i * c i := by
        intro τ; simp [L, mul_comm]
      have hmin : IsLocalMin (fun τ => L τ - v.1 τ) 1 := by
        have hnhds : ∀ᶠ τ in nhds (1 : Fin n → ℝ), ∀ i, 0 < τ i :=
          Filter.eventually_all.2 fun i =>
            (continuous_apply i).continuousAt.eventually (lt_mem_nhds (by simp))
        filter_upwards [hnhds] with τ hτ
        have h1 := hext τ (fun i => (hτ i).le)
        have h2 : L 1 - v.1 1 = 0 := by rw [hL]; simp [hc1]
        show L 1 - v.1 1 ≤ L τ - v.1 τ
        rw [h2, hL]; linarith
      have hfd : HasFDerivAt (fun τ => L τ - v.1 τ) (L - fderiv ℝ v.1 1) 1 :=
        L.hasFDerivAt.sub (hdiff 1).hasFDerivAt
      have hzero := hmin.hasFDerivAt_eq_zero hfd
      funext i
      have := congrArg (fun F => F (Pi.single i 1)) hzero
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply] at this
      rw [hL] at this
      have hci : ∑ j, (Pi.single i (1 : ℝ) : Fin n → ℝ) j * c j = c i := by
        simp [Pi.single_apply]
      rw [hci] at this
      simp only [g]; linarith
    · -- the gradient lies in the core
      rintro rfl
      refine ⟨hsum, fun τ hτ => ?_⟩
      have hτ0 : (0 : Fin n → ℝ) ≤ τ := hτ.1
      -- the restriction of `v` to the segment from `τ^N` to `τ`
      let h : ℝ → ℝ := fun s => v.1 (1 + s • (τ - 1))
      have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, (0 : Fin n → ℝ) ≤ 1 + s • (τ - 1) := by
        intro s hs i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul,
          Pi.zero_apply]
        have := hτ0 i
        simp only [Pi.zero_apply] at this
        nlinarith [hs.1, hs.2]
      have hhc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) h := by
        refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
        have := hconc.2 (hseg x hx) (hseg y hy) ha hb hab
        simp only [h]
        have heq : a • (1 + x • (τ - 1)) + b • (1 + y • (τ - 1)) =
            1 + (a • x + b • y) • (τ - 1) := by
          rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, hab,
            one_smul, smul_eq_mul, smul_eq_mul, add_smul]
        rw [heq] at this
        exact this
      have hhd : HasDerivAt h (fderiv ℝ v.1 1 (τ - 1)) 0 := by
        have hid : HasDerivAt (fun s : ℝ => (1 : Fin n → ℝ) + s • (τ - 1)) (τ - 1) 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (τ - 1)).const_add 1
        have hv : HasFDerivAt v.1 (fderiv ℝ v.1 1) ((1 : Fin n → ℝ) + (0 : ℝ) • (τ - 1)) := by
          rw [zero_smul, add_zero]; exact (hdiff 1).hasFDerivAt
        exact hv.comp_hasDerivAt (0 : ℝ) hid
      have hsl := hhc.slope_le_of_hasDerivAt (x := 0) (y := 1) (by simp) (by simp)
        (by norm_num) hhd
      rw [slope_def_field] at hsl
      simp only [h, zero_smul, add_zero, one_smul, add_sub_cancel, sub_zero, div_one] at hsl
      rw [map_sub, hlin (fderiv ℝ v.1 1) τ, heuler] at hsl
      have : ∑ i, τ i * g i = ∑ i, τ i * fderiv ℝ v.1 1 (Pi.single i 1) := rfl
      linarith
