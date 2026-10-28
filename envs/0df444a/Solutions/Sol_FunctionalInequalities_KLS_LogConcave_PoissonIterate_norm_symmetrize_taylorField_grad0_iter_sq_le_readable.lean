-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_symmetrize_taylorField_grad0_iter_sq_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:31:15.142089+00:00
-- url     : https://prove2.me/submissions/63d82073-9d02-49c9-86b6-c808a5a337a5

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_TaylorRecursion
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_symmetrize_taylorField_grad0_step_readable

section
noncomputable section
open Finset
section
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
/-- `fixingOutside` is monotone. -/
theorem FunctionalInequalities.Analysis.Tensor.fixingOutside_mono {s t : Finset Ω} (hst : s ⊆ t) : fixingOutside s ⊆ fixingOutside t := by
    intro σ hσ
    have hσ' : ∀ x, x ∉ s → σ x = x := by
      simpa [fixingOutside] using hσ
    have h : ∀ x, x ∉ t → σ x = x := by
      intro x hx
      apply hσ' x
      intro hxs
      exact hx (hst hxs)
    simpa [fixingOutside] using h
end
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
variable {C : NNReal} (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
include hνU hU hexp hC in
/-- **BKL Corollary 3.7** (52) along the iterates: for `d ≥ 1`,
`S_{d+1} T_d(∇₀h_{k+2}) = α_{k+2} T_{d+1}(∇₀h_{k+1})`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_taylorField_grad0_iter_succ (f : Lp ℝ 2 (ν : Measure V)) (k : ℕ) {d : ℕ}
    (hd : 1 ≤ d) (J : Fin (d + 1 + (k + 1)) → Fin (Module.finrank ℝ V)) :
    symmetrize (Module.finrank ℝ V) (d + (k + 2)) (d + 1)
        (taylorField d (grad0 T̄ (iter T̄ f (k + 1)))) (J ∘ Fin.cast (by omega)) =
      scale T̄ (iter T̄ f k) * taylorField (d + 1) (grad0 T̄ (iter T̄ f k)) J :=
  symmetrize_taylorField_grad0_step_readable m hν hi hνU hU hexp hC _ hd J
end HeatModel
end
end

noncomputable section
open MeasureTheory Finset
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ContDiff
section Block
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.one_mem_fixingOutside' (s : Finset Ω) :
    (1 : Equiv.Perm Ω) ∈ fixingOutside s := by
  simp [fixingOutside]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.mul_mem_fixingOutside' {s : Finset Ω} {σ τ : Equiv.Perm Ω}
    (hσ : σ ∈ fixingOutside s) (hτ : τ ∈ fixingOutside s) : σ * τ ∈ fixingOutside s := by
  simp only [fixingOutside, mem_filter, mem_univ, true_and] at hσ hτ ⊢
  intro x hx
  simp [Equiv.Perm.coe_mul, hσ x hx, hτ x hx]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.inv_mem_fixingOutside' {s : Finset Ω} {σ : Equiv.Perm Ω}
    (hσ : σ ∈ fixingOutside s) : σ⁻¹ ∈ fixingOutside s := by
  simp only [fixingOutside, mem_filter, mem_univ, true_and] at hσ ⊢
  intro x hx
  have h := congrArg (fun y => σ⁻¹ y) (hσ x hx)
  simpa using h.symm
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_fixingOutside_mul_right {M : Type*} [AddCommMonoid M] {s : Finset Ω}
    {τ : Equiv.Perm Ω} (hτ : τ ∈ fixingOutside s) (g : Equiv.Perm Ω → M) :
    ∑ σ ∈ fixingOutside s, g (σ * τ) = ∑ σ ∈ fixingOutside s, g σ :=
  sum_nbij' (· * τ) (· * τ⁻¹) (fun _ hσ => mul_mem_fixingOutside' hσ hτ)
    (fun _ hσ => mul_mem_fixingOutside' hσ (inv_mem_fixingOutside' hτ))
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => rfl)
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.card_fixingOutside_pos (s : Finset Ω) : (0 : ℝ) < (fixingOutside s).card := by
  exact_mod_cast card_pos.mpr ⟨1, one_mem_fixingOutside' s⟩
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_blockAverage_le (ρ : Equiv.Perm Ω →* (W ≃ₗᵢ[ℝ] W)) (s : Finset Ω) (v : W) :
    ‖blockAverage ρ s v‖ ≤ ‖v‖ := by
  have hG := card_fixingOutside_pos s
  rw [blockAverage, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hG)]
  calc ((fixingOutside s).card : ℝ)⁻¹ * ‖∑ σ ∈ fixingOutside s, ρ σ v‖
      ≤ ((fixingOutside s).card : ℝ)⁻¹ * ∑ σ ∈ fixingOutside s, ‖ρ σ v‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hG.le)
    _ = ‖v‖ := by
        simp only [LinearIsometryEquiv.norm_map, sum_const, nsmul_eq_mul]
        rw [inv_mul_cancel_left₀ hG.ne']
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.blockAverage_smul (ρ : Equiv.Perm Ω →* (W ≃ₗᵢ[ℝ] W)) (s : Finset Ω) (c : ℝ)
    (v : W) : blockAverage ρ s (c • v) = c • blockAverage ρ s v := by
  simp only [blockAverage, map_smul, ← smul_sum, smul_comm c]
/-- Averaging over a group absorbs the average over a subgroup. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.blockAverage_blockAverage (ρ : Equiv.Perm Ω →* (W ≃ₗᵢ[ℝ] W)) {s t : Finset Ω}
    (hst : s ⊆ t) (v : W) : blockAverage ρ t (blockAverage ρ s v) = blockAverage ρ t v := by
  have hG := card_fixingOutside_pos s
  have hmul : ∀ σ τ : Equiv.Perm Ω, ρ σ (ρ τ v) = ρ (σ * τ) v := fun σ τ => by
    rw [map_mul]
    rfl
  simp only [blockAverage, map_smul, map_sum, hmul]
  congr 1
  rw [← smul_sum, sum_comm]
  have h : ∀ τ ∈ fixingOutside s,
      ∑ σ ∈ fixingOutside t, ρ (σ * τ) v = ∑ σ ∈ fixingOutside t, ρ σ v := fun τ hτ =>
    sum_fixingOutside_mul_right (fixingOutside_mono hst hτ) (fun σ => ρ σ v)
  rw [sum_congr rfl h, sum_const, ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ hG.ne']
end Block
section Coordinates
variable {n N : ℕ}
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.slots_zero_subset {q q' : ℕ} (h : q ≤ q') : slots N 0 q ⊆ slots N 0 q' := by
  intro x hx
  simp only [slots, mem_filter, mem_univ, true_and] at hx ⊢
  omega
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_symmetrize_le (q : ℕ) (A : Coord n N) : ‖symmetrize n N q A‖ ≤ ‖A‖ :=
  norm_blockAverage_le _ _ _
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_smul (q : ℕ) (c : ℝ) (A : Coord n N) :
    symmetrize n N q (c • A) = c • symmetrize n N q A :=
  blockAverage_smul _ _ _ _
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_symmetrize {q q' : ℕ} (h : q ≤ q') (A : Coord n N) :
    symmetrize n N q' (symmetrize n N q A) = symmetrize n N q' A :=
  blockAverage_blockAverage _ (slots_zero_subset h) A
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.recast_rfl (A : Coord n N) : FunctionalInequalities.KLS.LogConcave.PoissonIterate.recast rfl A = A := by
  ext J
  simp [FunctionalInequalities.KLS.LogConcave.PoissonIterate.recast]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_recast {N' : ℕ} (h : N = N') (A : Coord n N) : ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.recast h A‖ = ‖A‖ := by
  subst h
  rw [recast_rfl]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_recast {N' : ℕ} (h : N = N') (q : ℕ) (A : Coord n N) :
    symmetrize n N' q (FunctionalInequalities.KLS.LogConcave.PoissonIterate.recast h A) = FunctionalInequalities.KLS.LogConcave.PoissonIterate.recast h (symmetrize n N q A) := by
  subst h
  rw [recast_rfl, recast_rfl]
end Coordinates
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
  {C : NNReal} (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.contDiff_two' (hUt : U.HasTemperateGrowth) : ContDiff ℝ 2 U :=
  hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)
include hνU hUt hexp hC in
/-- **BKL (56)–(57)**: iterating Corollary 3.7. If `α_{j+2}² ≤ β/C` for `j < k`, `e ≤ k` and
`d ≥ 1`, then `|S_{d+e} T_d(∇₀h_{k+1})|² ≤ (β/C)^e |T_{d+e}(∇₀h_{k+1-e})|²`. -/
theorem solution (f : Lp ℝ 2 (ν : Measure V)) {β : ℝ}
    (e : ℕ) : ∀ (d k : ℕ), 1 ≤ d → e ≤ k → (∀ j < k, FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f j) ^ 2 ≤ β / C) →
      ‖FunctionalInequalities.Analysis.Tensor.symmetrize (Module.finrank ℝ V) (d + (k + 1)) (d + e)
          (FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField d (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k)))‖ ^ 2 ≤
        (β / C) ^ e * ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField (d + e) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f (k - e)))‖ ^ 2 := by
  induction e with
  | zero =>
    intro d k _ _ _
    rw [pow_zero, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_symmetrize_le _ _) 2
  | succ e ih =>
    intro d k hd hk hβ
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [show d + (e + 1) = d + 1 + e by omega, show k + 1 - (e + 1) = k - e by omega]
    have hN : d + (k + 1 + 1) = d + 1 + (k + 1) := by omega
    have hS2 : FunctionalInequalities.KLS.LogConcave.PoissonIterate.recast hN (FunctionalInequalities.Analysis.Tensor.symmetrize (Module.finrank ℝ V) (d + (k + 1 + 1)) (d + 1)
        (FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField d (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f (k + 1))))) =
        FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k) • FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField (d + 1) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k)) := by
      ext J
      simp only [FunctionalInequalities.KLS.LogConcave.PoissonIterate.recast, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
      exact FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_taylorField_grad0_iter_succ m hν hi hνU (FunctionalInequalities.KLS.LogConcave.PoissonIterate.contDiff_two' hUt) hexp hC f k
        hd J
    have hnorm : ‖FunctionalInequalities.Analysis.Tensor.symmetrize (Module.finrank ℝ V) (d + (k + 1 + 1)) (d + 1 + e)
        (FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField d (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f (k + 1))))‖ =
        |FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k)| * ‖FunctionalInequalities.Analysis.Tensor.symmetrize (Module.finrank ℝ V) (d + 1 + (k + 1)) (d + 1 + e)
          (FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField (d + 1) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k)))‖ := by
      rw [← FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_symmetrize (q := d + 1) (by omega), ← FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_recast hN,
        ← FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_recast, hS2, FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_smul, norm_smul, Real.norm_eq_abs]
    have hα := hβ k (by omega)
    have hβC : 0 ≤ β / C := (sq_nonneg _).trans hα
    have ih' := ih (d + 1) k (by omega) (by omega) fun j hj => hβ j (by omega)
    rw [hnorm, mul_pow, sq_abs, pow_succ]
    calc FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k) ^ 2 * ‖FunctionalInequalities.Analysis.Tensor.symmetrize (Module.finrank ℝ V) (d + 1 + (k + 1))
          (d + 1 + e) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField (d + 1) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k)))‖ ^ 2
        ≤ β / C * ((β / C) ^ e *
            ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField (d + 1 + e) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f (k - e)))‖ ^ 2) :=
          mul_le_mul hα ih' (sq_nonneg _) hβC
      _ = _ := by ring
