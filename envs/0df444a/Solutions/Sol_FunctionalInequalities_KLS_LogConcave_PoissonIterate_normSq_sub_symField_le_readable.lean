-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_sub_symField_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:44:18.707326+00:00
-- url     : https://prove2.me/submissions/0576951a-cca5-401b-a01b-6e57b141e8de

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Permutation
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_sqrt_normSq_sub_permField_le_of_adjacent_readable

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace Classical
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ν : MeasureTheory.ProbabilityMeasure V} (T : MeasureTheory.Lp ℝ 2 (ν : MeasureTheory.Measure V) →ₗ.[ℝ] MeasureTheory.Lp V 2 (ν : MeasureTheory.Measure V))
omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- `normSq` is nonnegative. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_nonneg {k : ℕ} (u : Field ν k) : 0 ≤ normSq u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
end
end
end

noncomputable section
open MeasureTheory Finset
open FunctionalInequalities.Analysis.Tensor
open scoped Classical
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  {ν : MeasureTheory.ProbabilityMeasure V} {k : ℕ}
/-- `normSq u` is the squared norm of `u` in `PiLp 2`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_eq_norm_toLp_sq (u : Field ν k) :
    normSq u = ‖(WithLp.toLp 2 u :
      PiLp 2 fun _ : Fin k → Fin (Module.finrank ℝ V) => Lp ℝ 2 (ν : Measure V))‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl
/-- The Hilbert–Schmidt norm `√(normSq u)` is the norm of `u` in `PiLp 2`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_eq (u : Field ν k) :
    √(normSq u) = ‖(WithLp.toLp 2 u :
      PiLp 2 fun _ : Fin k → Fin (Module.finrank ℝ V) => Lp ℝ 2 (ν : Measure V))‖ := by
  rw [normSq_eq_norm_toLp_sq, Real.sqrt_sq (norm_nonneg _)]
/-- Homogeneity of the Hilbert–Schmidt norm `√(normSq ·)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_smul (c : ℝ) (u : Field ν k) :
    √(normSq (c • u)) = |c| * √(normSq u) := by
  simp only [sqrt_normSq_eq, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
/-- The triangle inequality for finite sums in the Hilbert–Schmidt norm `√(normSq ·)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_sum_le {ι : Type*} (s : Finset ι) (f : ι → Field ν k) :
    √(normSq (∑ i ∈ s, f i)) ≤ ∑ i ∈ s, √(normSq (f i)) := by
  simp only [sqrt_normSq_eq, WithLp.toLp_sum]
  exact norm_sum_le _ _
/-- Membership in the permutations of the first `p` positions. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.mem_fixingOutside_slots_zero {p : ℕ} {σ : Equiv.Perm (Fin k)} :
    σ ∈ fixingOutside (slots k 0 p) ↔ ∀ x : Fin k, p ≤ x.val → σ x = x := by
  simp only [fixingOutside, slots, mem_filter, mem_univ, true_and, zero_le, not_lt]
/-- The sum `Σ_{ℓ+1<q} ‖u - τ_ℓ u‖²` dominates each of its terms' square roots. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_adjacent_le {q : ℕ} (u : Field ν k) (ℓ : Fin k) (hℓ : ℓ.val + 1 < q) :
    √(normSq (u - permField (Equiv.swap ℓ (finRotate k ℓ)) u)) ≤
      √(∑ m ∈ univ.filter (fun m : Fin k => m.val + 1 < q),
        normSq (u - permField (Equiv.swap m (finRotate k m)) u)) :=
  Real.sqrt_le_sqrt <| single_le_sum (f := fun m : Fin k =>
      normSq (u - permField (Equiv.swap m (finRotate k m)) u))
    (fun _ _ => normSq_nonneg _) (by simp [hℓ])
/-- `u - S_q u` is the average of the displacements `u - π u` over the permutations `π` of the
first `q` positions. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sub_symField_eq (q : ℕ) (u : Field ν k) :
    u - symField q u = ((fixingOutside (slots k 0 q)).card : ℝ)⁻¹ •
      ∑ σ ∈ fixingOutside (slots k 0 q), (u - permField σ u) := by
  have hne : ((fixingOutside (slots k 0 q)).card : ℝ) ≠ 0 := by
    have : (1 : Equiv.Perm (Fin k)) ∈ fixingOutside (slots k 0 q) :=
      mem_fixingOutside_slots_zero.mpr fun _ _ => rfl
    exact_mod_cast (card_pos.mpr ⟨1, this⟩).ne'
  rw [sum_sub_distrib, sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, inv_smul_smul₀ hne]
  rfl
/-- **BKL Lemma 3.3, (44).** For `q ≤ k` and a tensor field `u` with `k` indices,
`‖u - S_q u‖² ≤ q⁴ Σ_{ℓ+1<q} ‖u - τ_ℓ u‖²`, where `S_q` averages over the permutations of the
first `q` index positions and `τ_ℓ` swaps positions `ℓ` and `ℓ + 1`. -/
theorem solution {q : ℕ} (hq : q ≤ k) (u : FunctionalInequalities.KLS.LogConcave.PoissonIterate.Field ν k) :
    FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.symField q u) ≤
      (q : ℝ) ^ 4 * ∑ ℓ ∈ univ.filter (fun ℓ : Fin k => ℓ.val + 1 < q),
        FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField (Equiv.swap ℓ (finRotate k ℓ)) u) := by
  set S := ∑ ℓ ∈ univ.filter (fun ℓ : Fin k => ℓ.val + 1 < q),
    FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField (Equiv.swap ℓ (finRotate k ℓ)) u)
  set G := FunctionalInequalities.Analysis.Tensor.fixingOutside (FunctionalInequalities.Analysis.Tensor.slots k 0 q)
  have hS : 0 ≤ S := sum_nonneg fun _ _ => FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_nonneg _
  have hG : (0 : ℝ) < G.card := by
    have : (1 : Equiv.Perm (Fin k)) ∈ G := FunctionalInequalities.KLS.LogConcave.PoissonIterate.mem_fixingOutside_slots_zero.mpr fun _ _ => rfl
    exact_mod_cast card_pos.mpr ⟨1, this⟩
  have hbound : √(FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.symField q u)) ≤ (q : ℝ) ^ 2 * √S := by
    rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.sub_symField_eq, FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_smul, abs_of_pos (inv_pos.mpr hG)]
    calc (G.card : ℝ)⁻¹ * √(FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (∑ σ ∈ G, (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField σ u)))
        ≤ (G.card : ℝ)⁻¹ * ∑ σ ∈ G, √(FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField σ u)) :=
          mul_le_mul_of_nonneg_left (FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_sum_le _ _) (inv_nonneg.mpr hG.le)
      _ ≤ (G.card : ℝ)⁻¹ * ∑ _σ ∈ G, (q : ℝ) ^ 2 * √S := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun σ hσ => ?_) (inv_nonneg.mpr hG.le)
          exact FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_sub_permField_le_of_adjacent_readable hq u (Real.sqrt_nonneg S)
            (fun ℓ hℓ => FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_adjacent_le u ℓ hℓ) hσ
      _ = (q : ℝ) ^ 2 * √S := by
          rw [sum_const, nsmul_eq_mul, inv_mul_cancel_left₀ hG.ne']
  have h' := pow_le_pow_left₀ (Real.sqrt_nonneg _) hbound 2
  rw [Real.sq_sqrt (FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_nonneg _), mul_pow, Real.sq_sqrt hS, ← pow_mul] at h'
  exact h'
