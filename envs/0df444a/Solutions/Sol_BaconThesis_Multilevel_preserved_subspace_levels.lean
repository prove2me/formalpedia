-- Prove2me | solution 1 for BaconThesis.Multilevel.preserved_subspace_levels
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T22:48:25.708773+00:00
-- url     : https://prove2.me/submissions/f1f7fbec-20bb-4509-abeb-9eb1886aa739

import Mathlib
import Definitions.Def_BaconThesis_Multilevel_PreservesSubspace

open scoped Matrix

namespace BaconThesis.Multilevel.SolPSL

open BaconThesis.Multilevel

variable {N : ℕ}

lemma mulVec_mem {H : Matrix (Fin N) (Fin N) ℂ} {S : Submodule ℂ (Fin N → ℂ)}
    (hS : PreservesSubspace H S) {v : Fin N → ℂ} (hv : v ∈ S) : H *ᵥ v ∈ S := by
  obtain ⟨b, h, -, hH, hb⟩ := hS
  subst hH
  rw [Matrix.sum_mulVec]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  rcases hb k with hk | hk
  · exact S.smul_mem _ (S.smul_mem _ hk)
  · have h0 : star (b k) ⬝ᵥ v = 0 := by
      have h1 := hk v hv
      have h2 : star (b k) ⬝ᵥ v = star (star v ⬝ᵥ b k) := by
        simp [dotProduct, star_sum, mul_comm]
      rw [h2, h1, star_zero]
    rw [h0, zero_smul, smul_zero]
    exact S.zero_mem

/-- `g T v` multiplies coordinate `k` by `∏_{j ∈ T} (ω k - ω j)`. -/
def g (ω : Fin N → ℝ) (T : Finset (Fin N)) (v : Fin N → ℂ) : Fin N → ℂ :=
  fun k => (∏ j ∈ T, (((ω k : ℝ) : ℂ) - ((ω j : ℝ) : ℂ))) * v k

lemma g_mem (ω : Fin N → ℝ) (S : Submodule ℂ (Fin N → ℂ))
    (hS : ∀ v ∈ S, Matrix.diagonal (fun i => ((ω i : ℝ) : ℂ)) *ᵥ v ∈ S)
    {v : Fin N → ℂ} (hv : v ∈ S) (T : Finset (Fin N)) : g ω T v ∈ S := by
  induction T using Finset.induction_on with
  | empty =>
    have : g ω ∅ v = v := by ext k; simp [g]
    rw [this]; exact hv
  | insert a T ha ih =>
    have : g ω (insert a T) v =
        Matrix.diagonal (fun i => ((ω i : ℝ) : ℂ)) *ᵥ g ω T v - ((ω a : ℝ) : ℂ) • g ω T v := by
      ext k
      simp only [g, Finset.prod_insert ha, Matrix.mulVec_diagonal, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
    rw [this]
    exact S.sub_mem (hS _ ih) (S.smul_mem _ ih)

end BaconThesis.Multilevel.SolPSL

open BaconThesis.Multilevel BaconThesis.Multilevel.SolPSL in
theorem solution {N : ℕ} (ω : Fin N → ℝ) (hω : Function.Injective ω)
    (S : Submodule ℂ (Fin N → ℂ))
    (hS : PreservesSubspace (Matrix.diagonal fun i => ((ω i : ℝ) : ℂ)) S) :
    S = Submodule.span ℂ ((fun i => (Pi.single i (1 : ℂ) : Fin N → ℂ)) ''
      {i | (Pi.single i (1 : ℂ) : Fin N → ℂ) ∈ S}) := by
  apply le_antisymm
  · intro v hv
    have hsingle : ∀ i, v i ≠ 0 → (Pi.single i (1 : ℂ) : Fin N → ℂ) ∈ S := by
      intro i hi
      have hg := g_mem ω S (fun w hw => mulVec_mem hS hw) hv (Finset.univ.erase i)
      have hc : (∏ j ∈ Finset.univ.erase i, (((ω i : ℝ) : ℂ) - ((ω j : ℝ) : ℂ))) * v i ≠ 0 := by
        refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j hj => ?_) hi
        rw [sub_ne_zero, Ne, Complex.ofReal_inj]
        exact fun h => (Finset.mem_erase.mp hj).1 (hω h).symm
      have heq : g ω (Finset.univ.erase i) v =
          ((∏ j ∈ Finset.univ.erase i, (((ω i : ℝ) : ℂ) - ((ω j : ℝ) : ℂ))) * v i) •
            (Pi.single i (1 : ℂ) : Fin N → ℂ) := by
        ext k
        by_cases hk : k = i
        · subst hk; simp [g]
        · simp only [g, Pi.smul_apply, Pi.single_apply, hk, if_false, smul_zero]
          rw [Finset.prod_eq_zero (i := k) (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩)
            (sub_self _), zero_mul]
      rw [heq] at hg
      exact (S.smul_mem_iff hc).mp hg
    have hv' : v = ∑ i, v i • (Pi.single i (1 : ℂ) : Fin N → ℂ) := by
      ext k; simp [Pi.single_apply]
    rw [hv']
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : v i = 0
    · rw [hi, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hsingle i hi, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hi
