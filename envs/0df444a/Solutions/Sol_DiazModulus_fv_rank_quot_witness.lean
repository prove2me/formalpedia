-- Prove2me | solution 1 for DiazModulus.fv_rank_quot_witness
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T14:10:24.823671+00:00
-- url     : https://prove2.me/submissions/103ed826-10fc-4585-a3fb-654e3f572f6e

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A finite-dimensional witness for a lower bound on dim Y/(Y ∩ V)

Let `K ⊆ Y` be the `Q̄`-subspace `Y ∩ V`, seen inside `Y`. If `dim_Q̄ Y/K ≥ N` as a cardinal, the quotient
contains `N` linearly independent classes. Lift each class to some `y ∈ Y` and let `Y₀` be the `Q̄`-span of
the lifts, a finite-dimensional subspace of `Y`. The lifts are linearly independent (their images in the
quotient are), so `dim Y₀ = N`. If `Σ cᵢ yᵢ` lies in `V`, it lies in `Y ∩ V`, so `Σ cᵢ [yᵢ] = 0` in the
quotient and every `cᵢ = 0`. Hence `Y₀ ∩ V = 0` and `dim Y₀ − dim (Y₀ ∩ V) = N`. -/

open DiazModulus in
theorem solution {n : ℕ} (Y : Submodule (↥Qbar) (Fin n → ℂ))
    (V : Submodule ℂ (Fin n → ℂ)) (N : ℕ)
    (hN : (N : Cardinal) ≤
      Module.rank (↥Qbar) (↥Y ⧸ (V.restrictScalars (↥Qbar)).comap Y.subtype)) :
    ∃ Y₀ : Submodule (↥Qbar) (Fin n → ℂ), Y₀ ≤ Y ∧ FiniteDimensional (↥Qbar) ↥Y₀ ∧
      N ≤ Module.finrank (↥Qbar) ↥Y₀ - Module.finrank (↥Qbar) ↥(Y₀ ⊓ V.restrictScalars (↥Qbar)) := by
  classical
  set K := (V.restrictScalars (↥Qbar)).comap Y.subtype
  have : Module.Free (↥Qbar) (↥Y ⧸ K) := Module.Free.of_divisionRing _ _
  obtain ⟨s, hs, hli⟩ := le_rank_iff_exists_linearIndependent_finset.1 hN
  choose g hg using fun q : ↥(s : Set (↥Y ⧸ K)) => Submodule.Quotient.mk_surjective K (q : ↥Y ⧸ K)
  let v : ↥(s : Set (↥Y ⧸ K)) → (Fin n → ℂ) := fun q => (g q : Fin n → ℂ)
  have hcomp : K.mkQ ∘ g = ((↑) : ↥(s : Set (↥Y ⧸ K)) → ↥Y ⧸ K) := funext hg
  have hlig : LinearIndependent (↥Qbar) g := by
    apply LinearIndependent.of_comp K.mkQ
    rw [hcomp]
    exact hli
  have hliv : LinearIndependent (↥Qbar) v := hlig.map' Y.subtype (Submodule.ker_subtype Y)
  refine ⟨Submodule.span (↥Qbar) (Set.range v), ?_, ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    exact (g q).2
  · exact FiniteDimensional.span_of_finite (↥Qbar) (Set.finite_range v)
  · have hbot : Submodule.span (↥Qbar) (Set.range v) ⊓ V.restrictScalars (↥Qbar) = ⊥ := by
      rw [eq_bot_iff]
      rintro z ⟨hz1, hz2⟩
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz1
      have hmem : (∑ q, c q • g q) ∈ K := by
        change Y.subtype (∑ q, c q • g q) ∈ V.restrictScalars (↥Qbar)
        rw [map_sum]
        simpa [map_smul, v] using hz2
      have h0 : ∑ q, c q • ((q : ↥Y ⧸ K)) = 0 := by
        have e : K.mkQ (∑ q, c q • g q) = 0 := (Submodule.Quotient.mk_eq_zero K).2 hmem
        rw [map_sum] at e
        simpa [map_smul, Submodule.mkQ_apply, hg] using e
      have hc := (Fintype.linearIndependent_iff.1 hli) c h0
      simp [hc]
    rw [hbot, finrank_bot, Nat.sub_zero, finrank_span_eq_card hliv]
    simp [hs]
