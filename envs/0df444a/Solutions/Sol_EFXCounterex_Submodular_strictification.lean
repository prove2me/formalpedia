-- Prove2me | solution 1 for EFXCounterex.Submodular.strictification
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:06:27.874495+00:00
-- url     : https://prove2.me/submissions/74ebc77e-8b1d-4bc8-a529-e151949fc14b

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXCounterex_Submodular_Setting

open EFXCounterex.Submodular

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (∀ i, IsNormalized (perturb ε v i)) ∧
      (∀ i, IsStrictlyIncreasing (perturb ε v i)) ∧
      (∀ i j S T, v i S < v j T → perturb ε v i S < perturb ε v j T) ∧
      (∀ X : Fin n → Finset (Fin m), IsAllocation X →
        LittleCharity.EFX.IsEFX (perturb ε v) X → LittleCharity.EFX.IsEFX v X) ∧
      (∀ (σ : Equiv.Perm (Fin n)) (π : Equiv.Perm (Fin m)),
        IsProfileSymmetry v σ π → IsProfileSymmetry (perturb ε v) σ π) := by
  classical
  -- a uniform positive lower bound on the strict gaps
  have hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ i j S T, v i S < v j T → δ ≤ v j T - v i S := by
    let P : Finset (Fin n × Fin n × Finset (Fin m) × Finset (Fin m)) :=
      Finset.univ.filter (fun q => v q.1 q.2.2.1 < v q.2.1 q.2.2.2)
    by_cases hP : P.Nonempty
    · obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image P
        (fun q => v q.2.1 q.2.2.2 - v q.1 q.2.2.1) hP
      have hqlt : v q.1 q.2.2.1 < v q.2.1 q.2.2.2 := by
        simpa [P] using hq
      refine ⟨v q.2.1 q.2.2.2 - v q.1 q.2.2.1, by linarith, ?_⟩
      intro i j S T h
      exact hmin (i, j, S, T) (by simp [P, h])
    · refine ⟨1, one_pos, ?_⟩
      intro i j S T h
      exact absurd ⟨(i, j, S, T), by simp [P, h]⟩ hP
  obtain ⟨δ, hδ, hδgap⟩ := hgap
  refine ⟨δ / (m + 1), by positivity, ?_⟩
  intro ε hε hεlt
  have hεm : ε * (m + 1) < δ := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < m + 1)).1 hεlt
    linarith
  have hcard : ∀ S : Finset (Fin m), (S.card : ℝ) ≤ m := by
    intro S
    have := Finset.card_le_univ S
    simpa using (by exact_mod_cast this : (S.card : ℝ) ≤ (Fintype.card (Fin m) : ℝ))
  have hstrict : ∀ i j S T, v i S < v j T → perturb ε v i S < perturb ε v j T := by
    intro i j S T h
    have h1 := hδgap i j S T h
    have h2 := hcard S
    have h3 : (0 : ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
    unfold perturb
    nlinarith
  refine ⟨?_, ?_, hstrict, ?_, ?_⟩
  · intro i
    have h0 : v i ∅ = 0 := hnorm i
    unfold IsNormalized perturb
    simp [h0]
  · intro i S T hST
    have h1 : v i S ≤ v i T := hmono i S T hST.subset
    have h2 : (S.card : ℝ) < (T.card : ℝ) := by exact_mod_cast Finset.card_lt_card hST
    unfold perturb
    nlinarith
  · intro X _ hE i j g hg
    by_contra hcon
    push Not at hcon
    have := hstrict i i _ _ hcon
    have hE' := hE i j g hg
    linarith
  · intro σ π hsym i S
    unfold perturb
    have := hsym i S
    have hc : (relabelBundle π S).card = S.card := by
      unfold relabelBundle; simp
    rw [this, hc]
