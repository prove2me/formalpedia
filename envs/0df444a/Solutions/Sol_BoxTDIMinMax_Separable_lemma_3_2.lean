-- Prove2me | solution 1 for BoxTDIMinMax.Separable.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:04:20.108505+00:00
-- url     : https://prove2.me/submissions/ecc7314d-50d7-4e02-b6c8-e16399e733bf

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting
import Theorems.Thm_BoxTDIMinMax_Separable_proposition_3_1

open Matrix BoxTDIMinMax.Separable

theorem solution {ι S : Type*} [Fintype ι] [Fintype S]
    (phi : S → ℤ → WithTop ℤ) (hphi : ∀ s, DiscConvex (phi s))
    (Q : Matrix ι S ℤ) (p : ι → ℤ) (zStar : S → ℤ) (hz : zStar ∈ intPts Q p)
    (yStar : ι → ℤ) (hy : 0 ≤ yStar) (hc : Compatible phi Q zStar yStar) :
    ∀ z ∈ intPts Q p,
      Phi phi zStar ≤ Phi phi z + ((yStar ⬝ᵥ (Q *ᵥ zStar - p) : ℤ) : WithTop ℤ) := by
  intro z hzR
  set w : S → ℤ := yStar ᵥ* Q with hw
  -- (3.11) for each coordinate, via Proposition 3.1
  have hs : ∀ s, phi s (zStar s) + ((w s * z s : ℤ) : WithTop ℤ) ≤
      phi s (z s) + ((w s * zStar s : ℤ) : WithTop ℤ) := fun s =>
    proposition_3_1 (phi s) (hphi s) (zStar s) (w s) (hc s) (z s)
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hs s)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← WithTop.coe_sum,
    ← WithTop.coe_sum] at hsum
  change Phi phi zStar + _ ≤ Phi phi z + _ at hsum
  have hfinStar : Phi phi zStar ≠ ⊤ := by
    unfold Phi
    exact WithTop.sum_ne_top.mpr (fun s _ => (hc s).1)
  obtain ⟨A, hA⟩ := WithTop.ne_top_iff_exists.mp hfinStar
  by_cases hfin : Phi phi z = ⊤
  · rw [hfin]; simp
  obtain ⟨B, hB⟩ := WithTop.ne_top_iff_exists.mp hfin
  rw [← hA, ← hB] at hsum ⊢
  have hsum' : A + ∑ s, w s * z s ≤ B + ∑ s, w s * zStar s := by exact_mod_cast hsum
  -- (3.12): w z = y (Q z) ≥ y p
  have h1 : ∑ s, w s * z s = yStar ⬝ᵥ (Q *ᵥ z) := by
    rw [Matrix.dotProduct_mulVec]; rfl
  have h2 : ∑ s, w s * zStar s = yStar ⬝ᵥ (Q *ᵥ zStar) := by
    rw [Matrix.dotProduct_mulVec]; rfl
  have h3 : yStar ⬝ᵥ p ≤ yStar ⬝ᵥ (Q *ᵥ z) := by
    unfold dotProduct
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hzR i) (hy i))
  rw [dotProduct_sub]
  have : A ≤ B + (yStar ⬝ᵥ (Q *ᵥ zStar) - yStar ⬝ᵥ p) := by linarith
  exact_mod_cast this
