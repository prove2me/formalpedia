-- Prove2me | solution 2 for BookProof.ChapterUnitaryTransport.mulOp_isSelfAdjointOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:38:43.609144+00:00
-- url     : https://prove2.me/submissions/3a4a0bfd-d676-459a-bb58-25d2d41ac23f

import Mathlib
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterUnboundedPosition
import Theorems.Thm_BookProof_ChapterUnitaryTransport_adjointDomain_mulOp
-- Generated from ChapterUnitaryTransport.lean — theorem BookProof.ChapterUnitaryTransport.mulOp_isSelfAdjointOn
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterF7
open BookProof.ChapterUnboundedPosition
open BookProof.ChapterUnitaryTransport


open scoped InnerProductSpace


variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
open BookProof.ChapterUnboundedPosition BookProof.ChapterContinuityUnitaryInfinite in
theorem h44_adj (f : ℤ → ℝ) :
    BookProof.ChapterUnboundedPosition.adjointDomain f = ((mulDomain f : Submodule ℂ L2Z) : Set L2Z) := by
  ext φ
  constructor
  · rintro ⟨η, hη⟩
    have hk : ∀ k, (f k : ℂ) * (φ : ℤ → ℂ) k = (η : ℤ → ℂ) k := by
      intro k
      have hfun : (fun j => (f j : ℂ) * ((lp.single 2 k (1 : ℂ) : L2Z) : ℤ → ℂ) j)
          = ((lp.single 2 k (f k : ℂ) : L2Z) : ℤ → ℂ) := by
        funext j
        rw [lp.single_apply, lp.single_apply]
        by_cases h : j = k
        · subst h; simp
        · simp [h]
      have hmem' : Memℓp (fun j => (f j : ℂ) * ((lp.single 2 k (1 : ℂ) : L2Z) : ℤ → ℂ) j) 2 := by
        refine (memℓp_zero ?_).of_exponent_ge zero_le
        refine (Set.finite_singleton k).subset ?_
        intro j hj
        by_contra h
        apply hj
        have hjk : j ≠ k := by simpa using h
        simp [lp.single_apply, Pi.single_apply, hjk]
      have hmem : (lp.single 2 k (1 : ℂ) : L2Z) ∈ mulDomain f := hmem'
      have h1 := hη ⟨_, hmem⟩
      have hm : (BookProof.ChapterUnboundedPosition.mulOp f ⟨_, hmem⟩ : L2Z) = lp.single 2 k (f k : ℂ) := by
        refine lp.ext ?_
        exact hfun
      rw [hm] at h1
      change inner ℂ (lp.single 2 k (f k : ℂ)) φ = inner ℂ (lp.single 2 k (1 : ℂ)) η at h1
      rw [lp.inner_single_left, lp.inner_single_left] at h1
      simpa [Complex.conj_ofReal, mul_comm] using h1
    have : (fun k => (f k : ℂ) * (φ : ℤ → ℂ) k) = (η : ℤ → ℂ) := funext hk
    have hm2 : Memℓp (fun k => (f k : ℂ) * (φ : ℤ → ℂ) k) 2 := by rw [this]; exact η.2
    exact hm2
  · intro hφ
    refine ⟨⟨_, hφ⟩, fun ψ => ?_⟩
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun k => ?_
    change inner ℂ ((f k : ℂ) * ((ψ : L2Z) : ℤ → ℂ) k) ((φ : ℤ → ℂ) k)
      = inner ℂ (((ψ : L2Z) : ℤ → ℂ) k) ((f k : ℂ) * (φ : ℤ → ℂ) k)
    simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    ring

theorem solution (f : ℤ → ℝ) : IsSelfAdjointOn (mulDomain f) (mulOp f) := by
  unfold IsSelfAdjointOn
  rw [BookProof.ChapterUnitaryTransport.adjointDomain_mulOp, h44_adj]

