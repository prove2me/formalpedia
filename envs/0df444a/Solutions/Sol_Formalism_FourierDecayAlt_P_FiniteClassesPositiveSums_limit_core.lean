-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.limit_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:02.706233+00:00
-- url     : https://prove2.me/submissions/c44f0f3f-122d-4c83-ab97-bb39b7484b6b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteClassesPositiveSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_periodic_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_psd_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
variable {K : Type} [CommRing K] (R : Subring K)
variable {R} {F : Finset (Point K)} {Lc : Set K} {S : Finset (K ⧸ R.toAddSubgroup)}
namespace Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
theorem _root_.solution (hEntry : PSDEntryBound) (hSubseq : BoundedSubseq)
    (hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ Lc → y ∈ S)
    (M : Point K → Point K → ℂ) (Th : ℕ → K → Point K → Point K → ℂ)
    (h1 : ∀ j x, ∀ r ∈ R, Th j (x + r) = Th j x) (h2 : ∀ j x, IsPSD F (Th j x))
    (h3 : ∀ j x, x ∉ Lc → ∀ h ∈ F, ∀ h' ∈ F, Th j x h h' = 0)
    (h5 : ∀ j, IsPSD F (fun h h' => M h h' -
      ∑ᶠ y : K ⧸ R.toAddSubgroup, Th j (Quotient.out y) h h')) :
    ∃ (φ : ℕ → ℕ) (Θ : K → Point K → Point K → ℂ), StrictMono φ ∧
      (∀ x, ∀ r ∈ R, Θ (x + r) = Θ x) ∧
      ∀ x, ∀ h ∈ F, ∀ h' ∈ F, Tendsto (fun j => Th (φ j) x h h') atTop (𝓝 (Θ x h h')) := by
  classical
  let T : Finset ((K ⧸ R.toAddSubgroup) × Point K × Point K) := S ×ˢ F ×ˢ F
  let θ : ℕ → T → ℂ := fun j i => Th j (Quotient.out i.1.1) i.1.2.1 i.1.2.2
  let B : ℝ := ∑ h ∈ F, |(M h h).re|
  have hB0 : 0 ≤ B := sum_nonneg fun _ _ => abs_nonneg _
  have hBh : ∀ h ∈ F, |(M h h).re| ≤ B := fun h hh =>
    single_le_sum (f := fun h => |(M h h).re|) (fun _ _ => abs_nonneg _) hh
  have hb : ∀ j i, ‖θ j i‖ ≤ B := by
    rintro j ⟨⟨y, h, h'⟩, hi⟩
    simp only [T, mem_product] at hi
    have hE := hEntry _ F (Th j (Quotient.out y)) M (h2 j _)
      (psd_single hS (h1 j) (h2 j) (h3 j) (h5 j) _) h hi.2.1 h' hi.2.2
    have hle : (M h h).re * (M h' h').re ≤ B ^ 2 := by
      calc (M h h).re * (M h' h').re ≤ |(M h h).re * (M h' h').re| := le_abs_self _
        _ = |(M h h).re| * |(M h' h').re| := abs_mul _ _
        _ ≤ B * B := mul_le_mul (hBh h hi.2.1) (hBh h' hi.2.2) (abs_nonneg _) hB0
        _ = B ^ 2 := (sq B).symm
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB0 two_ne_zero).1 (hE.trans hle)
  obtain ⟨φ, l, hφ, hl⟩ := hSubseq T θ B hb
  refine ⟨φ, fun x h h' => if hx : (((x : K) : K ⧸ R.toAddSubgroup), h, h') ∈ T then l ⟨_, hx⟩
    else 0, hφ, ?_, ?_⟩
  · intro x r hr
    have e : (((x + r : K)) : K ⧸ R.toAddSubgroup) = ((x : K) : K ⧸ R.toAddSubgroup) := by
      rw [QuotientAddGroup.eq]
      have : -(x + r) + x = -r := by ring
      rw [this]
      exact neg_mem hr
    funext h h'
    simp only [e]
  · intro x h hh h' hh'
    have e2 : ∀ j, Th j (Quotient.out ((x : K) : K ⧸ R.toAddSubgroup)) = Th j x :=
      fun j => periodic_out R (Th j) (h1 j) x
    by_cases hx : (((x : K) : K ⧸ R.toAddSubgroup), h, h') ∈ T
    · simp only [dif_pos hx]
      have := hl ⟨_, hx⟩
      simp only [θ, e2] at this
      exact this
    · simp only [dif_neg hx]
      have hxS : ((x : K) : K ⧸ R.toAddSubgroup) ∉ S := by
        intro hc
        exact hx (by simp only [T, mem_product]; exact ⟨hc, hh, hh'⟩)
      have : ∀ j, Th (φ j) x h h' = 0 := by
        intro j
        rw [← e2]
        exact h3 _ _ (fun hc => hxS (hS _ hc)) h hh h' hh'
      simp only [this]
      exact tendsto_const_nhds
end Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
