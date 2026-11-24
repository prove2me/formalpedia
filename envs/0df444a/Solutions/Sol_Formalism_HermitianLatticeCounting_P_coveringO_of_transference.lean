-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.coveringO_of_transference
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:46.532504+00:00
-- url     : https://prove2.me/submissions/575ca0d2-7cf8-4dc9-b146-5a54cf84f788

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SumComplexEmbeddingsEqSumInfinitePlace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sum_complexEmbeddings_eq_sum_infinitePlace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5bSig_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5bLat_mem
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_four_mul_card_le_norm_sq_mul_discr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
open NumberField
open NumberField
section Cov
variable {E : Type} [Field E] [NumberField E]
end Cov
open NumberField
section Cov2
variable {E : Type} [Field E] [NumberField E]
end Cov2
private theorem finrank_eq_two_mul_card_infinitePlace_of_isComplex {E : Type} [Field E] [NumberField E]
    (hc : ∀ w : InfinitePlace E, w.IsComplex) :
    (Module.finrank ℚ E : ℝ) = 2 * (Fintype.card (InfinitePlace E) : ℝ) := by
  have h := sum_complexEmbeddings_eq_sum_infinitePlace hc (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    NumberField.Embeddings.card] at h
  have h' : (((Module.finrank ℚ E : ℝ)) : ℂ) =
      ((2 * (Fintype.card (InfinitePlace E) : ℝ) : ℝ) : ℂ) := by
    push_cast
    rw [h]
    ring
  exact Complex.ofReal_injective h'
private theorem two_mul_div_two_le_sqrt_mul_sqrt_mul_rpow (r D : ℝ) (hr : 0 < r) (hD : 0 < D) :
    2 * r / 2 ≤ Real.sqrt (4 * r / D ^ (1 / r)) * (Real.sqrt (2 * r) * D ^ (1 / (2 * r))) := by
  have hT : 0 < D ^ (1 / r) := Real.rpow_pos_of_pos hD _
  have hT' : D ^ (1 / r) ≠ 0 := hT.ne'
  have hr' : r ≠ 0 := hr.ne'
  have ht2 : (D ^ (1 / (2 * r))) ^ 2 = D ^ (1 / r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le]
    congr 1
    push_cast
    field_simp
  have h4 : 0 ≤ 4 * r / D ^ (1 / r) := div_nonneg (by linarith) hT.le
  have h2r : 0 ≤ 2 * r := by linarith
  have hs0 : 0 ≤ Real.sqrt (4 * r / D ^ (1 / r)) * (Real.sqrt (2 * r) * D ^ (1 / (2 * r))) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hD.le _))
  have hs2 : (Real.sqrt (4 * r / D ^ (1 / r)) * (Real.sqrt (2 * r) * D ^ (1 / (2 * r)))) ^ 2 =
      8 * r ^ 2 := by
    rw [mul_pow, mul_pow, ht2, Real.sq_sqrt h4, Real.sq_sqrt h2r]
    field_simp
    ring
  nlinarith [hs0, hs2, hr]
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open NumberField
open NumberField
open NumberField
set_option maxHeartbeats 800000
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hT : Transference) : CoveringO := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.CoveringO
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.Transference at hT
  intro E _ _ hc x
  classical
  have hr0 : (0 : ℝ) < Fintype.card (InfinitePlace E) := by exact_mod_cast Fintype.card_pos
  have hcard := finrank_eq_two_mul_card_infinitePlace_of_isComplex hc
  have hfin : (finrank ℝ (s5bV E) : ℝ) = finrank ℚ E := by
    exact_mod_cast ((complexSpaceMixedLinearEquiv hc).finrank_eq.trans (mixedEmbedding.finrank E))
  have hd : (discr E : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.discr_ne_zero E
  have hD : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr hd
  have hDr : 0 < |(discr E : ℝ)| ^ (1 / (Fintype.card (InfinitePlace E) : ℝ)) :=
    Real.rpow_pos_of_pos hD _
  obtain ⟨lam, hlam_def⟩ : ∃ lam : ℝ, lam = Real.sqrt (4 * (Fintype.card (InfinitePlace E) : ℝ) /
      |(discr E : ℝ)| ^ (1 / (Fintype.card (InfinitePlace E) : ℝ))) := ⟨_, rfl⟩
  have hlampos : 0 < lam := by
    rw [hlam_def]
    exact Real.sqrt_pos.mpr (div_pos (by linarith) hDr)
  have hdual : ∀ y : s5bV E, y ≠ 0 →
      (∀ v ∈ integerEmbeddingLattice hc, ∃ m : ℤ, inner ℝ v y = (m : ℝ)) → lam ≤ ‖y‖ := by
    intro y hy hint_r
    have h := four_mul_card_le_norm_sq_mul_discr hc y hy hint_r
    rw [hlam_def, ← Real.sqrt_sq (norm_nonneg y)]
    exact Real.sqrt_le_sqrt ((div_le_iff₀ hDr).mpr h)
  obtain ⟨l, hl, hlx⟩ := hT (s5bV E) (integerEmbeddingLattice hc) lam hlampos
    hdual (WithLp.toLp 2 x)
  obtain ⟨a, rfl⟩ := (s5bLat_mem hc l).mp hl
  refine ⟨a, fun w => ?_⟩
  have hcomp : ‖x w - w.embedding (a : E)‖ ≤
      ‖(WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E)‖ := by
    have hsq : ‖x w - w.embedding (a : E)‖ ^ 2 ≤
        ‖(WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E)‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      have h := Finset.single_le_sum (f := fun v : InfinitePlace E =>
        ‖((WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E)) v‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ w)
      simpa [s5bSig_apply] using h
    nlinarith [norm_nonneg (x w - w.embedding (a : E)),
      norm_nonneg ((WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E))]
  have hconst := two_mul_div_two_le_sqrt_mul_sqrt_mul_rpow _ _ hr0 hD
  rw [← hlam_def] at hconst
  rw [hfin, hcard] at hlx
  rw [hcard]
  have key : ‖(WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E)‖ * lam ≤
      (Real.sqrt (2 * (Fintype.card (InfinitePlace E) : ℝ)) *
        |(discr E : ℝ)| ^ (1 / (2 * (Fintype.card (InfinitePlace E) : ℝ)))) * lam := by
    calc _ ≤ _ := hlx
      _ ≤ _ := hconst
      _ = _ := mul_comm _ _
  exact hcomp.trans (le_of_mul_le_mul_right key hlampos)
end Formalism.HermitianLatticeCounting.P
