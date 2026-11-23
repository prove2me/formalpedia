-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.glAct_mem_PolAB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:45.635794+00:00
-- url     : https://prove2.me/submissions/40f6f32f-7d66-44fb-ad1c-98bca83b9d88

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_mem_PolAB_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har4
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution {K : Type} [Field K] {k A B : ℕ} (g : GL (Fin k) K) (f : PolXY K k)
    (hf : f ∈ PolAB K k A B) : glAct g f ∈ PolAB K k A B := by
  rw [mem_PolAB_iff] at hf ⊢
  set σ : XY k → PolXY K k := Sum.elim
    (fun i : Fin k => ∑ j : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j))
    (fun i : Fin k => ∑ j : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i) * X (Sum.inr j)) with hσdef
  have hgl : glAct g = aeval σ := rfl
  have hσ : ∀ v : XY k, IsWeightedHomogeneous (wXY k) (σ v) (wXY k v) := by
    rintro (i | i)
    · show IsWeightedHomogeneous (wXY k) (∑ j : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j)) (wXY k (Sum.inl i))
      apply IsWeightedHomogeneous.sum
      intro j _
      have h := (isWeightedHomogeneous_C (wXY k) ((g : Matrix (Fin k) (Fin k) K) i j)).mul
        (isWeightedHomogeneous_X (R := K) (wXY k) (Sum.inl j))
      convert h using 1
      simp [wXY]
    · show IsWeightedHomogeneous (wXY k) (∑ j : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i) * X (Sum.inr j)) (wXY k (Sum.inr i))
      apply IsWeightedHomogeneous.sum
      intro j _
      have h := (isWeightedHomogeneous_C (wXY k) (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i)).mul
        (isWeightedHomogeneous_X (R := K) (wXY k) (Sum.inr j))
      convert h using 1
      simp [wXY]
  rw [hgl, f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  have hdeg := hf (MvPolynomial.mem_support_iff.1 hm)
  rw [← hdeg]
  have hp : IsWeightedHomogeneous (wXY k) (m.prod fun v e => σ v ^ e) (Finsupp.weight (wXY k) m) := by
    rw [Finsupp.weight_apply, Finsupp.prod, Finsupp.sum]
    apply IsWeightedHomogeneous.prod
    intro v _
    exact (hσ v).pow (m v)
  rw [← zero_add (Finsupp.weight (wXY k) m)]
  exact (isWeightedHomogeneous_C (wXY k) (coeff m f)).mul hp
end Formalism.CountingSumsFrames.Har4
