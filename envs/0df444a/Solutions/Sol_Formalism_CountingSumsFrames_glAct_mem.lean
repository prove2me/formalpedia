-- Prove2me | solution 1 for Formalism.CountingSumsFrames.glAct_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:31.873496+00:00
-- url     : https://prove2.me/submissions/05bcdcac-b609-4c60-a7a9-a3b1b27f3b78

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.CountingSumsFrames
theorem _root_.solution {N r : ℕ} (LL : Letters N) (j : ℕ) (c d : Fin r) :
    (glAct p LL j c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
      FockB.Ops {v : Fin N × Fin r | (v.1 : ℕ) < j} := by
  unfold glAct FockB.Ops
  refine Subalgebra.sum_mem _ fun i _ => ?_
  split_ifs with hi hv
  · have h1 : (LinearMap.mulLeft ℚ_[p] (X (i, c)) : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
        Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | (v.1 : ℕ) < j}) :=
      Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, c), hi, Or.inl rfl⟩)
    have h2 : ((pderiv (R := ℚ_[p]) (i, d) : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈ Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | (v.1 : ℕ) < j}) :=
      Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, d), hi, Or.inr rfl⟩)
    exact Subalgebra.mul_mem _ h1 h2
  · have h1 : (LinearMap.mulLeft ℚ_[p] (X (i, d)) : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
        Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | (v.1 : ℕ) < j}) :=
      Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, d), hi, Or.inl rfl⟩)
    have h2 : ((pderiv (R := ℚ_[p]) (i, c) : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈ Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | (v.1 : ℕ) < j}) :=
      Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, c), hi, Or.inr rfl⟩)
    exact Subalgebra.neg_mem _ (Subalgebra.mul_mem _ h1 h2)
  · exact Subalgebra.zero_mem _
end Formalism.CountingSumsFrames
