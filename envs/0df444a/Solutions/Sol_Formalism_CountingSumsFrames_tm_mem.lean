-- Prove2me | solution 1 for Formalism.CountingSumsFrames.tm_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:12.382805+00:00
-- url     : https://prove2.me/submissions/4c1abb6e-289b-4042-9800-e3d2393acfde

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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) (j : ℕ) (i : Fin N) (c d : Fin r) :
    tm (p := p) LL j i c d ∈ FockB.Ops {v : Fin N × Fin r | v.1 = i} := by
  unfold tm FockB.Ops
  split_ifs with hi hv
  · have h1 : (LinearMap.mulLeft ℚ_[p] (X (i, c)) : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
        Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | v.1 = i}) :=
      Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, c), rfl, Or.inl rfl⟩)
    have h2 : ((pderiv (R := ℚ_[p]) (i, d) : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈ Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | v.1 = i}) :=
      Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, d), rfl, Or.inr rfl⟩)
    exact Subalgebra.mul_mem _ h1 h2
  · have h1 : (LinearMap.mulLeft ℚ_[p] (X (i, d)) : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
        Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | v.1 = i}) :=
      Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, d), rfl, Or.inl rfl⟩)
    have h2 : ((pderiv (R := ℚ_[p]) (i, c) : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈ Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | v.1 = i}) :=
      Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, c), rfl, Or.inr rfl⟩)
    exact Subalgebra.neg_mem _ (Subalgebra.mul_mem _ h1 h2)
  · exact Subalgebra.zero_mem _
end Formalism.CountingSumsFrames
