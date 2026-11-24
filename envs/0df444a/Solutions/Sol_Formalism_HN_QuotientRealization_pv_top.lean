-- Prove2me | solution 1 for Formalism.HN.QuotientRealization.pv_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:24.057297+00:00
-- url     : https://prove2.me/submissions/03a68a18-1052-416b-a8a5-e00035b04a0e

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.QuotientRealization
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.QuotientRealization
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) : pv b X ⊤ v = ⊤ := by
  have hf : ∀ j, Formalism.HermitianLatticesTheory.fcoord b X v (b j) = (X v)⁻¹ *ᵥ Pi.single j 1 := by
    intro j
    simp only [Formalism.HermitianLatticesTheory.fcoord]
    congr 1
    funext i
    by_cases h : i = j
    · subst h; simp [Formalism.HermitianLatticesTheory.vecAt]
    · simp [Formalism.HermitianLatticesTheory.vecAt, Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]
  have key : ∀ j, (WithLp.equiv 2 (ι → ℂ)).symm (Formalism.HermitianLatticesTheory.fcoord b X v (b j)) ∈ pv b X ⊤ v :=
    fun j => Submodule.subset_span ⟨b j, Submodule.mem_top, rfl⟩
  rw [eq_top_iff]
  rintro z -
  have hz : z = ∑ j, (X v *ᵥ WithLp.ofLp z) j •
      (WithLp.equiv 2 (ι → ℂ)).symm (Formalism.HermitianLatticesTheory.fcoord b X v (b j)) := by
    have e : WithLp.ofLp z = (X v)⁻¹ *ᵥ (X v *ᵥ WithLp.ofLp z) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hX v), Matrix.one_mulVec]
    apply (WithLp.equiv 2 (ι → ℂ)).injective
    funext i
    simp only [hf]
    conv_lhs => rw [WithLp.equiv_apply, e]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply, mul_comm]
  rw [hz]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (key j)
end Formalism.HN.QuotientRealization
