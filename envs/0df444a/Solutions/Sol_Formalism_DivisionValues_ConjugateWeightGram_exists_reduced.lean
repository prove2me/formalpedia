-- Prove2me | solution 1 for Formalism.DivisionValues.ConjugateWeightGram.exists_reduced
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:20.44791+00:00
-- url     : https://prove2.me/submissions/0edfd1d2-8cd9-4b0c-93aa-8efdf4fea7d2

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open RationalHermitianForm
open Formalism.DivisionValues.ConjugateWeightGram
namespace Formalism.DivisionValues.ConjugateWeightGram
theorem _root_.solution {F : Type} [Field F] {n : ℕ} (Z : Submodule F (Fin n → F)) :
    ∃ (d : ℕ) (z : Fin d → Fin n → F) (f : Fin d → Fin n), LinearIndependent F z ∧
      Submodule.span F (Set.range z) = Z ∧ ∀ a b, z a (f b) = if a = b then 1 else 0 := by
  classical
  set d := finrank F Z with hd
  let b : Basis (Fin d) F Z := finBasis F Z
  let A : Matrix (Fin d) (Fin n) F := Matrix.of fun a i => (b a : Fin n → F) i
  have hrow : LinearIndependent F A.row :=
    b.linearIndependent.map' Z.subtype (Submodule.ker_subtype _)
  have hrank : A.rank = d := by simpa using hrow.rank_matrix
  have hcols : Submodule.span F (Set.range A.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_cols, hrank]
    simp
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent F (Set.range A.col)
  have hsp : ⊤ ≤ Submodule.span F (Set.range (Subtype.val : s → Fin d → F)) := by
    rw [Subtype.range_coe, hspan, hcols]
  let bs : Basis s F (Fin d → F) := Basis.mk hli hsp
  have : Fintype s := FiniteDimensional.fintypeBasisIndex bs
  have hcard : Fintype.card s = d := by
    have := finrank_eq_card_basis bs
    simpa using this.symm
  let e : Fin d ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  choose g hg using fun x : s => hs x.2
  let f : Fin d → Fin n := fun a => g (e a)
  let B : Matrix (Fin d) (Fin d) F := A.submatrix id f
  have hBcol : B.col = fun a => ((e a : s) : Fin d → F) := by
    funext a
    exact hg (e a)
  have hB : IsUnit B := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit, hBcol]
    exact hli.comp e e.injective
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB
  let z : Fin d → Fin n → F := fun a => (B⁻¹ * A) a
  have hz : ∀ a b, z a (f b) = if a = b then 1 else 0 := by
    intro a c
    have h1 : z a (f c) = (B⁻¹ * B) a c := by
      simp only [z, B, Matrix.mul_apply, Matrix.submatrix_apply, id]
    rw [h1, Matrix.nonsing_inv_mul B hBdet, Matrix.one_apply]
  have hzli : LinearIndependent F z := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have := congrFun hc (f i)
    simpa [Finset.sum_apply, hz] using this
  have hzmem : ∀ a, z a ∈ Z := by
    intro a
    have : z a = ∑ c, B⁻¹ a c • (b c : Fin n → F) := by
      funext i
      simp [z, A, Matrix.mul_apply, Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (b c).2
  refine ⟨d, z, f, hzli, ?_, hz⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact hzmem a
  · rw [finrank_span_eq_card hzli]
    simp [hd]
end Formalism.DivisionValues.ConjugateWeightGram
