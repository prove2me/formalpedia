-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.ql_span_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:34:09.406161+00:00
-- url     : https://prove2.me/submissions/041351b2-bdbf-4f31-892a-ca1dbfc9827e

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepClosed
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepDescent
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LengthLeOfSemilinear
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_length_le_of_semilinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
open Module Formalism.LatticeBaseChangeAlt Formalism.LatticeBaseChangeAlt.BQuot
variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O']
  [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
namespace Formalism.MainNotions.Gaps.T0
theorem _root_.solution {V V₁ : Type} [AddCommGroup V] [Module O V] [AddCommGroup V₁] [Module O' V₁]
    (ϖ : O) (hϖ : Irreducible ϖ) (hϖ' : Irreducible (algebraMap O O' ϖ))
    (jj : V →ₛₗ[algebraMap O O'] V₁) (A S : Submodule O V) (S₁ : Submodule O' V₁)
    (h : ∀ x ∈ S, jj x ∈ S₁) :
    ql (Submodule.span O' (jj '' (A : Set V))) S₁ ≤ ql A S := by
  set A₁ : Submodule O' V₁ := Submodule.span O' (jj '' (A : Set V)) with hA₁
  let g0 : ↥A →ₛₗ[algebraMap O O'] (↥A₁ ⧸ S₁.comap A₁.subtype) :=
    (S₁.comap A₁.subtype).mkQ.comp
      ((jj.comp A.subtype).codRestrict A₁ fun x => Submodule.subset_span ⟨x, x.2, rfl⟩)
  have hk : S.comap A.subtype ≤ LinearMap.ker g0 := by
    intro x hx
    rw [LinearMap.mem_ker]
    show (S₁.comap A₁.subtype).mkQ _ = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h x hx
  refine length_le_of_semilinear ϖ hϖ hϖ' ((S.comap A.subtype).liftQ g0 hk) ?_
  rw [eq_top_iff]
  intro z hz
  clear hz
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact Submodule.subset_span ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add a b ha hb iha ihb => exact Submodule.add_mem _ iha ihb
  | smul r a ha ih => exact Submodule.smul_mem _ r ih
end Formalism.MainNotions.Gaps.T0
