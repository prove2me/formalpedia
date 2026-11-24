-- Prove2me | solution 1 for Formalism.HN.PlaceLattice.discrete_span_of_linIndep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:22.659435+00:00
-- url     : https://prove2.me/submissions/72468807-10c6-46c9-b358-359a5fb68e7c

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceLattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.PlaceLattice
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι' : Type*} {f : ι' → E} (hf : LinearIndependent ℝ f) :
    DiscreteTopology (Submodule.span ℤ (Set.range f)) := by
  classical
  haveI : Finite ι' := hf.finite
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend (Basis.span hf).equivFun.toLinearMap
  have hψW : ∀ w : Submodule.span ℝ (Set.range f), ψ w = (Basis.span hf).equivFun w :=
    fun w => LinearMap.congr_fun hψ w
  have hψf : ∀ i, ψ (f i) = Pi.basisFun ℝ ι' i := by
    intro i
    have h : ψ (f i) = (Basis.span hf).equivFun (Basis.span hf i) := by
      rw [Basis.span_apply]
      exact hψW ⟨f i, Submodule.subset_span ⟨i, rfl⟩⟩
    rw [h]
    ext j
    simp [Basis.equivFun_self, Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hmem : ∀ x ∈ Submodule.span ℤ (Set.range f),
      ψ x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι')) := by
    intro x hx
    have hle : Submodule.map (ψ.restrictScalars ℤ) (Submodule.span ℤ (Set.range f)) ≤
        Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι')) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨i, (hψf i).symm⟩
    exact hle ⟨x, hx, rfl⟩
  have hW : ∀ z ∈ Submodule.span ℤ (Set.range f), z ∈ Submodule.span ℝ (Set.range f) :=
    fun z hz => Submodule.span_le_restrictScalars ℤ ℝ _ hz
  haveI := ZSpan.discreteTopology_pi_basisFun (ι := ι')
  refine DiscreteTopology.of_continuous_injective
    (f := fun x : Submodule.span ℤ (Set.range f) =>
      (⟨ψ x, hmem x x.2⟩ : Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι')))) ?_ ?_
  · fun_prop
  · intro x y hxy
    have h1 : ψ x = ψ y := congrArg Subtype.val hxy
    have h2 : (⟨(x : E), hW _ x.2⟩ : Submodule.span ℝ (Set.range f)) = ⟨y, hW _ y.2⟩ :=
      (Basis.span hf).equivFun.injective (by rw [← hψW, ← hψW]; exact h1)
    exact Subtype.ext (Subtype.mk.inj h2)
end Formalism.HN.PlaceLattice
