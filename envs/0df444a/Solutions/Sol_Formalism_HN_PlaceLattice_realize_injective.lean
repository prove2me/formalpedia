-- Prove2me | solution 1 for Formalism.HN.PlaceLattice.realize_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:31:26.451777+00:00
-- url     : https://prove2.me/submissions/c3df2ce2-5dd3-4f86-a663-ea32f517fb44

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Theorems.Thm_Formalism_HN_PlaceLattice_realize_apply0
import Theorems.Thm_Formalism_HN_PlaceLattice_realize_apply1

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
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) : Function.Injective (Formalism.HermitianLatticesTheory.realize b X) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hf : ∀ v i, Formalism.HermitianLatticesTheory.fcoord b X v x i = 0 := by
    intro v i
    apply Complex.ext
    · rw [← realize_apply0, hx]
      rfl
    · rw [← realize_apply1, hx]
      rfl
  have hv : ∀ v, Formalism.HermitianLatticesTheory.vecAt b v x = 0 := by
    intro v
    have h0 : (X v)⁻¹.mulVec (Formalism.HermitianLatticesTheory.vecAt b v x) = 0 := funext (hf v)
    have h1 := congrArg (X v).mulVec h0
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec,
      Matrix.mulVec_zero] at h1
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  apply b.repr.injective
  ext i
  have := congrFun (hv v) i
  simp only [Formalism.HermitianLatticesTheory.vecAt, Pi.zero_apply, map_eq_zero] at this
  simpa using this
end Formalism.HN.PlaceLattice
