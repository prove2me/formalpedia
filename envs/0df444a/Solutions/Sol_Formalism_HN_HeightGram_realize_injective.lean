-- Prove2me | solution 1 for Formalism.HN.HeightGram.realize_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:44.029545+00:00
-- url     : https://prove2.me/submissions/c0f53db5-09d1-4bab-8c1f-4b367e32ae1d

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Theorems.Thm_Formalism_HN_HeightGram_realize_apply0
import Theorems.Thm_Formalism_HN_HeightGram_realize_apply1
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
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.HeightGram
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.HeightGram
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) : Function.Injective (Formalism.HermitianLatticesTheory.realize b X) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hf : ∀ i, Formalism.HermitianLatticesTheory.fcoord b X v x i = 0 := by
    intro i
    apply Complex.ext
    · rw [← realize_apply0, hx]; simp
    · rw [← realize_apply1, hx]; simp
  have hvec : Formalism.HermitianLatticesTheory.vecAt b v x = 0 := by
    have h1 : (X v)⁻¹ *ᵥ Formalism.HermitianLatticesTheory.vecAt b v x = 0 := funext hf
    have h2 := congrArg (fun w => X v *ᵥ w) h1
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
    rwa [Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec] at h2
  have hrep : b.repr x = 0 := by
    ext i
    have := congrFun hvec i
    simp only [Formalism.HermitianLatticesTheory.vecAt, Pi.zero_apply] at this
    simpa using this
  simpa using hrep
end Formalism.HN.HeightGram
