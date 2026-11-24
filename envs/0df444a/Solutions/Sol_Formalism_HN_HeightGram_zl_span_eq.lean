-- Prove2me | solution 1 for Formalism.HN.HeightGram.zl_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:18.441823+00:00
-- url     : https://prove2.me/submissions/d957a16c-453b-462a-9fab-e23a34b368d2

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram

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
variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HN.HeightGram
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (ρ : V →+ E) {ι' : Type} [Fintype ι'] (e : ι' → V) :
    zl ρ (Submodule.span (𝓞 K) (Set.range e)) =
      Submodule.span ℤ (Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
        ρ (integralBasis K p.1 • e p.2)) := by
  have hω : ∀ p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι',
      integralBasis K p.1 • e p.2 = (RingOfIntegers.basis K p.1) • e p.2 := fun p => by
    rw [integralBasis_apply, algebraMap_smul]
  have hspan : (Submodule.span (𝓞 K) (Set.range e)).restrictScalars ℤ =
      Submodule.span ℤ (Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
        integralBasis K p.1 • e p.2) := by
    rw [← Submodule.span_smul_of_span_eq_top (RingOfIntegers.basis K).span_eq (Set.range e),
      Set.range_smul_range]
    congr 1
    ext x
    simp only [Set.mem_range, hω]
  have hz : zl ρ (Submodule.span (𝓞 K) (Set.range e)) =
      ((Submodule.span (𝓞 K) (Set.range e)).restrictScalars ℤ).map ρ.toIntLinearMap := by
    ext x
    first
    | exact Iff.rfl
    | simp [zl]
  rw [hz, hspan, Submodule.map_span, ← Set.range_comp]
  rfl
end Formalism.HN.HeightGram
