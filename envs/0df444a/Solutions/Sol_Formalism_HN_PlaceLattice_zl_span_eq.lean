-- Prove2me | solution 1 for Formalism.HN.PlaceLattice.zl_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:30:33.333804+00:00
-- url     : https://prove2.me/submissions/0c72968d-21de-4679-95f9-4d2a3d140fe0

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
variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HN.PlaceLattice
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (ρ : V →+ E) {ι' : Type} [Fintype ι'] (e : ι' → V) :
    zl ρ (Submodule.span (𝓞 K) (Set.range e)) =
      Submodule.span ℤ (Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
        ρ (integralBasis K p.1 • e p.2)) := by
  have hs : Submodule.span ℤ (Set.range (RingOfIntegers.basis K)) = ⊤ := (RingOfIntegers.basis K).span_eq
  have h1 := Submodule.span_smul_of_span_eq_top hs (Set.range e)
  open Pointwise in
  have hset : Set.range (RingOfIntegers.basis K) • Set.range e =
      Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' => integralBasis K p.1 • e p.2 := by
    ext x
    simp only [Set.mem_smul, Set.mem_range, Prod.exists, integralBasis_apply, algebraMap_smul]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      exact ⟨i, j, rfl⟩
    · rintro ⟨i, j, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
  rw [hset] at h1
  have h2 : Submodule.span ℤ (Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
      ρ (integralBasis K p.1 • e p.2)) =
      (Submodule.span ℤ (Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
        integralBasis K p.1 • e p.2)).map ρ.toIntLinearMap := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [h2, h1]
  ext x
  exact Iff.rfl
end Formalism.HN.PlaceLattice
