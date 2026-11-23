-- Prove2me | solution 1 for Formalism.F.linearIndependent_coe_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:44.038376+00:00
-- url     : https://prove2.me/submissions/5375a9e2-d415-42b1-b584-84e49c98bfd9

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
namespace Formalism.F
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hL : DiscreteTopology L] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (b i : E)) := by
  classical

  let V : Submodule ℝ E := Submodule.span ℝ (L : Set E)
  let L' : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let φ : L ≃ₗ[ℤ] L' :=
    { toFun := fun x => ⟨⟨x, Submodule.subset_span x.2⟩, x.2⟩
      invFun := fun y => ⟨((y : V) : E), y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : DiscreteTopology L' :=
    DiscreteTopology.of_continuous_injective (f := fun y : L' => (⟨((y : V) : E), y.2⟩ : L))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (by
        intro a c h
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h'))
  haveI : IsZLattice ℝ L' := ⟨by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    show Submodule.span ℝ _ = Submodule.span ℝ (L : Set E)
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩⟩
  have hrank := ZLattice.rank ℝ L'
  have hLspan : Submodule.span ℤ (Set.range fun i => (b i : E)) = L := by
    have h1 := congrArg (Submodule.map L.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h1
    exact h1
  have key : Fintype.card ι = Module.finrank ℝ V := by
    rw [← hrank, ← φ.finrank_eq, Module.finrank_eq_card_basis b]
  rw [linearIndependent_iff_card_eq_finrank_span]
  show Fintype.card ι = Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => (b i : E)))
  rw [← Submodule.span_span_of_tower ℤ ℝ, hLspan]
  exact key
end Formalism.F
