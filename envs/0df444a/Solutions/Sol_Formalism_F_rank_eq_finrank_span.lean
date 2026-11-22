-- Prove2me | solution 1 for Formalism.F.rank_eq_finrank_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:34.095612+00:00
-- url     : https://prove2.me/submissions/cd1cf2ed-a532-438e-b551-0f1de2407098

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeInequality
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SaturationProperties

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
    [FiniteDimensional ℝ E] (N : Submodule ℤ E) [hN : DiscreteTopology N] :
    rk N = finrank ℝ (span ℝ (N : Set E)) := by

  let V := span ℝ (N : Set E)
  let N' : Submodule ℤ V := N.comap (V.subtype.restrictScalars ℤ)
  let φ : N' ≃ₗ[ℤ] N :=
    { toFun := fun x => ⟨((x : V) : E), x.2⟩
      invFun := fun y => ⟨⟨y, Submodule.subset_span y.2⟩, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : DiscreteTopology N' :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : N' => (⟨((x : V) : E), x.2⟩ : N))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b h => by
        have h' := congrArg Subtype.val h
        simp only at h'
        exact Subtype.ext (Subtype.ext h'))
  haveI : IsZLattice ℝ N' := ⟨Submodule.span_span_coe_preimage⟩
  exact φ.finrank_eq.symm.trans (ZLattice.rank ℝ N')
end Formalism.F
