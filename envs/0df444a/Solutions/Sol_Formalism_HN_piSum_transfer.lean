-- Prove2me | solution 1 for Formalism.HN.piSum_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:11.041848+00:00
-- url     : https://prove2.me/submissions/b21c644e-d41a-41d3-b418-cd3405a62d83

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly
import Theorems.Thm_Formalism_HN_piSum_emb_apply
import Theorems.Thm_Formalism_HN_piSum_emb_inner
import Theorems.Thm_Formalism_HN_piSum_emb_injective
import Theorems.Thm_Formalism_F_covol_eq_of_linearEquiv_inner


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
open Formalism Formalism.HN
variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
variable (ρ : ∀ i, V i →+ E i)
variable [∀ i, FiniteDimensional ℝ (E i)]
namespace Formalism.HN
theorem _root_.solution (i : ι) (M : Submodule ℤ (E i)) [DiscreteTopology M] :
    DiscreteTopology (M.map ((piSum_emb E i).restrictScalars ℤ)) ∧
    Formalism.F.rk (M.map ((piSum_emb E i).restrictScalars ℤ)) = Formalism.F.rk M ∧
    Formalism.F.covol (M.map ((piSum_emb E i).restrictScalars ℤ)) = Formalism.F.covol M := by
  have hfi : Function.Injective ((piSum_emb E i).restrictScalars ℤ) := piSum_emb_injective i
  let e := Submodule.equivMapOfInjective _ hfi M
  have he : ∀ x : M, ((e x : M.map ((piSum_emb E i).restrictScalars ℤ)) : PiLp 2 E) =
      piSum_emb E i x := by
    intro x
    rfl
  have key : ∀ y : M.map ((piSum_emb E i).restrictScalars ℤ),
      ((e.symm y : M) : E i) = (y : PiLp 2 E) i := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [LinearEquiv.symm_apply_apply]
    rw [he, piSum_emb_apply, Pi.single_eq_same]
  have hcoord : Continuous fun y : M.map ((piSum_emb E i).restrictScalars ℤ) => (y : PiLp 2 E) i := by
    exact (PiLp.continuous_apply 2 E i).comp continuous_subtype_val
  have hc : Continuous fun y : M.map ((piSum_emb E i).restrictScalars ℤ) => e.symm y :=
    continuous_induced_rng.2 (hcoord.congr fun y => (key y).symm)
  have hdisc : DiscreteTopology (M.map ((piSum_emb E i).restrictScalars ℤ)) := by
    exact DiscreteTopology.of_continuous_injective hc e.symm.injective
  refine ⟨hdisc, ?_, ?_⟩
  · exact (LinearEquiv.finrank_eq e).symm
  · refine Formalism.F.covol_eq_of_linearEquiv_inner M _ e fun x y => ?_
    rw [he, he]
    exact piSum_emb_inner i (x : E i) (y : E i)
end Formalism.HN
