-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.LatticeIndexBis.exists_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:35:26.844653+00:00
-- url     : https://prove2.me/submissions/bd934a92-5cd1-49f7-b223-6265e963a603

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeIndexBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.LatticeIndexBis
variable {O K V ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]
namespace Formalism.LatticeBaseChangeAlt.LatticeIndexBis
theorem _root_.solution [FiniteDimensional K V] (A : Submodule O V) (hA : A.FG) (U : Submodule K V)
    (hU : Submodule.span K (A : Set V) = U) :
    ∃ a : Fin (finrank K U) → V, LinearIndependent K a ∧ A = Submodule.span O (Set.range a) ∧
      Submodule.span K (Set.range a) = U := by
  classical
  haveI : NoZeroSMulDivisors O V := ⟨fun {o v} h => by
    rw [← algebraMap_smul K o v, smul_eq_zero] at h
    rcases h with h | h
    · left
      exact (IsFractionRing.injective O K) (by rw [h, map_zero])
    · right
      exact h⟩
  haveI : Module.Finite O A := Module.Finite.iff_fg.mpr hA
  haveI : Module.Free O A := Module.free_of_finite_type_torsion_free'
  let bA := Module.Free.chooseBasis O A
  let e : Module.Free.ChooseBasisIndex O A → V := fun i => (bA i : V)
  have hliO : LinearIndependent O e := bA.linearIndependent.map' A.subtype (Submodule.ker_subtype A)
  have hli : LinearIndependent K e := by
    first
    | exact (LinearIndependent.iff_fractionRing O K).1 hliO
    | exact LinearIndependent.iff_fractionRing.1 hliO
  have hAe : A = Submodule.span O (Set.range e) := by
    conv_lhs => rw [← Submodule.map_subtype_top A]
    rw [← bA.span_eq, Submodule.map_span, ← Set.range_comp] <;> rfl
  have hspan : Submodule.span K (Set.range e) = U := by
    calc Submodule.span K (Set.range e)
        = Submodule.span K (Submodule.span O (Set.range e) : Set V) :=
          (Submodule.span_span_of_tower O K _).symm
      _ = Submodule.span K (A : Set V) :=
          congrArg (fun s : Submodule O V => Submodule.span K (s : Set V)) hAe.symm
      _ = U := hU
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex O A) = Module.finrank K U := by
    rw [← hspan, finrank_span_eq_card hli]
  let σ := Fintype.equivFinOfCardEq hcard
  have hr : Set.range (e ∘ σ.symm) = Set.range e := by
    first
    | exact EquivLike.range_comp e σ.symm
    | exact Equiv.range_comp e σ.symm
    | rw [Set.range_comp, σ.symm.range_eq_univ, Set.image_univ]
  refine ⟨e ∘ σ.symm, hli.comp _ σ.symm.injective, ?_, ?_⟩
  · rw [hr]
    exact hAe
  · rw [hr]
    exact hspan
end Formalism.LatticeBaseChangeAlt.LatticeIndexBis
