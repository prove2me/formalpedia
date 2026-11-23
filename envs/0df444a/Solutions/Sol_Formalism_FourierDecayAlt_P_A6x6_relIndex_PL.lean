-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.relIndex_PL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:56.387545+00:00
-- url     : https://prove2.me/submissions/a8fa4d59-22b6-4c6b-be91-a48dbde369a7

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_mem_PL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_ker_prj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x6
open Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {m : ℕ}
namespace Formalism.FourierDecayAlt.P.A6x6
theorem _root_.solution (Λ L : AddSubgroup K) :
    (PL Λ m).relIndex (PL L m) = Λ.relIndex L ^ m := by
  have e : ∀ y : Fin m → K ⧸ Λ, y ∈ (PL L m).map (prj Λ m) ↔
      ∀ i, y i ∈ L.map (QuotientAddGroup.mk' Λ) := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩ i
      exact ⟨x i, mem_PL.1 hx i, rfl⟩
    · intro h
      choose x hx hxy using h
      exact ⟨x, mem_PL.2 hx, funext hxy⟩
  rw [← ker_prj, AddSubgroup.relIndex_ker]
  have h2 : Λ.relIndex L = Nat.card (L.map (QuotientAddGroup.mk' Λ)) := by
    conv_lhs => rw [← QuotientAddGroup.ker_mk' Λ]
    exact AddSubgroup.relIndex_ker _ _
  rw [h2]
  have := Nat.card_congr ((Equiv.subtypeEquivRight e).trans
    (Equiv.subtypePiEquivPi (p := fun (_ : Fin m) (b : K ⧸ Λ) => b ∈ L.map (QuotientAddGroup.mk' Λ))))
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at this
  exact this
end Formalism.FourierDecayAlt.P.A6x6
