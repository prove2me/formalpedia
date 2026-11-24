-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.path_basis_of_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:29:25.156588+00:00
-- url     : https://prove2.me/submissions/299f6c45-fdc3-4c64-abbf-75b5fafc5155

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_MinorDeterminantBasis_basis_of
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_MinorDeterminantBasis_psi_map
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_MinorDeterminantBasis_psi_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open MinorDeterminantBasis
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : LemmaA2indep → PathIdxFinite → PolBRank → PathBasisOfCount := by
  classical
  intro hA hF hR n N isVec B hC R _
  haveI := hF n N isVec B
  letI := Fintype.ofFinite (PathIdx n N isVec B)
  obtain ⟨hcard, hfin, hspan⟩ := hR n N B
  haveI : Finite (expSet n N B) := hfin.to_subtype
  have hce : Nat.card (PathIdx n N isVec B) = Nat.card (expSet n N B) := by
    rw [hC, Nat.card_coe_set_eq, ← hcard]
    rfl
  obtain ⟨e⟩ := Finite.card_eq.mp hce
  let m : PathIdx n N isVec B → ℕ × Fin n →₀ ℕ := fun x => (e x : ℕ × Fin n →₀ ℕ)
  have hm : Function.Injective m := Subtype.val_injective.comp e.injective
  have hFs : ∀ x : PathIdx n N isVec B, ∀ d ∈ (psiPath ℤ isVec x.1.1 N x.1.2).support,
      d ∈ Set.range m := by
    intro x d hd
    have h1 := psi_support hR x.2.1 x.2.2.2.1 d hd
    exact ⟨e.symm ⟨d, h1⟩, by simp [m]⟩
  have hfun : ∀ (S : Type) [CommRing S], (fun x : PathIdx n N isVec B =>
      MvPolynomial.map (Int.castRingHom S) (psiPath ℤ isVec x.1.1 N x.1.2)) =
      fun x => psiPath S isVec x.1.1 N x.1.2 := fun S _ =>
    funext fun x => (psi_map S x.2.1 x.2.2.2.1).symm
  have hp : ∀ p : ℕ, ∀ _ : Fact p.Prime, LinearIndependent (ZMod p) fun x : PathIdx n N isVec B =>
      MvPolynomial.map (Int.castRingHom (ZMod p)) (psiPath ℤ isVec x.1.1 N x.1.2) := by
    intro p hpp
    rw [hfun]
    exact hA (ZMod p) n N isVec B
  obtain ⟨h1, h2⟩ := basis_of m hm (fun x => psiPath ℤ isVec x.1.1 N x.1.2) hFs hp R
  rw [hfun] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  rw [hspan R]
  congr 1
  ext f
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨m y, (e y).2, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨e.symm ⟨d, hd⟩, by simp [m]⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
