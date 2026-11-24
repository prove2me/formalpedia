-- Prove2me | solution 1 for Formalism.REAL.modularCharacter_eq_one_on_exp_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:19:00.728827+00:00
-- url     : https://prove2.me/submissions/1d44a554-0c53-45f1-9501-ffbe8df01bdb

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvolutionInvariants
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Theorems.Thm_Formalism_REAL_indefiniteUnitaryMk_val
import Theorems.Thm_Formalism_REAL_indefinite_unitary_ext
import Theorems.Thm_Formalism_REAL_modularCharacter_mul
import Theorems.Thm_Formalism_REAL_modularCharacter_one
import Theorems.Thm_Formalism_REAL_modularCharacter_eq_one_on_compact
import Theorems.Thm_Formalism_REAL_signature_mem_indefinite_unitary
import Theorems.Thm_Formalism_REAL_coeMatrix_inv_eq
import Theorems.Thm_Formalism_REAL_exp_conjTranspose_of_hermitian
import Theorems.Thm_Formalism_REAL_maximal_compact_facts
import Theorems.Thm_Formalism_REAL_parabolic_character_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped NNReal ENNReal
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (p : UJ ε) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inP ε X)
    (hp : ((p : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = NormedSpace.exp X) :
    modularCharacterAlt ε p = 1 := by
  set j := indefiniteUnitaryMk ε (Jm ε) (signature_mem_indefinite_unitary ε) with hj
  have hDj : modularCharacterAlt ε j = 1 := modularCharacter_eq_one_on_compact ε j (maximal_compact_facts n ε).2.2.1
  have hherm : (NormedSpace.exp X)ᴴ = NormedSpace.exp X :=
    exp_conjTranspose_of_hermitian (((parabolic_character_holds n ε X).1.mp hX).1)
  have hconj : j * p * j = p⁻¹ := by
    apply indefinite_unitary_ext
    have hinv := coeMatrix_inv_eq ε p
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
    rw [hinv, hj, indefiniteUnitaryMk_val]
    show Jm ε * _ * Jm ε = Jm ε * (coeMatrixAlt ε p)ᴴ * Jm ε
    rw [show coeMatrixAlt ε p = NormedSpace.exp X from hp, hp, hherm]
  have h1 : modularCharacterAlt ε p⁻¹ = modularCharacterAlt ε p := by
    rw [← hconj, modularCharacter_mul, modularCharacter_mul, hDj, one_mul, mul_one]
  have h2 : modularCharacterAlt ε p * modularCharacterAlt ε p = 1 := by
    rw [← modularCharacter_one ε, ← mul_inv_cancel p, modularCharacter_mul, h1]
  have h3 : ((modularCharacterAlt ε p : ℝ≥0) : ℝ) * (modularCharacterAlt ε p : ℝ) = 1 := by exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ (modularCharacterAlt ε p : ℝ) := (modularCharacterAlt ε p).2
  have h5 : ((modularCharacterAlt ε p : ℝ≥0) : ℝ) = 1 := by nlinarith
  exact_mod_cast h5
end Formalism.REAL
