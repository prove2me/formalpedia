-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.graded_eq_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:51:12.188205+00:00
-- url     : https://prove2.me/submissions/21a1e9ce-9d82-48a3-b35a-8250f2b4f5cb

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_initPart_pow_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_grMap_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_filtration_eq_holds
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : GrEq := by
  intro p _ K r _ LLw q J M ρ w e hv he x
  have hset : (initPart (Fin.last K, ρ) e '' (FilE p LLw J M ρ w (Fin.last K, ρ) e :
      Set (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]))) =
      ((MMwZ p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e)).map
        (grMap p (Fin.last K, ρ) e) : Set (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) := by
    ext y
    simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_map, grMap_apply]
    constructor
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨h, hh, rfl⟩ := (filtration_eq_holds p K r LLw J M ρ w e hv he f).mp hf
      exact ⟨h, hh, (initPart_pow_mul _ e h).symm⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨X (Fin.last K, ρ) ^ e * h,
        (filtration_eq_holds p K r LLw J M ρ w e hv he _).mpr ⟨h, hh, rfl⟩, initPart_pow_mul _ e h⟩
  unfold grLat
  rw [hset, Submodule.span_eq]
  simp only [Submodule.mem_map, grMap_apply]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
end Formalism.InvariantFactorPaths.L4
