-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.eproj_Y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:06.161552+00:00
-- url     : https://prove2.me/submissions/4608baf1-fef2-4ab0-966b-beb57be9ef91

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eproj_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eproj_pol
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eproj_ycond
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_min


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (e1 : ℕ) (hHP : HypP p LL ρ e1)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL N ρ w PE) :
    ∀ h ∈ Y p LL J M, h ∈ WtSpC p LL N univ w → PE h ∈ MMw p LL J M ρ w := by
  intro h hh hW
  obtain ⟨hhP, hhY⟩ := Submodule.mem_inf.mp hh
  rw [Submodule.mem_iInf] at hhY
  obtain ⟨hA, hB⟩ := Submodule.mem_inf.mp (eproj_mem LL N ρ w PE hPE h)
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr
    ⟨eproj_pol LL N ρ w PE hPE h hhP hW, ?_⟩, hA⟩, hB⟩
  rw [Submodule.mem_iInf]
  intro k
  obtain ⟨P, hP, -, -⟩ := hHP.1 (min (J k) N) (min_le_right _ _) univ (Or.inl rfl)
    {la | ((la 0 : ℤ) : WithTop ℤ) ≤ M k} (fun la la' hl => by
      show (((la 0 : ℤ) : WithTop ℤ) ≤ M k) ↔ (((la' 0 : ℤ) : WithTop ℤ) ≤ M k)
      rw [hl 0 (Finset.mem_univ 0)])
  have hk := hhY k
  rw [ycond_min] at hk ⊢
  exact eproj_ycond LL _ N (min_le_right _ _) ρ w PE hPE (M k) P hP h (Submodule.mem_inf.mpr ⟨hk, hhP⟩) hW
end Formalism.InvariantFactorPaths.L4
