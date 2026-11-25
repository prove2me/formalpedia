-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.restrictedLattice_exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:50:54.061639+00:00
-- url     : https://prove2.me/submissions/fb3b9c63-ab0a-4b53-9050-4bbdd616d9f1

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedLatticeDividedPower
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_compL_deg
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_compP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_initPart_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K : ℕ}
variable {r : ℕ} [NeZero r]
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (o : ℕ)
    (z : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hz : z ∈ M2 p LL J M ρ) (hzP : z ∈ Pol p r (setLast LL o)) :
    ∃ h ∈ Y p (setLast LL o) J M, h ∈ IntPol p (Fin (K + 1) × Fin r) ∧ initPart (Fin.last K, ρ) 0 h = z := by
  have hP : ∀ w ∈ M2 p LL J M ρ, ∃ h ∈ Y p (setLast LL o) J M, h ∈ IntPol p (Fin (K + 1) × Fin r) ∧
      initPart (Fin.last K, ρ) 0 h
        = compL ℚ_[p] (fun m : Fin (K + 1) × Fin r →₀ ℕ => ∑ a, m (Fin.last K, a) = o) w := by
    intro w hw
    unfold M2 at hw
    refine Submodule.iSup_induction _ (motive := fun w => ∃ h ∈ Y p (setLast LL o) J M,
      h ∈ IntPol p (Fin (K + 1) × Fin r) ∧ initPart (Fin.last K, ρ) 0 h
        = compL ℚ_[p] (fun m : Fin (K + 1) × Fin r →₀ ℕ => ∑ a, m (Fin.last K, a) = o) w) hw ?_ ?_ ?_
    · intro o' w' hw'
      obtain ⟨h', hh', rfl⟩ := Submodule.mem_map.1 hw'
      obtain ⟨hY', hI'⟩ := Submodule.mem_inf.1 hh'
      have hpol : h' ∈ Pol p r (setLast LL o') := (Submodule.mem_inf.1 hY').1
      have hcomm : compL ℚ_[p] (fun m : Fin (K + 1) × Fin r →₀ ℕ => ∑ a, m (Fin.last K, a) = o)
            (initPart (Fin.last K, ρ) 0 h')
          = initPart (Fin.last K, ρ) 0
            (compL ℚ_[p] (fun m : Fin (K + 1) × Fin r →₀ ℕ => ∑ a, m (Fin.last K, a) = o) h') := by
        ext m
        change MvPolynomial.coeff m (compP _ _) = MvPolynomial.coeff m (initPart _ _ (compP _ _))
        rw [coeff_compP, coeff_initPart, coeff_initPart, coeff_compP]
        split_ifs <;> rfl
      change ∃ h ∈ Y p (setLast LL o) J M, h ∈ IntPol p (Fin (K + 1) × Fin r) ∧
        initPart (Fin.last K, ρ) 0 h = compL ℚ_[p] (fun m : Fin (K + 1) × Fin r →₀ ℕ => ∑ a, m (Fin.last K, a) = o)
          (initPart (Fin.last K, ρ) 0 h')
      rw [hcomm, compL_deg LL o o' h' hpol]
      split_ifs with ho
      · subst ho
        exact ⟨h', hY', hI', rfl⟩
      · exact ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, rfl⟩
    · refine ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, ?_⟩
      rw [map_zero]
      exact (resL p (Fin.last K, ρ) 0).map_zero
    · rintro x y ⟨h1, hY1, hI1, e1⟩ ⟨h2, hY2, hI2, e2⟩
      exact ⟨h1 + h2, add_mem hY1 hY2, add_mem hI1 hI2, by rw [initPart_add, e1, e2, map_add]⟩
  obtain ⟨h, hY, hI, he⟩ := hP z hz
  refine ⟨h, hY, hI, ?_⟩
  rw [he, compL_deg LL o o z hzP, if_pos rfl]
end Formalism.InvariantFactorPaths.L4
