-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.omega_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:16:02.64556+00:00
-- url     : https://prove2.me/submissions/3c386426-513e-4eeb-92ab-c4c48ff5bde7

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_XDXD
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_shiftW_self
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_cw_glAct
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_cw_WD
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_phiW_shift
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_cw_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_WS_eig
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eW_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eJ_cw_lt
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eJ_cw_diag
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_omega_formula
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
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (ρ : Fin r) (c : ℤ) (o : ℕ)
    (th : Fin r → ℤ) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hP : x ∈ Pol p r (setLast LL (o + 1)))
    (hF : x ∈ FreeOf p (Fin.last K, ρ)) (hx : x ∈ HWC p LL (K + 1) (univ.erase ρ) th) (β : Fin r → ℤ)
    (htop : ∀ γ, phiW β < phiW γ → cw p K γ x = 0) :
    cw p K β (Omega p LL c ρ x) = ((Enum ρ c o th β : ℤ) : ℚ_[p]) • cw p K β x := by
  have hterm : ∀ a ∈ univ.erase ρ, ∀ b ∈ univ.erase ρ, cw p K β (eW p K b a (glAct p LL K a b x)) =
      ((((if a = b then β a * (th a - β a) else 0) - (if a < b then (β a + 1) * β b else 0) : ℤ)) : ℚ_[p]) •
        cw p K β x := by
    intro a ha b hb
    rw [eW_apply, cw_WD, cw_glAct]
    rcases lt_trichotomy a b with hab | hab | hab
    · rw [eJ_cw_lt LL hv _ th x hx a b ha hb hab, if_neg (ne_of_lt hab), if_pos hab]
      have e1 : shiftW (shiftW β a b) b a = β := by funext c'; simp only [shiftW]; ring
      have hne : ((Fin.last K, a) : Fin (K + 1) × Fin r) ≠ (Fin.last K, b) :=
        fun h => (ne_of_lt hab) (Prod.mk.inj h).2
      rw [e1, map_neg, mul_neg, eW_apply,
        XDXD _ _ hne _ _ _ (WS_eig β _ (cw_mem β x) a) (WS_eig β _ (cw_mem β x) b), ← neg_smul]
      congr 1
      push_cast
      ring
    · subst hab
      rw [shiftW_self, eJ_cw_diag LL hv _ th x hx a ha, Derivation.map_smul, mul_smul_comm,
        WS_eig β _ (cw_mem β x) a, smul_smul, if_pos rfl, if_neg (lt_irrefl a)]
      congr 1
      push_cast
      ring
    · rw [htop (shiftW β a b) (by
        rw [phiW_shift]
        have : ((b : ℕ) : ℤ) < ((a : ℕ) : ℤ) := by exact_mod_cast hab
        omega), map_zero, map_zero, mul_zero, if_neg (ne_of_gt hab), if_neg (not_lt_of_gt hab)]
      simp
  rw [omega_formula LL ρ c o x hP hF, map_sub, map_smul, map_sum]
  simp only [map_sum]
  rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => hterm a ha b hb))]
  simp only [← Finset.sum_smul]
  rw [← sub_smul]
  congr 1
  unfold Enum
  push_cast
  rfl
end Formalism.InvariantFactorPaths.L4
