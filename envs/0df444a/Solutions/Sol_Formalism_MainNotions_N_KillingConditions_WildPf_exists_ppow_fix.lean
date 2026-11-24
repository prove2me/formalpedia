-- Prove2me | solution 1 for Formalism.MainNotions.N.KillingConditions.WildPf.exists_ppow_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:52.595049+00:00
-- url     : https://prove2.me/submissions/458a5c46-798a-4d06-bcc4-8080a50c30ca

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightVersion_Imports
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_WildPro
import Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_IsWild_pow
import Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_pow_fix
import Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_fix_of_coprime
import Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_exists_pow_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KillingConditions Formalism.MainNotions.N.KillingConditions.WildPf
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
variable {A}
namespace Formalism.MainNotions.N.KillingConditions.WildPf
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hpA : A.valuation ((p : ℕ) : Ω) < 1) {σ : Ω ≃ₐ[E] Ω} (hσ : IsWild A σ)
    (y : Ω) (hy : IsIntegral E y) : ∃ a : ℕ, ∀ k, a ≤ k → (σ ^ (p ^ k)) y = y := by
  obtain ⟨n, hn, hfix⟩ := exists_pow_fix σ y hy
  obtain ⟨a, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm
  have h1 : (σ ^ (p ^ a)) y = y := by
    refine fix_of_coprime hpA hcop (hσ.pow _) y ?_
    rw [← pow_mul]
    exact hfix
  refine ⟨a, fun k hk => ?_⟩
  have h2 : σ ^ (p ^ k) = (σ ^ (p ^ a)) ^ (p ^ (k - a)) := by
    rw [← pow_mul, ← pow_add]
    congr 2
    omega
  rw [h2]
  exact pow_fix h1 _
end Formalism.MainNotions.N.KillingConditions.WildPf
