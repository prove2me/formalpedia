-- Prove2me | solution 1 for Formalism.HC.Der.inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:19:37.689895+00:00
-- url     : https://prove2.me/submissions/4b9ca63a-fcf5-4509-bd5a-0ecce8b377fb

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Theorems.Thm_Formalism_HC_Der_tauN_inertia_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_HC_Der_cyc_isGalois
import Theorems.Thm_Formalism_HC_Der_exists_over
import Theorems.Thm_Formalism_HC_Der_gal_eq_art_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E), (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u := by
  intro l _ P _ _ σ
  have := cyc_isGalois H.condN
  obtain ⟨Q, _, _, h1, -⟩ := exists_over (emb H) l P
  rw [h1]
  constructor
  · rintro ⟨τ, h2, h3⟩
    obtain ⟨u, rfl⟩ := (tauN H.condN).surjective τ
    exact ⟨u, (tauN_inertia_iff _ l Q u).mp h3, (gal_eq_art_iff H σ u).mpr h2⟩
  · rintro ⟨u, h2, h3⟩
    exact ⟨_, (gal_eq_art_iff H σ u).mp h3, (tauN_inertia_iff _ l Q u).mpr h2⟩
end Formalism.HC.Der
