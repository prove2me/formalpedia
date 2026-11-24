-- Prove2me | solution 1 for Formalism.HC.Frame.thick_part_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:20:36.641933+00:00
-- url     : https://prove2.me/submissions/a566ad0f-5a9c-4043-953d-2bbef14215ec

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_thick_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
open Classical
namespace Formalism.HC.Frame
theorem _root_.solution {L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < φ.n0) (hR : NoRel T L)
    (u₀ t x : φ.A) (hord : 4 * L < addOrderOf x) (i₀ : ℤ) :
    ((Finset.Ico i₀ (i₀ + L)).filter (fun i : ℤ => φ.InTranslate T u₀ (t + i • x))).card ≤ 2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card.1 hcon
  rw [Finset.mem_filter] at hp hq hr
  have K : ∀ a b c : ℤ, a ∈ Finset.Ico i₀ (i₀ + L) → b ∈ Finset.Ico i₀ (i₀ + L) →
      c ∈ Finset.Ico i₀ (i₀ + L) → a < b → b < c → φ.InTranslate T u₀ (t + a • x) →
      φ.InTranslate T u₀ (t + b • x) → φ.InTranslate T u₀ (t + c • x) → False :=
    fun a b c ha _ hc hab hbc hxa hxb hxc =>
      φ.thick_key T hT hR u₀ t x hord i₀ a b c ha hc hab hbc hxa hxb hxc
  rcases lt_or_gt_of_ne hpq with h1 | h1 <;> rcases lt_or_gt_of_ne hpr with h2 | h2 <;>
    rcases lt_or_gt_of_ne hqr with h3 | h3 <;>
    first
    | omega
    | exact K p q r hp.1 hq.1 hr.1 (by omega) (by omega) hp.2 hq.2 hr.2
    | exact K p r q hp.1 hr.1 hq.1 (by omega) (by omega) hp.2 hr.2 hq.2
    | exact K q p r hq.1 hp.1 hr.1 (by omega) (by omega) hq.2 hp.2 hr.2
    | exact K q r p hq.1 hr.1 hp.1 (by omega) (by omega) hq.2 hr.2 hp.2
    | exact K r p q hr.1 hp.1 hq.1 (by omega) (by omega) hr.2 hp.2 hq.2
    | exact K r q p hr.1 hq.1 hp.1 (by omega) (by omega) hr.2 hq.2 hp.2
end Formalism.HC.Frame
