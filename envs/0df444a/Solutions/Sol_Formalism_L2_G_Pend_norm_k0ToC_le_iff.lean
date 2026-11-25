-- Prove2me | solution 1 for Formalism.L2.G.Pend.norm_k0ToC_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:12:23.758821+00:00
-- url     : https://prove2.me/submissions/7c3224be-f90a-425f-9262-bb9918580804

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_IsLocalRingOfComplete
import Definitions.Def_Lemmata_FirstBlockLemmaF_Imports
import Definitions.Def_Lemmata_GeneralBFactThird_Imports
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PendingLemmas_WittFractionToCpAlgebraMap
import Theorems.Thm_Formalism_L2_G_Pend_norm_wToC_le
import Theorems.Thm_Formalism_L2_G_Pend_witt_fraction_to_Cp_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing Filter Topology
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Pend
variable (p : ℕ) [hp : Fact p.Prime]
attribute [local instance] algZW algQK
attribute [local instance] Formalism.L2.G.Pend.towerZQK
namespace Formalism.L2.G.Pend
theorem _root_.solution (x : K0 p) : ‖k0ToC p x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap (WW p) (K0 p)) := by
  constructor
  · intro h
    by_cases hx0 : x = 0
    · exact ⟨0, by rw [map_zero, hx0]⟩
    rcases ValuationRing.isInteger_or_isInteger (WW p) x with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact ⟨c, hc⟩
    · by_cases hu : IsUnit c
      · obtain ⟨u, rfl⟩ := hu
        exact ⟨((u⁻¹ : (WW p)ˣ) : WW p), by rw [map_units_inv (algebraMap (WW p) (K0 p)), hc, inv_inv]⟩
      · exfalso
        have hcm : c ∈ maximalIdeal (WW p) := (mem_maximalIdeal c).2 hu
        rw [(WittVector.irreducible p).maximalIdeal_eq, Ideal.mem_span_singleton] at hcm
        obtain ⟨d, rfl⟩ := hcm
        have h1 : ‖k0ToC p x⁻¹‖ ≤ (p : ℝ)⁻¹ := by
          rw [← hc, witt_fraction_to_Cp_algebraMap, map_mul, map_natCast, norm_mul, norm_p_C]
          exact mul_le_of_le_one_right (r_nonneg p) (norm_wToC_le p d)
        have hne : k0ToC p x ≠ 0 := (map_ne_zero (k0ToC p)).2 hx0
        rw [map_inv₀, norm_inv] at h1
        have h2 : 1 ≤ ‖k0ToC p x‖⁻¹ := (one_le_inv₀ (norm_pos_iff.2 hne)).2 h
        exact absurd (h2.trans h1) (not_le.2 (r_lt_one p))
  · rintro ⟨y, rfl⟩
    rw [witt_fraction_to_Cp_algebraMap]
    exact norm_wToC_le p y
end Formalism.L2.G.Pend
