-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:13.031869+00:00
-- url     : https://prove2.me/submissions/89395ac3-a024-4e3d-b331-10fc63b90fe5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_orderAt_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (I : X.IdealSheafData) (x : X) :
    orderAt I x = 1 ↔
      stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
        ¬ stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2 := by
  constructor
  · intro h
    constructor
    · have ha : ((1 : ℕ) : ℕ∞) ≤ orderAt I x := by rw [h]; simp
      simpa using (le_orderAt_iff I x 1).mp ha
    · intro hle
      have h2 := (le_orderAt_iff I x 2).mpr hle
      rw [h] at h2
      have h3 : (2 : ℕ) ≤ 1 := by exact_mod_cast h2
      omega
  · rintro ⟨ha, hb⟩
    have ha' : ((1 : ℕ) : ℕ∞) ≤ orderAt I x := (le_orderAt_iff I x 1).mpr (by simpa using ha)
    have hb' : ¬ ((2 : ℕ) : ℕ∞) ≤ orderAt I x := fun hc => hb ((le_orderAt_iff I x 2).mp hc)
    rcases eq_or_ne (orderAt I x) ⊤ with htop | hfin
    · exact absurd (htop ▸ le_top) hb'
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
      rw [← hn] at ha' hb' ⊢
      have hn1 : 1 ≤ n := by exact_mod_cast ha'
      have hn2 : ¬ (2 ≤ n) := fun hc => hb' (by exact_mod_cast hc)
      have hn3 : n = 1 := by omega
      rw [hn3, Nat.cast_one]
end FunctorialResolution.EmbeddedResolution
