-- Prove2me | solution 1 for EdenVerified.p22_descending_radiusPairSpectrum_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:33:46.692582+00:00
-- url     : https://prove2.me/submissions/902cdfc6-87df-4745-866b-840bbb16541e

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_descending_radiusPairSpectrum_swap


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c s₁ s₂ : ℝ),
    descending (radiusPairSpectrum c s₁ s₂) = descending (radiusPairSpectrum c s₂ s₁) :=
  @Eden.descending_radiusPairSpectrum_swap
end EdenVerified
