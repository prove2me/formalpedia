-- Prove2me | solution 1 for EdenVerified.p23_kaplanYorkeDimension_radiusPair_bound_and_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:36:44.280919+00:00
-- url     : https://prove2.me/submissions/ba47cebc-c252-4bca-9d97-ff6e2a4c26af

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_kaplanYorkeDimension_radiusPair_bound_and_eq


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c s₁ s₂ : ℝ} (hc : 4 < c)
    (hs₁ : s₁ = 0 ∨ s₁ = 1 ∨ s₁ = 2) (hs₂ : s₂ = 0 ∨ s₂ = 1 ∨ s₂ = 2),
    kaplanYorkeDimension (descending (radiusPairSpectrum c s₁ s₂)) ≤ targetDimension c ∧
      (kaplanYorkeDimension (descending (radiusPairSpectrum c s₁ s₂)) = targetDimension c ↔
        s₁ = 1 ∧ s₂ = 1) :=
  @Eden.kaplanYorkeDimension_radiusPair_bound_and_eq
end EdenVerified
