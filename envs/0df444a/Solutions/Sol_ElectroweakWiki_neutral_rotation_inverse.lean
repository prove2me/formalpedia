-- Prove2me | solution 1 for ElectroweakWiki.neutral_rotation_inverse
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T08:27:13.449119+00:00
-- url     : https://prove2.me/submissions/78d65315-8551-4c0f-bec3-a7e97e11260f

import Definitions.Def_ElectroweakWiki_defs

theorem solution (θ B W3 : ℝ) :
    B = Real.cos θ * ElectroweakWiki.photonField θ B W3 -
      Real.sin θ * ElectroweakWiki.zField θ B W3 ∧
    W3 = Real.sin θ * ElectroweakWiki.photonField θ B W3 +
      Real.cos θ * ElectroweakWiki.zField θ B W3 ∧
    ElectroweakWiki.photonField θ B W3 ^ 2 +
      ElectroweakWiki.zField θ B W3 ^ 2 = B ^ 2 + W3 ^ 2 := by
  have h : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  unfold ElectroweakWiki.photonField ElectroweakWiki.zField
  constructor
  · calc
      B = B * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by rw [h]; ring
      _ = _ := by ring
  constructor
  · calc
      W3 = W3 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by rw [h]; ring
      _ = _ := by ring
  · calc
      (Real.cos θ * B + Real.sin θ * W3) ^ 2 +
          (-Real.sin θ * B + Real.cos θ * W3) ^ 2 =
        (B ^ 2 + W3 ^ 2) * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
      _ = B ^ 2 + W3 ^ 2 := by rw [h]; ring

#print axioms solution
