-- Prove2me | solution 1 for BirkhoffGlobalSection.gauge_inverse_contact_weight
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-30T19:51:30.582556+00:00
-- url     : https://prove2.me/submissions/3d00424b-f644-4d54-b520-566ff11c25e9

import Mathlib.Analysis.Convex.Gauge
import Theorems.Thm_BirkhoffGlobalSection_gauge_inverse_contact_pullback

open scoped ContDiff Topology
open BirkhoffGlobalSection Set

private theorem gauge_inverse_weight_pos (B : Set Phase) (h0 : B ∈ 𝓝 (0 : Phase))
    (hb : Bornology.IsVonNBounded ℝ B) (u : Phase) (hu : u ∈ unitThreeSphere) :
    0 < zNormSq ((gauge B u)⁻¹ • u) + wNormSq ((gauge B u)⁻¹ • u) := by
  have hQ : zNormSq u + wNormSq u = 1 := hu
  have hune : u ≠ 0 := by
    intro h
    simp [h, zNormSq, wNormSq] at hQ
  have hg : 0 < gauge B u := (gauge_pos (absorbent_nhds_zero h0) hb).2 hune
  have hscale : zNormSq ((gauge B u)⁻¹ • u) + wNormSq ((gauge B u)⁻¹ • u) =
      ((gauge B u)⁻¹) ^ 2 * (zNormSq u + wNormSq u) := by
    simp [zNormSq, wNormSq]
    ring
  rw [hscale, hQ, mul_one]
  exact sq_pos_of_pos (inv_pos.mpr hg)

theorem solution (B : Set Phase) (h0 : B ∈ 𝓝 (0 : Phase))
    (hb : Bornology.IsVonNBounded ℝ B) (u : Phase) (hu : u ∈ unitThreeSphere)
    (hG : ContDiffAt ℝ ∞ (fun x : Phase => (gauge B x)⁻¹ • x) u) :
    let G : Phase → Phase := fun x => (gauge B x)⁻¹ • x
    let f : Phase → ℝ := fun x => zNormSq (G x) + wNormSq (G x)
    0 < f u ∧ ContDiffAt ℝ ∞ f u ∧
      (∀ v : Phase, phaseRadialContact (G u) (fderiv ℝ G u v) =
        f u * phaseRadialContact u v) := by
  dsimp only
  refine ⟨gauge_inverse_weight_pos B h0 hb u hu, ?_, ?_⟩
  · have hcoord (i : Fin 4) := contDiffAt_pi.mp hG i
    exact ((hcoord 0).pow 2 |>.add ((hcoord 1).pow 2)).add
      (((hcoord 2).pow 2).add ((hcoord 3).pow 2))
  · intro v
    exact gauge_inverse_contact_pullback B u v hu hG
