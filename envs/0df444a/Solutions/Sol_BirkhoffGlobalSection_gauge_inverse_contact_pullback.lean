-- Prove2me | solution 1 for BirkhoffGlobalSection.gauge_inverse_contact_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-30T18:30:15.459336+00:00
-- url     : https://prove2.me/submissions/541a3993-fba1-4a4a-a45a-202ecdaa4848

import Mathlib.Analysis.Convex.Gauge
import Theorems.Thm_BirkhoffGlobalSection_radial_rescaling_contact_pullback

open scoped ContDiff Topology
open BirkhoffGlobalSection Filter Set

/-- Inverse radial primitive pullback. The radial chart supplies its smoothness
input. This formula identifies the weighted standard sphere primitive, but
does not prove contact nondegeneracy or construct a complete Reeb flow. -/
theorem solution (B : Set Phase) (u v : Phase)
    (hu : u ∈ unitThreeSphere)
    (hG : ContDiffAt ℝ ∞ (fun x : Phase => (gauge B x)⁻¹ • x) u) :
    let G : Phase → Phase := fun x => (gauge B x)⁻¹ • x
    phaseRadialContact (G u) (fderiv ℝ G u v) =
      (zNormSq (G u) + wNormSq (G u)) * phaseRadialContact u v := by
  let a : Phase → ℝ := fun x => (gauge B x)⁻¹
  let G : Phase → Phase := fun x => a x • x
  have huQ : zNormSq u + wNormSq u = 1 := hu
  have hune : u ≠ 0 := by
    intro h
    simp [h, zNormSq, wNormSq] at huQ
  have hex : ∃ i : Fin 4, u i ≠ 0 := by
    by_contra! hz
    apply hune
    funext i
    exact hz i
  obtain ⟨i, hi⟩ := hex
  have hdG : DifferentiableAt ℝ G u := hG.differentiableAt (by simp)
  have hdcomp : DifferentiableAt ℝ (fun x => G x i) u := differentiableAt_pi.mp hdG i
  have hdcoord : DifferentiableAt ℝ (fun x : Phase => x i) u :=
    (hasFDerivAt_apply i u).differentiableAt
  have hratio : DifferentiableAt ℝ (fun x => G x i / x i) u := by
    convert! hdcomp.mul (hdcoord.inv hi) using 1
  have hne : ∀ᶠ x in 𝓝 u, x i ≠ 0 :=
    hdcoord.continuousAt.eventually (isOpen_compl_singleton.mem_nhds hi)
  have heq : a =ᶠ[𝓝 u] (fun x => G x i / x i) := by
    filter_upwards [hne] with x hx
    dsimp [G]
    simp [hx]
  have hda : DifferentiableAt ℝ a u := hratio.congr_of_eventuallyEq heq
  have hpull := radial_rescaling_contact_pullback a u v hda
  have hQ : zNormSq (G u) + wNormSq (G u) = (a u) ^ 2 := by
    change zNormSq (a u • u) + wNormSq (a u • u) = (a u) ^ 2
    have hscale : zNormSq (a u • u) + wNormSq (a u • u) =
        (a u) ^ 2 * (zNormSq u + wNormSq u) := by
      simp [zNormSq, wNormSq]
      ring
    rw [hscale, huQ, mul_one]
  change phaseRadialContact (G u) (fderiv ℝ G u v) =
    (zNormSq (G u) + wNormSq (G u)) * phaseRadialContact u v
  rw [hQ]
  exact hpull
