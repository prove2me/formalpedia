-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx3.t_PoissonJoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:00.624843+00:00
-- url     : https://prove2.me/submissions/25c9a007-74d8-470d-81aa-f1094608a31c

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3
open Formalism.H MeasureTheory
open scoped FourierTransform
namespace Formalism.FourierDecayAlt.P.Jx3
theorem _root_.solution : PoissonJoint := by
  intro h0 V _ _ _ _ _ ι _ π hπ Λ _ _ E _ emb dmap La Lad φ Cφ nh hinj hLa hd0 hcov hc hdec hpos hnh t₀ B hB S hS
  classical
  set F : V → ℂ := 𝓕 (fun v => (φ v : ℂ)) with hF
  have hcv : 0 < ZLattice.covolume Λ := ZLattice.covolume_pos Λ volume
  choose σ hσL hσ using fun μ : dual Λ => hcov μ.1 μ.2
  have hσinj : Function.Injective σ := fun a b h => Subtype.ext (by rw [← hσ a, ← hσ b, h])
  have hσ0 : ∀ μ : dual Λ, μ ≠ 0 → σ μ ≠ 0 := by
    intro μ hμ h; apply hμ; apply Subtype.ext; rw [← hσ μ, h, hd0]; rfl
  have hnorm : ∀ μ : dual Λ, ‖nh (σ μ)‖ = (ZLattice.covolume Λ)⁻¹ * ‖F μ‖ := by
    intro μ; rw [hnh, hσ, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hcv.le]
  have hfin : ∀ T : Finset {μ : dual Λ // μ ≠ 0},
      ∑ μ ∈ T, ‖F (μ : dual Λ)‖ ≤ ZLattice.covolume Λ * B := by
    intro T
    have := hB (T.image (fun μ => σ μ.1)) (by
      intro l hl; obtain ⟨μ, _, rfl⟩ := Finset.mem_image.1 hl; exact ⟨hσL _, hσ0 _ μ.2⟩)
    rw [Finset.sum_image (fun a _ b _ h => Subtype.ext (hσinj h))] at this
    simp_rw [hnorm, ← Finset.mul_sum] at this
    rwa [inv_mul_le_iff₀ hcv] at this
  have hsum' : Summable (fun μ : {μ : dual Λ // μ ≠ 0} => ‖F (μ : dual Λ)‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) hfin
  have hts : ∑' μ : {μ : dual Λ // μ ≠ 0}, ‖F (μ : dual Λ)‖ ≤ ZLattice.covolume Λ * B :=
    hsum'.tsum_le_of_sum_le hfin
  have hsum : Summable (fun μ : dual Λ => ‖F μ‖) := by
    refine (Finset.summable_compl_iff ({0} : Finset (dual Λ))).1 ?_
    have e : {x : dual Λ // x ∉ ({0} : Finset (dual Λ))} ≃ {μ : dual Λ // μ ≠ 0} :=
      Equiv.subtypeEquivRight (fun x => by simp)
    refine (summable_of_sum_le (fun _ => norm_nonneg _) (c := ZLattice.covolume Λ * B) ?_)
    intro T
    have := hfin (T.map ⟨fun x => ⟨x.1, by simpa using x.2⟩, fun a b h => by
      have := congrArg (fun z => z.1) h; exact Subtype.ext this⟩)
    rw [Finset.sum_map] at this
    exact this
  obtain ⟨_, hP⟩ := h0 V ι π hπ Λ φ Cφ (emb t₀) hc hdec hsum (fun l => hpos _)
  have hmem : ∀ t ∈ S, emb (t - t₀) ∈ Λ := fun t ht => hLa _ (hS t ht)
  let S' : Finset Λ := S.attach.image (fun t => ⟨emb (t.1 - t₀), hmem t.1 t.2⟩)
  have h1 : ∑ t ∈ S, φ (emb t) = ∑ l ∈ S', φ ((l : V) + emb t₀) := by
    rw [Finset.sum_image]
    · rw [← Finset.sum_attach]; refine Finset.sum_congr rfl (fun t _ => ?_); simp [map_sub]
    · intro a _ b _ h
      have h2 : emb (a.1 - t₀) = emb (b.1 - t₀) := congrArg Subtype.val h
      have h3 := hinj h2
      exact Subtype.ext (by simpa using h3)
  rw [h1]
  refine (hP S').trans ?_
  unfold F7.poissonBound
  have hre : (F 0).re ≤ ‖F 0‖ := Complex.re_le_norm _
  have hn0 : ‖nh 0‖ = (ZLattice.covolume Λ)⁻¹ * ‖F 0‖ := by
    rw [hnh, hd0, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hcv.le]
  rw [hn0, mul_add]
  refine add_le_add (mul_le_mul_of_nonneg_left hre (inv_nonneg.2 hcv.le)) ?_
  rw [inv_mul_le_iff₀ hcv]
  exact hts
end Formalism.FourierDecayAlt.P.Jx3
