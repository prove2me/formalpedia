-- Prove2me | solution 1 for Formalism.ZF.exists_factorization_of_sum_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:42:11.898012+00:00
-- url     : https://prove2.me/submissions/4852ca32-25cd-4768-a9ab-19840fcf86dc

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZeroFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Set Filter Topology
noncomputable section
namespace Formalism.ZF
private theorem closedBall_mem_nhds_of_mem_closedBall_lt {z₀ z : ℂ} {r R₁ : ℝ} (hR : R₁ < r)
    (hz : z ∈ Metric.closedBall z₀ R₁) : Metric.closedBall z₀ r ∈ 𝓝 z :=
  Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds (Metric.closedBall_subset_ball hR hz))
    Metric.ball_subset_closedBall
private theorem natCast_analyticOrderNatAt_of_ne_top {f : ℂ → ℂ} {z : ℂ}
    (h : analyticOrderAt f z ≠ ⊤) : ((analyticOrderNatAt f z : ℕ) : ℕ∞) = analyticOrderAt f z :=
  ENat.natCast_toNat h
end Formalism.ZF
end
end

set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution (z₀ : ℂ) (r R₁ : ℝ) (hR : R₁ < r) :
    ∀ N : ℕ, ∀ (f : ℂ → ℂ) (Z : Finset ℂ), DifferentiableOn ℂ f (Metric.closedBall z₀ r) →
      (∀ ρ ∈ Z, ρ ∈ Metric.closedBall z₀ R₁) →
      (∀ z ∈ Metric.closedBall z₀ R₁, f z = 0 → z ∈ Z) →
      (∀ ρ ∈ Z, analyticOrderAt f ρ ≠ ⊤) →
      ∑ ρ ∈ Z, analyticOrderNatAt f ρ = N →
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.closedBall z₀ r) ∧
        (∀ z ∈ Metric.closedBall z₀ R₁, h z ≠ 0) ∧
        ∀ z ∈ Metric.closedBall z₀ r, f z = (∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ) * h z := by
  classical
  intro N
  induction N with
  | zero =>
    intro f Z hf hZ hzero htop hsum
    have h0 : ∀ ρ ∈ Z, analyticOrderNatAt f ρ = 0 := Finset.sum_eq_zero_iff.mp hsum
    refine ⟨f, hf, ?_, ?_⟩
    · intro z hz hfz
      have hzZ := hzero z hz hfz
      have han : AnalyticAt ℂ f z := hf.analyticAt (closedBall_mem_nhds_of_mem_closedBall_lt hR hz)
      have hord : analyticOrderAt f z = 0 := by
        rw [← natCast_analyticOrderNatAt_of_ne_top (htop z hzZ)]
        simp [h0 z hzZ]
      exact (han.analyticOrderAt_eq_zero.mp hord) hfz
    · intro z _
      rw [Finset.prod_eq_one (fun ρ hρ => by rw [h0 ρ hρ, pow_zero]), one_mul]
  | succ n ih =>
    intro f Z hf hZ hzero htop hsum
    obtain ⟨ρ₀, hρ₀Z, hρ₀⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact Nat.succ_ne_zero n)
    have hρ₀B := hZ ρ₀ hρ₀Z
    have hanρ₀ : AnalyticAt ℂ f ρ₀ := hf.analyticAt (closedBall_mem_nhds_of_mem_closedBall_lt hR hρ₀B)
    have hfρ₀ : f ρ₀ = 0 := by
      by_contra hne
      apply hρ₀
      have h0 : analyticOrderAt f ρ₀ = 0 := hanρ₀.analyticOrderAt_eq_zero.mpr hne
      simp [analyticOrderNatAt, h0]
    obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = dslope f ρ₀ := ⟨_, rfl⟩
    have hfg : ∀ z, f z = (z - ρ₀) * g z := by
      intro z
      have h := sub_smul_dslope f ρ₀ z
      rw [hfρ₀, sub_zero, smul_eq_mul, ← hg] at h
      exact h.symm
    have hgd : DifferentiableOn ℂ g (Metric.closedBall z₀ r) := by
      rw [hg]
      exact (Complex.differentiableOn_dslope (closedBall_mem_nhds_of_mem_closedBall_lt hR hρ₀B)).mpr hf
    have hfeq : f = (fun z : ℂ => z - ρ₀) * g := funext fun z => hfg z
    have key : ∀ ρ ∈ Z,
        analyticOrderAt f ρ = (if ρ = ρ₀ then 1 else 0) + analyticOrderAt g ρ := by
      intro ρ hρ
      have hB := hZ ρ hρ
      have hga : AnalyticAt ℂ g ρ := hgd.analyticAt (closedBall_mem_nhds_of_mem_closedBall_lt hR hB)
      have hla : AnalyticAt ℂ (fun z : ℂ => z - ρ₀) ρ := analyticAt_id.sub analyticAt_const
      rw [hfeq, analyticOrderAt_mul hla hga]
      congr 1
      split_ifs with hρρ₀
      · rw [hρρ₀]
        have hl : AnalyticAt ℂ (fun z : ℂ => z - ρ₀) ρ₀ := analyticAt_id.sub analyticAt_const
        have h1 := (hl.analyticOrderAt_eq_natCast (n := 1)).mpr
          ⟨fun _ => 1, analyticAt_const, one_ne_zero, Filter.Eventually.of_forall fun z => by simp⟩
        simpa using h1
      · exact hla.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hρρ₀)
    have keyN : ∀ ρ ∈ Z,
        analyticOrderNatAt f ρ = (if ρ = ρ₀ then 1 else 0) + analyticOrderNatAt g ρ ∧
          analyticOrderAt g ρ ≠ ⊤ := by
      intro ρ hρ
      have hk := key ρ hρ
      have ht := htop ρ hρ
      have hgt : analyticOrderAt g ρ ≠ ⊤ := by
        intro h
        apply ht
        rw [hk, h]
        simp
      refine ⟨?_, hgt⟩
      have h1 : ((analyticOrderNatAt f ρ : ℕ) : ℕ∞) =
          (((if ρ = ρ₀ then 1 else 0) + analyticOrderNatAt g ρ : ℕ) : ℕ∞) := by
        rw [natCast_analyticOrderNatAt_of_ne_top ht, hk, Nat.cast_add,
          natCast_analyticOrderNatAt_of_ne_top hgt]
        split_ifs <;> simp
      exact_mod_cast h1
    have hsumg : ∑ ρ ∈ Z, analyticOrderNatAt g ρ = n := by
      have hs : ∑ ρ ∈ Z, analyticOrderNatAt f ρ =
          ∑ ρ ∈ Z, ((if ρ = ρ₀ then 1 else 0) + analyticOrderNatAt g ρ) :=
        Finset.sum_congr rfl fun ρ hρ => (keyN ρ hρ).1
      rw [hs, Finset.sum_add_distrib] at hsum
      simp only [Finset.sum_ite_eq', hρ₀Z, if_true] at hsum
      omega
    have hzg : ∀ z ∈ Metric.closedBall z₀ R₁, g z = 0 → z ∈ Z :=
      fun z hz h0 => hzero z hz (by rw [hfg z, h0, mul_zero])
    obtain ⟨h, hhd, hh0, hhf⟩ := ih g Z hgd hZ hzg (fun ρ hρ => (keyN ρ hρ).2) hsumg
    refine ⟨h, hhd, hh0, fun z hz => ?_⟩
    have hone : ∏ ρ ∈ Z, (z - ρ) ^ (if ρ = ρ₀ then 1 else 0) = z - ρ₀ := by
      rw [Finset.prod_eq_single ρ₀ (fun b _ hb => by simp [hb]) (fun h => absurd hρ₀Z h)]
      simp
    have hprod : ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ =
        (z - ρ₀) * ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt g ρ := by
      calc ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ
          = ∏ ρ ∈ Z, ((z - ρ) ^ (if ρ = ρ₀ then 1 else 0) * (z - ρ) ^ analyticOrderNatAt g ρ) :=
            Finset.prod_congr rfl fun ρ hρ => by rw [(keyN ρ hρ).1, pow_add]
        _ = (z - ρ₀) * ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt g ρ := by
            rw [Finset.prod_mul_distrib, hone]
    rw [hfg z, hhf z hz, hprod, mul_assoc]
end Formalism.ZF
