-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.rootStableExhaustion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:54.157165+00:00
-- url     : https://prove2.me/submissions/c35583d7-eadf-48fc-aea5-9070a82f740e

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_roots_finite
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_unitBox_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_unitBox_isCompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_unitBox_isOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.Exhaust := by
  intro K _ _ _ R ψ hD hn s hs
  have := hD.t2
  have := hD.artin
  have := hD.red
  obtain ⟨ϖ, hϖR, hϖ⟩ := hD.unif
  have hfin : {ζ : K | ζ ^ s = 1}.Finite := roots_finite s hs 1
  have hOm : ∀ j : ℕ, {z : K | ∀ ζ : K, ζ ^ s = 1 → ζ * z ∈ unitBox R ϖ j} =
      ⋂ ζ ∈ {ζ : K | ζ ^ s = 1}, (fun z => ζ * z) ⁻¹' unitBox R ϖ j := by
    intro j
    ext z
    simp only [Set.mem_iInter, Set.mem_preimage]
    rfl
  have hsub : ∀ j : ℕ, {z : K | ∀ ζ : K, ζ ^ s = 1 → ζ * z ∈ unitBox R ϖ j} ⊆ unitBox R ϖ j := by
    intro j z hz
    have := hz 1 (one_pow s)
    rwa [one_mul] at this
  refine ⟨fun j => {z : K | ∀ ζ : K, ζ ^ s = 1 → ζ * z ∈ unitBox R ϖ j}, ?_, ?_, ?_⟩
  · intro j
    refine ⟨?_, ?_, ?_, ?_⟩
    · beta_reduce
      rw [hOm]
      exact hfin.isOpen_biInter fun ζ _ =>
        (unitBox_isOpen hD hn ϖ hϖR hϖ j).preimage (continuous_const.mul continuous_id)
    · refine (unitBox_isCompact hD ϖ j).of_isClosed_subset ?_ (hsub j)
      beta_reduce
      rw [hOm]
      exact isClosed_biInter fun ζ _ =>
        (unitBox_isCompact hD ϖ j).isClosed.preimage (continuous_const.mul continuous_id)
    · intro z hz
      obtain ⟨y, hzy, _, _⟩ := hsub j hz
      exact IsUnit.of_mul_eq_one y hzy
    · intro z hz ζ hζ ζ' hζ'
      have := hz (ζ' * ζ) (by rw [mul_pow, hζ, hζ', one_mul])
      rwa [mul_assoc] at this
  · intro j z hz ζ hζ
    exact unitBox_mono ϖ hϖR (Nat.le_succ j) (hz ζ hζ)
  · intro z
    have h1 : ∀ ζ : K, ζ ^ s = 1 → ∃ j, ζ * (z : K) ∈ unitBox R ϖ j := by
      intro ζ hζ
      obtain ⟨m₁, h₁⟩ := hϖ (ζ * (z : K))
      obtain ⟨m₂, h₂⟩ := hϖ (ζ ^ (s - 1) * ((z⁻¹ : Kˣ) : K))
      refine ⟨max m₁ m₂, ζ ^ (s - 1) * ((z⁻¹ : Kˣ) : K), ?_, ?_, ?_⟩
      · have : ζ * ζ ^ (s - 1) = 1 := by
          rw [← pow_succ', Nat.sub_add_cancel hs, hζ]
        calc ζ * (z : K) * (ζ ^ (s - 1) * ((z⁻¹ : Kˣ) : K))
            = (ζ * ζ ^ (s - 1)) * ((z : K) * ((z⁻¹ : Kˣ) : K)) := by ring
          _ = 1 := by rw [this, Units.mul_inv, one_mul]
      · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (le_max_left m₁ m₂)
        rw [hk, pow_add, mul_comm ((ϖ : K) ^ m₁), mul_assoc]
        exact R.mul_mem (R.pow_mem hϖR _) h₁
      · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (le_max_right m₁ m₂)
        rw [hk, pow_add, mul_comm ((ϖ : K) ^ m₂), mul_assoc]
        exact R.mul_mem (R.pow_mem hϖR _) h₂
    choose! f hf using h1
    refine ⟨hfin.toFinset.sup f, ?_⟩
    intro ζ hζ
    exact unitBox_mono ϖ hϖR (Finset.le_sup (f := f) (hfin.mem_toFinset.2 hζ)) (hf ζ hζ)
end Formalism.FourierDecayAlt.P
