-- Prove2me | solution 1 for Formalism.REAL.compact_integration_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:29:37.723876+00:00
-- url     : https://prove2.me/submissions/9d1e9659-96f5-4dfd-86a9-e99d454688b8

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactHaarRightInvariantInst
import Theorems.Thm_Formalism_REAL_group_exponential_facts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory MeasureTheory.Measure
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : KByParts := by
  intro n ε E _ _ _ F D Z hZ hF hD hder
  haveI : IsMulRightInvariant (muK ε) := ⟨fun g => compact_haar_right_invariant n ε g⟩
  haveI : IsProbabilityMeasure (muK ε) := compact_haar_probability n ε
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    TopologicalSpace.secondCountableTopology_induced _ _ MulOpposite.unop
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    TopologicalSpace.secondCountableTopology_induced _ _ (Units.embedProduct _)
  haveI : SecondCountableTopology (UJ ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (UJ ε : Set (Matrix (Fin n) (Fin n) ℂ)ˣ)
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))
  obtain ⟨h0, hadd, -, hKf⟩ := group_exponential_facts n ε Z hZ.1
  obtain ⟨hk, -⟩ := hKf hZ
  have hhom : ∀ s t : ℝ, expK ε Z (s + t) = expK ε Z s * expK ε Z t := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, hk, hk, hk, hadd]
  have hzero : expK ε Z 0 = 1 := by
    apply Subtype.ext
    exact (hk 0).trans h0
  have hderiv : ∀ (k : KG ε) (t : ℝ),
      HasDerivAt (fun s => F (k * expK ε Z s)) (D (k * expK ε Z t)) t := by
    intro k t
    have h := hder (k * expK ε Z t)
    rw [← sub_self t] at h
    have e : (fun s => F (k * expK ε Z s)) = fun s => F (k * expK ε Z t * expK ε Z (s - t)) := by
      funext s
      rw [mul_assoc, ← hhom, add_sub_cancel]
    rw [e]
    exact h.comp_sub_const t t
  obtain ⟨C, hC⟩ : ∃ C, ∀ y : KG ε, ‖D y‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_univ.image hD.norm).bddAbove
    exact ⟨C, fun y => hC ⟨y, Set.mem_univ _, rfl⟩⟩
  obtain ⟨CF, hCF⟩ : ∃ C, ∀ y : KG ε, ‖F y‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_univ.image hF.norm).bddAbove
    exact ⟨C, fun y => hC ⟨y, Set.mem_univ _, rfl⟩⟩
  have hcomp : ∀ t : ℝ, Continuous (fun k : KG ε => k * expK ε Z t) := fun t =>
    continuous_id.mul continuous_const
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muK ε) (x₀ := (0 : ℝ))
    (F := fun t k => F (k * expK ε Z t)) (F' := fun t k => D (k * expK ε Z t))
    (bound := fun _ => C) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hF.comp (hcomp t)).aestronglyMeasurable)
    (Integrable.mono' (integrable_const CF) (hF.comp (hcomp 0)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => hCF _))
    (hD.comp (hcomp 0)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k t _ => hC _)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k t _ => hderiv k t)
  have hconst : (fun t : ℝ => ∫ k, F (k * expK ε Z t) ∂(muK ε)) = fun _ => ∫ k, F k ∂(muK ε) := by
    funext t
    exact integral_mul_right_eq_self F (expK ε Z t)
  have h2 : HasDerivAt (fun _ : ℝ => ∫ k, F k ∂(muK ε)) (∫ k, D (k * expK ε Z 0) ∂(muK ε)) 0 := by
    rw [← hconst]
    exact key.2
  have h3 := h2.unique (hasDerivAt_const (0 : ℝ) (∫ k, F k ∂(muK ε)))
  simp only [hzero, mul_one] at h3
  exact h3
end Formalism.REAL
