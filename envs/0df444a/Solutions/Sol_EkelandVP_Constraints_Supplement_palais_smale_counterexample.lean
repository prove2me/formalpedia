-- Prove2me | solution 1 for EkelandVP.Constraints.Supplement.palais_smale_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:21:30.277428+00:00
-- url     : https://prove2.me/submissions/02a67212-688f-4a9e-94ce-bdf96b2fc304

import Mathlib
import Definitions.Def_EkelandVP_Constraints_Supplement_riemannianManifold
import Definitions.Def_EkelandVP_Constraints_Supplement_conditionC
set_option autoImplicit false

open Manifold Bundle
open scoped ContDiff Bundle

open EkelandVP
open EkelandVP.Constraints
open EkelandVP.Constraints.Supplement

/-- Counterexample on the full printed domain: a countable disjoint union of points.
A compatible intrinsic extended metric has distance +∞ between distinct components. -/
theorem solution :
    ∃ (D : CompleteStrongRiemannian.{0}) (e : D.M ≃ₜ ℕ) (F : D.M → ℝ),
      (∀ x, F x = componentValue (e x)) ∧
      ContMDiff 𝓘(ℝ, D.H) 𝓘(ℝ) 1 F ∧
      (∀ x, differentialNorm D F x = 0) ∧
      ConditionC F (differentialNorm D F) ∧
      (∀ x, 0 < F x) ∧ IsGLB (Set.range F) 0 ∧
      ¬ (∃ x, ∀ y, F x ≤ F y) := by
        classical
        letI : ChartedSpace PUnit.{1} ℕ := ChartedSpace.ofDiscreteTopology
        letI : IsManifold 𝓘(ℝ, PUnit.{1}) ∞ ℕ := IsManifold.of_discreteTopology ∞
        have ht (x : ℕ) : Subsingleton (TangentSpace 𝓘(ℝ, PUnit.{1}) x) :=
          inferInstanceAs (Subsingleton PUnit.{1})
        let g : ContMDiffRiemannianMetric 𝓘(ℝ, PUnit.{1}) ∞ PUnit.{1}
            (fun x : ℕ => TangentSpace 𝓘(ℝ, PUnit.{1}) x) := {
          inner := fun _ => 0
          symm := by intros; rfl
          pos := by
            intro x v hv
            exact (hv ((ht x).elim _ _)).elim
          isVonNBounded := by
            intro x
            letI := ht x
            exact Bornology.IsVonNBounded.of_subsingleton
          contMDiff := contMDiff_of_discreteTopology }
        letI : RiemannianBundle (fun x : ℕ => TangentSpace 𝓘(ℝ, PUnit.{1}) x) :=
          ⟨g.toRiemannianMetric⟩
        letI : IsContMDiffRiemannianBundle 𝓘(ℝ, PUnit.{1}) ∞ PUnit.{1}
            (fun x : ℕ => TangentSpace 𝓘(ℝ, PUnit.{1}) x) := inferInstance
        letI : IsContinuousRiemannianBundle PUnit.{1}
            (fun x : ℕ => TangentSpace 𝓘(ℝ, PUnit.{1}) x) :=
          ⟨fun _ => 0, continuous_of_discreteTopology, by intros; rfl⟩
        letI em : EMetricSpace ℕ := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, PUnit.{1}) ℕ
        letI : UniformSpace ℕ := em.toUniformSpace
        letI : IsRiemannianManifold 𝓘(ℝ, PUnit.{1}) ℕ := ⟨fun _ _ => rfl⟩
        have hd (x y : ℕ) (hxy : x ≠ y) : edist x y = ⊤ := by
          change riemannianEDist 𝓘(ℝ, PUnit.{1}) x y = ⊤
          rw [riemannianEDist]
          apply iInf_eq_top.mpr
          intro p
          have hp : x = y := by
            have h := TotallyDisconnectedSpace.eq_of_continuous p p.continuous 0 1
            simpa using h
          exact (hxy hp).elim
        letI : DiscreteUniformity ℕ := by
          apply discreteUniformity_iff_setRelId_mem_uniformity.mpr
          apply Filter.mem_of_superset (edist_mem_uniformity (α := ℕ) (by norm_num : (0 : ENNReal) < 1))
          intro p hp
          change p.1 = p.2
          by_contra h
          simpa [hd _ _ h] using hp
        letI hc : CompleteSpace ℕ := inferInstance
        let D : CompleteStrongRiemannian := { H := PUnit.{1}, M := ℕ, emetricM := em, completeM := hc }
        let e : D.M ≃ₜ ℕ := Homeomorph.refl ℕ
        refine ⟨D, e, componentValue, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x; rfl
        · exact contMDiff_of_discreteTopology
        · intro x
          unfold differentialNorm
          have h : mfderiv 𝓘(ℝ, D.H) 𝓘(ℝ) componentValue x = 0 := by
            ext v
            have hv : v = 0 := (ht x).elim _ _
            simp [hv]
          simp only [h, ContinuousLinearMap.opNorm_zero]
        · intro S hB hδ
          have hS : S.Nonempty := by
            by_contra h
            apply hδ
            refine ⟨1, zero_lt_one, ?_⟩
            intro x hx
            exact (h ⟨x, hx⟩).elim
          obtain ⟨p, hp⟩ := hS
          refine ⟨p, subset_closure hp, ?_⟩
          unfold differentialNorm
          have h : mfderiv 𝓘(ℝ, D.H) 𝓘(ℝ) componentValue p = 0 := by
            ext v
            have hv : v = 0 := (ht p).elim _ _
            simp [hv]
          simp only [h, ContinuousLinearMap.opNorm_zero]
        · intro n
          unfold componentValue
          positivity
        · constructor
          · rintro _ ⟨n, rfl⟩
            unfold componentValue
            positivity
          · intro b hb
            by_contra h
            have hbpos : 0 < b := lt_of_not_ge h
            obtain ⟨n, hn⟩ := exists_nat_gt (1 / b)
            have hbn := hb (Set.mem_range_self n)
            unfold componentValue at hbn
            have hnpos : (0 : ℝ) < n + 1 := by positivity
            have hlt : 1 / (n + 1 : ℝ) < b := by
              apply (div_lt_iff₀ hnpos).mpr
              have hn' : 1 / b < (n : ℝ) + 1 := by linarith
              have := (div_lt_iff₀ hbpos).mp hn'
              nlinarith
            exact (not_lt_of_ge hbn) hlt
        · rintro ⟨n, hn⟩
          have h := hn (n + 1)
          change 1 / (n + 1 : ℝ) ≤ 1 / ((n + 1 : ℕ) + 1 : ℝ) at h
          have hp : (0 : ℝ) < n + 1 := by positivity
          have hq : (n + 1 : ℝ) < (n + 1 : ℕ) + 1 := by push_cast; linarith
          exact (not_le_of_gt (one_div_lt_one_div_of_lt hp hq)) h
