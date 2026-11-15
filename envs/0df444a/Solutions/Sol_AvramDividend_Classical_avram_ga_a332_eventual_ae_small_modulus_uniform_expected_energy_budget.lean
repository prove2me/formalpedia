-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a332_eventual_ae_small_modulus_uniform_expected_energy_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:37:14.54524+00:00
-- url     : https://prove2.me/submissions/0a40d352-1eac-480d-9139-f7e8069a8984

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Small : ℝ → ℕ → Ω → ℝ)
    (E A B : ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hSI : ∀ δ, 0 < δ → ∀ m,
      Integrable (fun ω => max (Small δ m ω) 0) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hAI : ∀ m, Integrable (A m) P)
    (hBI : ∀ m, Integrable (B m) P)
    (hEB : ∀ m, (∫ ω, E m ω ∂P) ≤ K)
    (hAL : Tendsto (fun m => ∫ ω, A m ω ∂P)
      atTop (𝓝 (0:ℝ)))
    (hBL : Tendsto (fun m => ∫ ω, B m ω ∂P)
      atTop (𝓝 (0:ℝ)))
    (hMod : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∃ k : ℕ,
      ∀ m : ℕ, k ≤ m →
        ∀ᵐ ω ∂P,
          max (Small δ m ω) 0 ≤
            ε*E m ω+A m ω+B m ω) :
    ∀ η, 0 < η → ∃ δ, 0 < δ ∧ ∃ k : ℕ,
      ∀ m : ℕ, k ≤ m →
        (∫ ω, max (Small δ m ω) 0 ∂P) ≤ η := by
  intro η hη
  let ε : ℝ := η/(4*(K+1))
  have hKpos : (0 : ℝ) < K+1 := by linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨δ,hδ,k0,hMod0⟩ := hMod ε hε
  have hεB : ε*K ≤ η/4 := by
    have hprod : ε*K ≤ ε*(K+1) :=
      mul_le_mul_of_nonneg_left (by linarith : K ≤ K+1) hε.le
    have hEq : ε*(K+1) = η/4 := by
      dsimp [ε]
      field_simp
    linarith
  have hSum : Tendsto (fun m : ℕ =>
      (∫ ω, A m ω ∂P)+(∫ ω, B m ω ∂P))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using hAL.add hBL
  have hSmall : ∀ᶠ m : ℕ in atTop,
      (∫ ω, A m ω ∂P)+(∫ ω, B m ω ∂P) < η/2 :=
    hSum.eventually (isOpen_Iio.mem_nhds (by linarith : (0:ℝ)<η/2))
  have hAll : ∀ᶠ m : ℕ in atTop,
      k0 ≤ m ∧
        (∫ ω, A m ω ∂P)+(∫ ω, B m ω ∂P) < η/2 :=
    (eventually_ge_atTop k0).and hSmall
  obtain ⟨k,hk⟩ := Filter.eventually_atTop.1 hAll
  refine ⟨δ,hδ,k,?_⟩
  intro m hkm
  obtain ⟨hm0,hAB⟩ := hk m hkm
  have hMajor : Integrable
      (fun ω => ε*E m ω+A m ω+B m ω) P :=
    (((hEI m).const_mul ε).add (hAI m)).add (hBI m)
  have hCompare := integral_mono_ae (hSI δ hδ m) hMajor
    (hMod0 m hm0)
  have hUpper :
      (∫ ω, max (Small δ m ω) 0 ∂P) ≤
        ε*(∫ ω, E m ω ∂P)+
        (∫ ω, A m ω ∂P)+(∫ ω, B m ω ∂P) := by
    have hEq :
      (∫ ω, ε*E m ω+A m ω+B m ω ∂P) =
        ε*(∫ ω, E m ω ∂P)+
        (∫ ω, A m ω ∂P)+(∫ ω, B m ω ∂P) := by
      have h1 :
          (∫ ω, ε*E m ω + A m ω ∂P) =
            ε*(∫ ω, E m ω ∂P) +
            (∫ ω, A m ω ∂P) := by
        simpa only [integral_const_mul] using
          (integral_add ((hEI m).const_mul ε) (hAI m))
      have h2 :
          (∫ ω, ε*E m ω + A m ω + B m ω ∂P) =
            (∫ ω, ε*E m ω + A m ω ∂P) +
            (∫ ω, B m ω ∂P) := by
        exact integral_add (((hEI m).const_mul ε).add (hAI m)) (hBI m)
      rw [h2,h1]
    exact hCompare.trans_eq hEq
  have hEnergy := mul_le_mul_of_nonneg_left (hEB m) hε.le
  linarith
