-- Prove2me | solution 1 for DirectedOpinion.Memory.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T03:28:02.1207+00:00
-- url     : https://prove2.me/submissions/34ca69b5-aa6b-44b4-980d-b84bbb55ba33

import Mathlib
import Definitions.Def_DirectedOpinion_Memory_Setting
import Theorems.Thm_DirectedOpinion_Memory_remark_10_2
import Theorems.Thm_DirectedOpinion_Memory_eq_15
import Theorems.Thm_DirectedOpinion_Memory_coefficient_bound

open MeasureTheory ProbabilityTheory DirectedOpinion.Memory

theorem solution {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (mk : DirectedOpinion.NoMemory.MarkFns M) (X : DirectedOpinion.NoMemory.Label → Ω → M)
    (U : DirectedOpinion.NoMemory.Label → ℕ → Ω → ℝ) (ζ : M → ℝ → ℝ) (c d : ℝ)
    (hGW : DirectedOpinion.NoMemory.GWModel P mk X U ζ c d) (hc : 0 < c) (hcd : c + d < 1)
    (hN0 : ∀ᵐ ω ∂P, 0 < mk.N (X [] ω)) (hN1 : ∀ᵐ ω ∂P, 0 < mk.N (X [0] ω)) :
    variance (Mstar mk X U ζ c d) P ≤ variance (RstarNoMem mk X U ζ c d) P := by
  have hd : 0 < d := hGW.d_pos
  obtain ⟨_, hV⟩ := remark_10_2 P mk X U ζ c d hGW hN0 hN1
  have hR := eq_15 P mk X U ζ c d hGW hc hcd hN0 hN1
  -- bounds on ρ₂ and ρ*₂
  have hsq : ∀ x : M, ∑ j ∈ Finset.range (mk.N x), mk.C x j ^ 2 ≤ c ^ 2 := by
    intro x
    by_cases hN : 0 < mk.N x
    · have hs := hGW.weights_sum x hN
      calc ∑ j ∈ Finset.range (mk.N x), mk.C x j ^ 2
          ≤ ∑ j ∈ Finset.range (mk.N x), mk.C x j * c := by
            apply Finset.sum_le_sum
            intro j hj
            have h0 := hGW.weights_nonneg x j
            have h1 : mk.C x j ≤ c := by
              rw [← hs]
              exact Finset.single_le_sum (f := fun j => mk.C x j)
                (fun i _ => hGW.weights_nonneg x i) hj
            rw [sq]; exact mul_le_mul_of_nonneg_left h1 h0
        _ = c ^ 2 := by rw [← Finset.sum_mul, hs, sq]
    · have : mk.N x = 0 := by omega
      rw [this]; simp; positivity
  have hρ₂0 : 0 ≤ DirectedOpinion.NoMemory.rho2 P mk X := by
    unfold DirectedOpinion.NoMemory.rho2
    exact integral_nonneg fun ω => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hρ₂c : DirectedOpinion.NoMemory.rho2 P mk X ≤ c ^ 2 := by
    unfold DirectedOpinion.NoMemory.rho2
    calc ∫ ω, ∑ j ∈ Finset.range (mk.N (X [0] ω)), mk.C (X [0] ω) j ^ 2 ∂P
        ≤ ∫ _ω, c ^ 2 ∂P :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun j _ => sq_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall fun ω => hsq _)
      _ = c ^ 2 := by simp
  have hρ₂s : 0 ≤ rho2star P mk X := by
    unfold rho2star sumC2
    exact integral_nonneg fun ω => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hcv : ∀ i, 0 ≤ ∫ ω, condVarSig P X (DirectedOpinion.NoMemory.Z X U ζ) i ω ∂P := by
    intro i
    apply integral_nonneg_of_ae
    unfold condVarSig condVar
    apply condExp_nonneg
    exact Filter.Eventually.of_forall fun ω => by
      simp only [Pi.zero_apply, Pi.pow_apply]; exact sq_nonneg _
  obtain ⟨_, _, hcoef⟩ := coefficient_bound c d (DirectedOpinion.NoMemory.rho2 P mk X) hc hd hcd
    hρ₂0 hρ₂c
  have h3 : 2 * d ^ 2 * (c + d - 1) / ((c + d) ^ 2 * (2 - (c + d)))
      * ∫ ω, condVarSig P X (DirectedOpinion.NoMemory.Z X U ζ) [] ω ∂P ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ (hcv [])
    apply div_nonpos_of_nonpos_of_nonneg
    · have : c + d - 1 ≤ 0 := by linarith
      have : 0 ≤ 2 * d ^ 2 := by positivity
      nlinarith
    · have : 0 ≤ 2 - (c + d) := by linarith
      positivity
  have h4 : d ^ 2 * rho2star P mk X
      * (1 / (1 - DirectedOpinion.NoMemory.rho2 P mk X)
          * geomExp (DirectedOpinion.NoMemory.rho2 P mk X)
            (fun k => ((c + d) ^ (2 * (k + 2)))⁻¹ * pT c d (k + 1))
        - 1 / ((c + d) ^ 2 * ((c + d) ^ 2 - DirectedOpinion.NoMemory.rho2 P mk X)))
      * ∫ ω, condVarSig P X (DirectedOpinion.NoMemory.Z X U ζ) [0] ω ∂P ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ (hcv [0])
    apply mul_nonpos_of_nonneg_of_nonpos _ hcoef
    positivity
  have e : d ^ 2 * rho2star P mk X / ((c + d) ^ 2 * ((c + d) ^ 2 - DirectedOpinion.NoMemory.rho2 P mk X))
      = rho2star P mk X * d ^ 2 / ((c + d) ^ 2 * ((c + d) ^ 2 - DirectedOpinion.NoMemory.rho2 P mk X)) := by
    ring
  rw [hV, hR, e]
  linarith
