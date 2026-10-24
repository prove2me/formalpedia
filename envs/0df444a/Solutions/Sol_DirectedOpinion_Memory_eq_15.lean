-- Prove2me | solution 1 for DirectedOpinion.Memory.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T03:31:04.516629+00:00
-- url     : https://prove2.me/submissions/4845a07e-ac8a-449a-bd71-1afc1fda541f

import Mathlib
import Definitions.Def_DirectedOpinion_Memory_Setting
import Theorems.Thm_DirectedOpinion_NoMemory_proposition_4

open MeasureTheory ProbabilityTheory DirectedOpinion.Memory

theorem solution {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (mk : DirectedOpinion.NoMemory.MarkFns M) (X : DirectedOpinion.NoMemory.Label → Ω → M)
    (U : DirectedOpinion.NoMemory.Label → ℕ → Ω → ℝ) (ζ : M → ℝ → ℝ) (c d : ℝ)
    (hGW : DirectedOpinion.NoMemory.GWModel P mk X U ζ c d) (hc : 0 < c) (hcd : c + d < 1)
    (hN0 : ∀ᵐ ω ∂P, 0 < mk.N (X [] ω)) (hN1 : ∀ᵐ ω ∂P, 0 < mk.N (X [0] ω)) :
    variance (RstarNoMem mk X U ζ c d) P =
      d ^ 2 / (c + d) ^ 2 * variance (DirectedOpinion.NoMemory.Z X U ζ [] 0) P
        + rho2star P mk X * d ^ 2 / ((c + d) ^ 2 * ((c + d) ^ 2 - DirectedOpinion.NoMemory.rho2 P mk X))
          * variance (DirectedOpinion.NoMemory.Z X U ζ [0] 0) P := by
  have hd : 0 < d := hGW.d_pos
  have hb : 0 < c + d := by linarith
  have hbne : c + d ≠ 0 := hb.ne'
  -- rescaled marks: weights 𝓒/(c+d) on the actual children, 0 elsewhere
  let mk' : DirectedOpinion.NoMemory.MarkFns M :=
    { N := mk.N
      C := fun x j => if j < mk.N x then mk.C x j / (c + d) else 0
      Q := mk.Q
      measurable_N := mk.measurable_N
      measurable_C := fun j => by
        refine Measurable.ite ?_ ((mk.measurable_C j).div_const _) measurable_const
        exact mk.measurable_N (MeasurableSet.of_discrete (s := {n : ℕ | j < n}))
      measurable_Q := mk.measurable_Q }
  have hCle : ∀ x j, j < mk.N x → mk.C x j ≤ c := by
    intro x j hj
    have hs := hGW.weights_sum x (by omega)
    rw [← hs]
    exact Finset.single_le_sum (f := fun j => mk.C x j)
      (fun i _ => hGW.weights_nonneg x i) (Finset.mem_range.mpr hj)
  have hsum' : ∀ x, ∑ j ∈ Finset.range (mk'.N x), mk'.C x j
      = (∑ j ∈ Finset.range (mk.N x), mk.C x j) / (c + d) := by
    intro x
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    simp [mk', Finset.mem_range.mp hj]
  have hsq' : ∀ x, ∑ j ∈ Finset.range (mk'.N x), mk'.C x j ^ 2
      = (∑ j ∈ Finset.range (mk.N x), mk.C x j ^ 2) / (c + d) ^ 2 := by
    intro x
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    simp [mk', Finset.mem_range.mp hj, div_pow]
  have hgw' : DirectedOpinion.NoMemory.GWModel P mk' X U ζ (c / (c + d)) (d / (c + d)) :=
    { c_nonneg := by positivity
      c_lt_one := by rw [div_lt_one hb]; linarith
      d_pos := by positivity
      d_le_one := by rw [div_le_one hb]; linarith
      cd_le_one := by rw [← add_div, div_self hbne]
      weights_nonneg := fun x j => by
        simp only [mk']
        split_ifs
        · exact div_nonneg (hGW.weights_nonneg x j) hb.le
        · exact le_rfl
      weights_le_one := fun x j => by
        simp only [mk']
        split_ifs with h
        · rw [div_le_one hb]; linarith [hCle x j h]
        · norm_num
      weights_sum := fun x hx => by
        rw [hsum', hGW.weights_sum x hx]
      Q_mem := hGW.Q_mem
      ζ_mem := hGW.ζ_mem
      measurable_ζ := hGW.measurable_ζ
      measurable_X := hGW.measurable_X
      measurable_U := hGW.measurable_U
      indep_marks := hGW.indep_marks
      ident_marks := hGW.ident_marks
      indep_unif := hGW.indep_unif
      unif := hGW.unif
      indep_marks_unif := hGW.indep_marks_unif }
  have h4 := (DirectedOpinion.NoMemory.proposition_4 P mk' X U ζ (c / (c + d)) (d / (c + d)) hgw'
    (by rw [← add_div, div_self hbne]) hN0 hN1).2
  -- the rescaled no-memory root opinion is 𝓡* of recursion (9)
  have hR : DirectedOpinion.NoMemory.Rstar mk' X U ζ (c / (c + d)) (d / (c + d))
      = RstarNoMem mk X U ζ c d := by
    funext ω
    unfold DirectedOpinion.NoMemory.Rstar RstarNoMem DirectedOpinion.NoMemory.rootOpinion
    have hlam : 1 - c / (c + d) - d / (c + d) = 0 := by field_simp; ring
    rw [hlam]
    have hop : DirectedOpinion.NoMemory.treeOp (fun i => mk'.N (X i ω)) (fun i j => mk'.C (X i ω) j) 0
        = DirectedOpinion.NoMemory.treeOp (nAt mk X ω) (fun i j => wAt mk X ω i j / (c + d)) 0 := by
      funext f i
      unfold DirectedOpinion.NoMemory.treeOp
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp [mk', nAt, wAt, Finset.mem_range.mp hj]
    have hsig : (fun s i => DirectedOpinion.NoMemory.W mk' X U ζ (c / (c + d)) (d / (c + d)) i s ω)
        = (fun s i => DirectedOpinion.NoMemory.W mk X U ζ c d i s ω / (c + d)) := by
      funext s i
      unfold DirectedOpinion.NoMemory.W
      rw [hsum']
      simp only [mk']
      field_simp
    rw [hop, hsig]
  have hρ2 : DirectedOpinion.NoMemory.rho2 P mk' X = DirectedOpinion.NoMemory.rho2 P mk X / (c + d) ^ 2 := by
    unfold DirectedOpinion.NoMemory.rho2
    rw [← integral_div]
    congr 1; funext ω; exact hsq' _
  have hρ2s : DirectedOpinion.NoMemory.rho2Star P mk' X = rho2star P mk X / (c + d) ^ 2 := by
    unfold DirectedOpinion.NoMemory.rho2Star rho2star sumC2
    rw [← integral_div]
    congr 1; funext ω; exact hsq' _
  -- ρ₂ ≤ c² < (c+d)²
  have hsq : ∀ x : M, ∑ j ∈ Finset.range (mk.N x), mk.C x j ^ 2 ≤ c ^ 2 := by
    intro x
    by_cases hN : 0 < mk.N x
    · have hs := hGW.weights_sum x hN
      calc ∑ j ∈ Finset.range (mk.N x), mk.C x j ^ 2
          ≤ ∑ j ∈ Finset.range (mk.N x), mk.C x j * c := by
            apply Finset.sum_le_sum
            intro j hj
            rw [sq]
            exact mul_le_mul_of_nonneg_left (hCle x j (Finset.mem_range.mp hj))
              (hGW.weights_nonneg x j)
        _ = c ^ 2 := by rw [← Finset.sum_mul, hs, sq]
    · have : mk.N x = 0 := by omega
      rw [this]; simp; positivity
  have hρ₂c : DirectedOpinion.NoMemory.rho2 P mk X ≤ c ^ 2 := by
    unfold DirectedOpinion.NoMemory.rho2
    calc ∫ ω, ∑ j ∈ Finset.range (mk.N (X [0] ω)), mk.C (X [0] ω) j ^ 2 ∂P
        ≤ ∫ _ω, c ^ 2 ∂P :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun j _ => sq_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall fun ω => hsq _)
      _ = c ^ 2 := by simp
  have hgap : 0 < (c + d) ^ 2 - DirectedOpinion.NoMemory.rho2 P mk X := by nlinarith
  rw [← hR, h4, hρ2, hρ2s]
  have hb2 : (c + d) ^ 2 ≠ 0 := by positivity
  have e1 : 1 - DirectedOpinion.NoMemory.rho2 P mk X / (c + d) ^ 2
      = ((c + d) ^ 2 - DirectedOpinion.NoMemory.rho2 P mk X) / (c + d) ^ 2 := by
    field_simp
  rw [e1]
  have := hgap.ne'
  field_simp
