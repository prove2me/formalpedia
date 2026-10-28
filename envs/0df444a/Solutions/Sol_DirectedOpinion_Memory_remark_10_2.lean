-- Prove2me | solution 1 for DirectedOpinion.Memory.remark_10_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T03:35:17.095998+00:00
-- url     : https://prove2.me/submissions/209fe913-5bf7-49bb-a669-e04c7bde7e1e

import Mathlib
import Definitions.Def_DirectedOpinion_Memory_Setting
import Theorems.Thm_DirectedOpinion_Memory_theorem_8

open MeasureTheory ProbabilityTheory DirectedOpinion.Memory

theorem solution {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (mk : DirectedOpinion.NoMemory.MarkFns M) (X : DirectedOpinion.NoMemory.Label → Ω → M)
    (U : DirectedOpinion.NoMemory.Label → ℕ → Ω → ℝ) (ζ : M → ℝ → ℝ) (c d : ℝ)
    (hGW : DirectedOpinion.NoMemory.GWModel P mk X U ζ c d)
    (hN0 : ∀ᵐ ω ∂P, 0 < mk.N (X [] ω)) (hN1 : ∀ᵐ ω ∂P, 0 < mk.N (X [0] ω)) :
    let ρ₁s := rho1star P mk X
    let ρ₁ := rho1 P mk X
    let ρ₂s := rho2star P mk X
    let ρ₂ := DirectedOpinion.NoMemory.rho2 P mk X
    let Rstar := Mstar mk X U ζ c d
    (∫ ω, Rstar ω ∂P
      = d / (c + d) * ∫ ω, DirectedOpinion.NoMemory.Z X U ζ [] 0 ω ∂P
        + d * ρ₁s / ((c + d - ρ₁) * (c + d)) * ∫ ω, DirectedOpinion.NoMemory.Z X U ζ [0] 0 ω ∂P) ∧
    variance Rstar P
      = d ^ 2 / (c + d) ^ 2 * variance (DirectedOpinion.NoMemory.Z X U ζ [] 0) P
        + d ^ 2 * ρ₂s / ((c + d) ^ 2 * ((c + d) ^ 2 - ρ₂)) * variance (DirectedOpinion.NoMemory.Z X U ζ [0] 0) P
        + 2 * d ^ 2 * (c + d - 1) / ((c + d) ^ 2 * (2 - (c + d)))
          * ∫ ω, condVarSig P X (DirectedOpinion.NoMemory.Z X U ζ) [] ω ∂P
        + d ^ 2 * ρ₂s
          * (1 / (1 - ρ₂) * geomExp ρ₂ (fun k => ((c + d) ^ (2 * (k + 2)))⁻¹ * pT c d (k + 1))
            - 1 / ((c + d) ^ 2 * ((c + d) ^ 2 - ρ₂)))
          * ∫ ω, condVarSig P X (DirectedOpinion.NoMemory.Z X U ζ) [0] ω ∂P := by
  intro ρ₁s ρ₁ ρ₂s ρ₂ Rstar
  have hd : 0 < d := hGW.d_pos
  have hc0 : 0 ≤ c := hGW.c_nonneg
  have hb : 0 < c + d := by linarith
  have hb1 : c + d ≤ 1 := hGW.cd_le_one
  set sC : M → ℝ := fun x => ∑ j ∈ Finset.range (mk.N x), mk.C x j with hsC
  have hsC_meas : Measurable sC := by
    have : Measurable (fun p : M × ℕ => ∑ j ∈ Finset.range p.2, mk.C p.1 j) :=
      measurable_from_prod_countable_left fun n =>
        Finset.measurable_sum (Finset.range n) fun j _ => mk.measurable_C j
    exact this.comp (measurable_id.prodMk mk.measurable_N)
  have hsC_le : ∀ x, sC x ≤ c := by
    intro x
    by_cases hN : 0 < mk.N x
    · exact (hGW.weights_sum x hN).le
    · have : mk.N x = 0 := by omega
      simp [hsC, this, hc0]
  have hsC_nn : ∀ x, 0 ≤ sC x := fun x => Finset.sum_nonneg fun j _ => hGW.weights_nonneg x j
  -- the general signal ξ = d ζ + Q (c − Σ𝓒)
  let ξ : M → ℝ → ℝ := fun x u => d * ζ x u + mk.Q x * (c - sC x)
  have hξb : ∀ x u, |ξ x u| ≤ d + c - sC x := by
    intro x u
    have h1 := hGW.ζ_mem x u
    have h2 := hGW.Q_mem x
    have h3 := hsC_le x
    simp only [Set.mem_Icc] at h1 h2
    have e1 : |d * ζ x u| ≤ d := by
      rw [abs_mul, abs_of_pos hd]; nlinarith [abs_le.mpr ⟨h1.1, h1.2⟩]
    have e2 : |mk.Q x * (c - sC x)| ≤ c - sC x := by
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ c - sC x)]
      nlinarith [abs_le.mpr ⟨h2.1, h2.2⟩]
    calc |ξ x u| ≤ |d * ζ x u| + |mk.Q x * (c - sC x)| := abs_add_le _ _
      _ ≤ d + (c - sC x) := add_le_add e1 e2
      _ = d + c - sC x := by ring
  have hGWξ : DirectedOpinion.NoMemory.GWModel P mk X U ξ c d :=
    { c_nonneg := hGW.c_nonneg
      c_lt_one := hGW.c_lt_one
      d_pos := hGW.d_pos
      d_le_one := hGW.d_le_one
      cd_le_one := hGW.cd_le_one
      weights_nonneg := hGW.weights_nonneg
      weights_le_one := hGW.weights_le_one
      weights_sum := hGW.weights_sum
      Q_mem := hGW.Q_mem
      ζ_mem := fun x u => by
        have := hξb x u
        have := hsC_nn x
        rw [Set.mem_Icc, ← abs_le]; linarith
      measurable_ζ := by
        have hζ := hGW.measurable_ζ
        have : Function.uncurry ξ = fun p : M × ℝ =>
            d * Function.uncurry ζ p + mk.Q p.1 * (c - sC p.1) := rfl
        rw [this]
        exact (hζ.const_mul d).add ((mk.measurable_Q.comp measurable_fst).mul
          ((hsC_meas.comp measurable_fst).const_sub c))
      measurable_X := hGW.measurable_X
      measurable_U := hGW.measurable_U
      indep_marks := hGW.indep_marks
      ident_marks := hGW.ident_marks
      indep_unif := hGW.indep_unif
      unif := hGW.unif
      indep_marks_unif := hGW.indep_marks_unif }
  have h8 := theorem_8 P mk X U ξ c d hGWξ hξb
  simp only at h8
  obtain ⟨hm8, -, hv8, -⟩ := h8
  -- measurability and boundedness of the signals
  have hZmeas : ∀ (η : M → ℝ → ℝ), Measurable (Function.uncurry η) → ∀ i,
      Measurable (DirectedOpinion.NoMemory.Z X U η i 0) := fun η hη i =>
    hη.comp ((hGW.measurable_X i).prodMk (hGW.measurable_U i 0))
  have hZL2 : ∀ i, MemLp (DirectedOpinion.NoMemory.Z X U ζ i 0) 2 P := fun i =>
    MemLp.of_bound (hZmeas ζ hGW.measurable_ζ i).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        have := hGW.ζ_mem (X i ω) (U i 0 ω)
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨this.1, this.2⟩)
  have key : ∀ i, (∀ᵐ ω ∂P, 0 < mk.N (X i ω)) →
      (∫ ω, DirectedOpinion.NoMemory.Z X U ξ i 0 ω ∂P = d * ∫ ω, DirectedOpinion.NoMemory.Z X U ζ i 0 ω ∂P) ∧
      variance (sumC mk X i) P = 0 ∧
      (∀ Y : Ω → ℝ, covariance (sumC mk X i) Y P = 0) ∧
      variance (condMeanSig P X (DirectedOpinion.NoMemory.Z X U ξ) i) P
        = d ^ 2 * variance (P[DirectedOpinion.NoMemory.Z X U ζ i 0 | MeasurableSpace.comap (X i) inferInstance]) P ∧
      ∫ ω, condVarSig P X (DirectedOpinion.NoMemory.Z X U ξ) i ω ∂P
        = d ^ 2 * ∫ ω, condVarSig P X (DirectedOpinion.NoMemory.Z X U ζ) i ω ∂P := by
    intro i hNi
    have hsCae : ∀ᵐ ω ∂P, sumC mk X i ω = c := by
      filter_upwards [hNi] with ω hω
      exact hGW.weights_sum _ hω
    have hZae : DirectedOpinion.NoMemory.Z X U ξ i 0 =ᵐ[P]
        d • DirectedOpinion.NoMemory.Z X U ζ i 0 := by
      filter_upwards [hsCae] with ω hω
      simp only [DirectedOpinion.NoMemory.Z, ξ, Pi.smul_apply, smul_eq_mul]
      have : sC (X i ω) = c := hω
      rw [this]; ring
    have hEsC : ∫ ω, sumC mk X i ω ∂P = c := by
      rw [integral_congr_ae hsCae]; simp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [integral_congr_ae hZae]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact integral_const_mul _ _
    · rw [variance_congr (show sumC mk X i =ᵐ[P] fun _ => c from hsCae)]
      simp [variance, evariance]
    · intro Y
      unfold covariance
      rw [hEsC]
      have : (fun ω => (sumC mk X i ω - c) * (Y ω - ∫ ω, Y ω ∂P)) =ᵐ[P] fun _ => (0 : ℝ) := by
        filter_upwards [hsCae] with ω hω
        rw [hω]; ring
      rw [integral_congr_ae this]; simp
    · unfold condMeanSig
      have h1 := (condExp_congr_ae (m := MeasurableSpace.comap (X i) inferInstance) hZae).trans
        (condExp_smul d (DirectedOpinion.NoMemory.Z X U ζ i 0) _)
      rw [variance_congr h1]
      exact variance_const_mul d _ P
    · unfold condVarSig
      have h1 := (condVar_congr_ae (m := MeasurableSpace.comap (X i) inferInstance) hZae).trans
        (condVar_smul d (DirectedOpinion.NoMemory.Z X U ζ i 0))
      rw [integral_congr_ae h1]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact integral_const_mul _ _
  have hF : ∀ i, variance (DirectedOpinion.NoMemory.Z X U ζ i 0) P
      = ∫ ω, condVarSig P X (DirectedOpinion.NoMemory.Z X U ζ) i ω ∂P
        + variance (P[DirectedOpinion.NoMemory.Z X U ζ i 0 | MeasurableSpace.comap (X i) inferInstance]) P := by
    intro i
    exact (integral_condVar_add_variance_condExp (hGW.measurable_X i).comap_le (hZL2 i)).symm
  obtain ⟨hA0, hB0, hC0, hD0, hE0⟩ := key [] hN0
  obtain ⟨hA1, hB1, hC1, hD1, hE1⟩ := key [0] hN1
  -- ρ₂ ≤ c² < (c+d)²
  have hCle : ∀ x j, j < mk.N x → mk.C x j ≤ c := by
    intro x j hj
    have hs := hGW.weights_sum x (by omega)
    rw [← hs]
    exact Finset.single_le_sum (f := fun j => mk.C x j)
      (fun i _ => hGW.weights_nonneg x i) (Finset.mem_range.mpr hj)
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
  have hgap : (c + d) ^ 2 - DirectedOpinion.NoMemory.rho2 P mk X ≠ 0 := by
    have : c ^ 2 < (c + d) ^ 2 := by nlinarith
    linarith
  have hc1 : c < 1 := hGW.c_lt_one
  have h1ρ : 1 - DirectedOpinion.NoMemory.rho2 P mk X ≠ 0 := by
    have : c ^ 2 < 1 := by nlinarith
    linarith
  have h2b : 2 - (c + d) ≠ 0 := by linarith
  have h1b : 1 - (1 - c - d) ^ 2 ≠ 0 := by
    have : 1 - (1 - c - d) ^ 2 = (c + d) * (2 - (c + d)) := by ring
    rw [this]; exact mul_ne_zero hb.ne' h2b
  have hbne : c + d ≠ 0 := hb.ne'
  simp only [ρ₁s, ρ₁, ρ₂s, ρ₂, Rstar]
  constructor
  · have e : Mstar mk X U ζ c d = limOpinion mk X (DirectedOpinion.NoMemory.Z X U ξ) c d [] := rfl
    rw [e, hm8, hA0, hA1]
    ring
  · have e : Mstar mk X U ζ c d = limOpinion mk X (DirectedOpinion.NoMemory.Z X U ξ) c d [] := rfl
    rw [e, hv8, hB0, hB1, hC0, hC1, hD0, hD1, hE0, hE1, hF [], hF [0]]
    field_simp
    ring
