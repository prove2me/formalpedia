-- Prove2me | solution 1 for CarrollGR.schwarzschild_unique_vacuum_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T18:00:30.371609+00:00
-- url     : https://prove2.me/submissions/4b3f22e7-62e4-463d-81dd-72082ba88af2

import Mathlib
import Definitions.Def_CarrollGR_Defs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

open scoped ContDiff

namespace BirkB
open CarrollGR Finset Filter Topology

noncomputable def aa (A : ℝ → ℝ → ℝ) : Coord → ℝ := fun y => A (y 1) (y 0)

def UU (r₁ r₂ t₁ t₂ : ℝ) : Set Coord :=
  {y | y 1 ∈ Set.Ioo r₁ r₂ ∧ y 0 ∈ Set.Ioo t₁ t₂ ∧ y 2 ∈ Set.Ioo 0 Real.pi}

theorem UU_open (r₁ r₂ t₁ t₂ : ℝ) : IsOpen (UU r₁ r₂ t₁ t₂) :=
  (isOpen_Ioo.preimage (continuous_apply 1)).inter
    ((isOpen_Ioo.preimage (continuous_apply 0)).inter (isOpen_Ioo.preimage (continuous_apply 2)))

theorem aa_smooth {A : ℝ → ℝ → ℝ} {r₁ r₂ t₁ t₂ : ℝ}
    (hA : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => A p.1 p.2) (Set.Ioo r₁ r₂ ×ˢ Set.Ioo t₁ t₂)) :
    ContDiffOn ℝ ∞ (aa A) (UU r₁ r₂ t₁ t₂) := by
  have hL : ContDiff ℝ ∞ (fun y : Coord => (y 1, y 0)) := by fun_prop
  exact hA.comp hL.contDiffOn (fun y hy => ⟨hy.1, hy.2.1⟩)

theorem dAt {f : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {x : Coord} (hx : x ∈ U) : DifferentiableAt ℝ f x :=
  (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)

theorem pd_smooth {f : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (μ : Fin 4) : ContDiffOn ℝ ∞ (partialD μ f) U := by
  have h := hf.fderiv_of_isOpen hU (m := ∞) (by simp)
  show ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y (Pi.single μ (1:ℝ))) U
  exact h.clm_apply contDiffOn_const

theorem pd_pd_comm {f : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {x : Coord} (hx : x ∈ U) (i j : Fin 4) :
    partialD i (partialD j f) x = partialD j (partialD i f) x := by
  have hc := hf.contDiffAt (hU.mem_nhds hx)
  have hs : IsSymmSndFDerivAt ℝ f x :=
    hc.isSymmSndFDerivAt (by simpa using (WithTop.coe_le_coe.mpr le_top : (2 : WithTop ℕ∞) ≤ ∞))
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_of_isOpen hU (m := ∞) (by simp)).contDiffAt (hU.mem_nhds hx)).differentiableAt
      (by simp)
  unfold partialD
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simp
  exact hs _ _

theorem pd_line {f : Coord → ℝ} {x : Coord} (hf : DifferentiableAt ℝ f x) (α : Fin 4) :
    HasDerivAt (fun s : ℝ => f (x + s • (Pi.single α (1:ℝ) : Coord))) (partialD α f x) 0 := by
  have hl : HasDerivAt (fun s : ℝ => x + s • (Pi.single α (1:ℝ) : Coord))
      (Pi.single α (1:ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (Pi.single α (1:ℝ) : Coord)).const_add x
  have hf' : DifferentiableAt ℝ f (x + (0:ℝ) • (Pi.single α (1:ℝ) : Coord)) := by simpa using hf
  have := hf'.hasFDerivAt.comp_hasDerivAt (0:ℝ) hl
  simp only [zero_smul, add_zero] at this
  exact this

theorem pd_zero_of_inv {f : Coord → ℝ} {μ : Fin 4}
    (hf : ∀ y (s : ℝ), f (y + s • (Pi.single μ (1:ℝ) : Coord)) = f y) (y : Coord) :
    partialD μ f y = 0 := by
  by_cases hd : DifferentiableAt ℝ f y
  · have h1 := pd_line hd μ
    have h2 : (fun s : ℝ => f (y + s • (Pi.single μ (1:ℝ) : Coord))) = fun _ => f y :=
      funext fun s => hf y s
    rw [h2] at h1
    exact h1.unique (hasDerivAt_const (0:ℝ) (f y))
  · simp [partialD, fderiv_zero_of_not_differentiableAt hd]

theorem pd_inv_trans {f : Coord → ℝ} {v : Coord}
    (hf : ∀ y (s : ℝ), f (y + s • v) = f y) (ν : Fin 4) (y : Coord) (s : ℝ) :
    partialD ν f (y + s • v) = partialD ν f y := by
  unfold partialD
  have : (fun z => f (z + s • v)) = f := funext fun z => hf z s
  rw [← fderiv_comp_add_right, this]

theorem aa_inv (A : ℝ → ℝ → ℝ) {μ : Fin 4} (hμ : μ = 2 ∨ μ = 3) (y : Coord) (s : ℝ) :
    aa A (y + s • (Pi.single μ (1:ℝ) : Coord)) = aa A y := by
  rcases hμ with rfl | rfl <;> simp [aa]

theorem pa_z (A : ℝ → ℝ → ℝ) {μ : Fin 4} (hμ : μ = 2 ∨ μ = 3) (y : Coord) :
    partialD μ (aa A) y = 0 := pd_zero_of_inv (aa_inv A hμ) y

theorem paa_z (A : ℝ → ℝ → ℝ) {μ : Fin 4} (hμ : μ = 2 ∨ μ = 3) (ν : Fin 4) (y : Coord) :
    partialD μ (partialD ν (aa A)) y = 0 :=
  pd_zero_of_inv (fun z s => pd_inv_trans (aa_inv A hμ) ν z s) y

theorem pd_eq_zero_of {f : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hf : ∀ y ∈ U, f y = 0)
    {x : Coord} (hx : x ∈ U) (μ : Fin 4) : partialD μ f x = 0 := by
  have h : f =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hf y hy
  unfold partialD
  rw [h.fderiv_eq]
  simp

theorem dq {P Q : Coord → ℝ} {x : Coord} (hP : DifferentiableAt ℝ P x)
    (hQ : DifferentiableAt ℝ Q x) (hQ0 : Q x ≠ 0) :
    DifferentiableAt ℝ (fun y : Coord => P y / Q y) x := by
  have e : (fun y : Coord => P y / Q y) = fun y => P y * (Q y)⁻¹ := funext fun y => div_eq_mul_inv _ _
  rw [e]
  exact hP.mul (hQ.inv hQ0)

theorem pd_y1 (x : Coord) (α : Fin 4) :
    partialD α (fun y : Coord => y 1) x = (Pi.single α (1:ℝ) : Coord) 1 := by
  have p1 : HasFDerivAt (fun f : Coord => f 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1 : Coord →L[ℝ] ℝ) x :=
    hasFDerivAt_apply 1 x
  unfold partialD
  rw [p1.fderiv]
  simp

theorem pdq2 {P Q : Coord → ℝ} {x : Coord} (hP : DifferentiableAt ℝ P x)
    (hQ : DifferentiableAt ℝ Q x) (hQ0 : Q x ≠ 0) (α : Fin 4) :
    partialD α (fun y : Coord => P y / (2 * Q y)) x
      = ((partialD α P x * Q x - P x * partialD α Q x) / (2 * Q x ^ 2)) := by
  have hd : DifferentiableAt ℝ (fun y => P y / (2 * Q y)) x :=
    dq hP (hQ.const_mul 2) (mul_ne_zero two_ne_zero hQ0)
  have h1 := pd_line hP α
  have h2 := pd_line hQ α
  have h3 := pd_line hd α
  have h4 := h1.div (h2.const_mul 2) (by simpa using mul_ne_zero two_ne_zero hQ0)
  rw [h3.unique h4]
  simp only [zero_smul, add_zero]
  field_simp
  try ring

theorem pdnq {Q : Coord → ℝ} {x : Coord} (hQ : DifferentiableAt ℝ Q x) (hQ0 : Q x ≠ 0)
    (α : Fin 4) :
    partialD α (fun y : Coord => -(y 1) / Q y) x
      = ((-(Pi.single α (1:ℝ) : Coord) 1 * Q x + x 1 * partialD α Q x) / Q x ^ 2) := by
  have hP : DifferentiableAt ℝ (fun y : Coord => -(y 1)) x := by fun_prop
  have hd : DifferentiableAt ℝ (fun y : Coord => -(y 1) / Q y) x := dq hP hQ hQ0
  have h1 := pd_line hP α
  have h2 := pd_line hQ α
  have h3 := pd_line hd α
  have h4 := h1.div h2 (by simpa using hQ0)
  rw [h3.unique h4]
  have e : partialD α (fun y : Coord => -(y 1)) x = -(Pi.single α (1:ℝ) : Coord) 1 := by
    have h0 := pd_y1 x α
    unfold partialD at h0 ⊢
    rw [fderiv_fun_neg]
    simp [h0]
  rw [e]
  simp only [zero_smul, add_zero]
  ring

theorem pdi1 {x : Coord} (hx : x 1 ≠ 0) (α : Fin 4) :
    partialD α (fun y : Coord => 1 / y 1) x = (-(Pi.single α (1:ℝ) : Coord) 1 / x 1 ^ 2) := by
  have hP : DifferentiableAt ℝ (fun y : Coord => y 1) x := by fun_prop
  have hd : DifferentiableAt ℝ (fun y : Coord => 1 / y 1) x := dq (differentiableAt_const _) hP hx
  have h1 := pd_line hP α
  have h3 := pd_line hd α
  have h4 := (hasDerivAt_const (0:ℝ) (1:ℝ)).div h1 (by simpa using hx)
  rw [h3.unique h4]
  rw [pd_y1 x α]
  simp only [zero_smul, add_zero]
  ring

theorem pdc (c : ℝ) (x : Coord) (α : Fin 4) : partialD α (fun _ : Coord => c) x = 0 := by
  simp [partialD]

theorem pd_neg' (f : Coord → ℝ) (x : Coord) (α : Fin 4) :
    partialD α (fun y => -f y) x = -partialD α f x := by
  unfold partialD
  rw [fderiv_fun_neg]
  simp

theorem pd_sq1 (x : Coord) (α : Fin 4) :
    partialD α (fun y : Coord => y 1 ^ 2) x = 2 * x 1 * (Pi.single α (1:ℝ) : Coord) 1 := by
  have hP : DifferentiableAt ℝ (fun y : Coord => y 1) x := by fun_prop
  have hd : DifferentiableAt ℝ (fun y : Coord => y 1 ^ 2) x := by fun_prop
  have h1 := pd_line hP α
  have h3 := pd_line hd α
  have h4 := h1.pow 2
  rw [h3.unique h4]
  rw [pd_y1 x α]
  simp only [zero_smul, add_zero]
  ring

theorem pd_prod2 (F : Coord → ℝ) (G : ℝ → ℝ) (G' : ℝ) (x : Coord)
    (hF : DifferentiableAt ℝ F x) (hG : HasDerivAt G G' (x 2)) (α : Fin 4) :
    partialD α (fun y => F y * G (y 2)) x
      = partialD α F x * G (x 2) + F x * G' * (Pi.single α (1:ℝ) : Coord) 2 := by
  have p2 : HasFDerivAt (fun f : Coord => f 2)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2 : Coord →L[ℝ] ℝ) x :=
    hasFDerivAt_apply 2 x
  have h2 := hG.comp_hasFDerivAt (f := fun f : Coord => f 2) x p2
  have h := hF.hasFDerivAt.mul h2
  unfold partialD
  rw [show (fun y : Coord => F y * G (y 2)) = (F * (G ∘ fun f : Coord => f 2)) from rfl, h.fderiv]
  simp
  ring

noncomputable def gB : Fin 4 → Fin 4 → ℝ → ℝ :=
  ![![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)],
    ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)],
    ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)],
    ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun t : ℝ => Real.sin t ^ 2)]]

noncomputable def gB' : Fin 4 → Fin 4 → ℝ → ℝ :=
  ![![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)],
    ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)],
    ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)],
    ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun t : ℝ => 2 * Real.sin t * Real.cos t)]]

noncomputable def bF : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ :=
  ![![![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)]],
    ![![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun t : ℝ => Real.sin t ^ 2)]],
    ![![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun t : ℝ => Real.sin t * Real.cos t)]],
    ![![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun t : ℝ => Real.cos t / Real.sin t)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun t : ℝ => Real.cos t / Real.sin t), (fun _ : ℝ => 1)]]]

noncomputable def bF' : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ :=
  ![![![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)]],
    ![![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun t : ℝ => 2 * Real.sin t * Real.cos t)]],
    ![![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun t : ℝ => Real.cos t * Real.cos t - Real.sin t * Real.sin t)]],
    ![![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun t : ℝ => -(Real.sin t * Real.sin t + Real.cos t * Real.cos t) / Real.sin t ^ 2)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun t : ℝ => -(Real.sin t * Real.sin t + Real.cos t * Real.cos t) / Real.sin t ^ 2), (fun _ : ℝ => 0)]]]

theorem hd_s2 (t : ℝ) : HasDerivAt (fun t : ℝ => Real.sin t ^ 2) (2 * Real.sin t * Real.cos t) t := by
  have h := (Real.hasDerivAt_sin t).pow 2
  exact h.congr_deriv (by simp <;> ring)

theorem hd_sc (t : ℝ) : HasDerivAt (fun t : ℝ => Real.sin t * Real.cos t)
    (Real.cos t * Real.cos t - Real.sin t * Real.sin t) t := by
  have h := (Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)
  exact h.congr_deriv (by ring)

theorem hd_ct (t : ℝ) (hs : Real.sin t ≠ 0) : HasDerivAt (fun t : ℝ => Real.cos t / Real.sin t)
    (-(Real.sin t * Real.sin t + Real.cos t * Real.cos t) / Real.sin t ^ 2) t := by
  have h := (Real.hasDerivAt_cos t).div (Real.hasDerivAt_sin t) hs
  exact h.congr_deriv (by ring)

theorem gB_deriv (t : ℝ) (i j : Fin 4) : HasDerivAt (gB i j) (gB' i j t) t := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact hasDerivAt_const t (1:ℝ)
    | exact hd_s2 t


theorem bF_deriv (t : ℝ) (hs : Real.sin t ≠ 0) (σ μ ν : Fin 4) :
    HasDerivAt (bF σ μ ν) (bF' σ μ ν t) t := by
  fin_cases σ <;> fin_cases μ <;> fin_cases ν <;>
    first
    | exact hasDerivAt_const t (1:ℝ)
    | exact hd_s2 t
    | exact hd_sc t
    | exact hd_ct t hs

noncomputable def aF (A B : ℝ → ℝ → ℝ) : Fin 4 → Fin 4 → Fin 4 → Coord → ℝ :=
  ![![![(fun y : Coord => partialD 0 (aa A) y / (2 * aa A y)), (fun y : Coord => partialD 1 (aa A) y / (2 * aa A y)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ))], ![(fun y : Coord => partialD 1 (aa A) y / (2 * aa A y)), (fun y : Coord => partialD 0 (aa B) y / (2 * aa A y)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ))], ![(fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ))], ![(fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ))]],
    ![![(fun y : Coord => partialD 1 (aa A) y / (2 * aa B y)), (fun y : Coord => partialD 0 (aa B) y / (2 * aa B y)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ))], ![(fun y : Coord => partialD 0 (aa B) y / (2 * aa B y)), (fun y : Coord => partialD 1 (aa B) y / (2 * aa B y)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ))], ![(fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun y : Coord => -(y 1) / aa B y), (fun _ : Coord => (0:ℝ))], ![(fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun y : Coord => -(y 1) / aa B y)]],
    ![![(fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ))], ![(fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun y : Coord => 1 / y 1), (fun _ : Coord => (0:ℝ))], ![(fun _ : Coord => (0:ℝ)), (fun y : Coord => 1 / y 1), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ))], ![(fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (-1:ℝ))]],
    ![![(fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ))], ![(fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun y : Coord => 1 / y 1)], ![(fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (1:ℝ))], ![(fun _ : Coord => (0:ℝ)), (fun y : Coord => 1 / y 1), (fun _ : Coord => (1:ℝ)), (fun _ : Coord => (0:ℝ))]]]

noncomputable def aFd (A B : ℝ → ℝ → ℝ) (x : Coord) (α : Fin 4) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![![![((partialD α (partialD 0 (aa A)) x * aa A x - partialD 0 (aa A) x * partialD α (aa A) x) / (2 * aa A x ^ 2)), ((partialD α (partialD 1 (aa A)) x * aa A x - partialD 1 (aa A) x * partialD α (aa A) x) / (2 * aa A x ^ 2)), 0, 0], ![((partialD α (partialD 1 (aa A)) x * aa A x - partialD 1 (aa A) x * partialD α (aa A) x) / (2 * aa A x ^ 2)), ((partialD α (partialD 0 (aa B)) x * aa A x - partialD 0 (aa B) x * partialD α (aa A) x) / (2 * aa A x ^ 2)), 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![((partialD α (partialD 1 (aa A)) x * aa B x - partialD 1 (aa A) x * partialD α (aa B) x) / (2 * aa B x ^ 2)), ((partialD α (partialD 0 (aa B)) x * aa B x - partialD 0 (aa B) x * partialD α (aa B) x) / (2 * aa B x ^ 2)), 0, 0], ![((partialD α (partialD 0 (aa B)) x * aa B x - partialD 0 (aa B) x * partialD α (aa B) x) / (2 * aa B x ^ 2)), ((partialD α (partialD 1 (aa B)) x * aa B x - partialD 1 (aa B) x * partialD α (aa B) x) / (2 * aa B x ^ 2)), 0, 0], ![0, 0, ((-(Pi.single α (1:ℝ) : Coord) 1 * aa B x + x 1 * partialD α (aa B) x) / aa B x ^ 2), 0], ![0, 0, 0, ((-(Pi.single α (1:ℝ) : Coord) 1 * aa B x + x 1 * partialD α (aa B) x) / aa B x ^ 2)]],
    ![![0, 0, 0, 0], ![0, 0, (-(Pi.single α (1:ℝ) : Coord) 1 / x 1 ^ 2), 0], ![0, (-(Pi.single α (1:ℝ) : Coord) 1 / x 1 ^ 2), 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, (-(Pi.single α (1:ℝ) : Coord) 1 / x 1 ^ 2)], ![0, 0, 0, 0], ![0, (-(Pi.single α (1:ℝ) : Coord) 1 / x 1 ^ 2), 0, 0]]]


noncomputable def Fg (A B : ℝ → ℝ → ℝ) : Fin 4 → Fin 4 → Coord → ℝ :=
  ![![(fun z : Coord => -aa A z), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ))],
    ![(fun _ : Coord => (0:ℝ)), (fun z : Coord => aa B z), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ))],
    ![(fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun z : Coord => z 1 ^ 2), (fun _ : Coord => (0:ℝ))],
    ![(fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun _ : Coord => (0:ℝ)), (fun z : Coord => z 1 ^ 2)]]

theorem g_repr (A B : ℝ → ℝ → ℝ) (z : Coord) (i j : Fin 4) :
    sphericalMetric A B z i j = Fg A B i j z * gB i j (z 2) := by
  fin_cases i <;> fin_cases j <;> simp [sphericalMetric, Fg, gB, Matrix.diagonal, aa]

theorem Fg_diff {A B : ℝ → ℝ → ℝ} {y : Coord} (ha : DifferentiableAt ℝ (aa A) y)
    (hb : DifferentiableAt ℝ (aa B) y) (i j : Fin 4) : DifferentiableAt ℝ (Fg A B i j) y := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact differentiableAt_const _
    | exact ha.neg
    | exact hb
    | exact (by fun_prop : DifferentiableAt ℝ (fun z : Coord => z 1 ^ 2) y)

theorem pd_g {A B : ℝ → ℝ → ℝ} {y : Coord} (ha : DifferentiableAt ℝ (aa A) y)
    (hb : DifferentiableAt ℝ (aa B) y) (μ i j : Fin 4) :
    partialD μ (fun z => sphericalMetric A B z i j) y
      = partialD μ (Fg A B i j) y * gB i j (y 2)
        + Fg A B i j y * gB' i j (y 2) * (Pi.single μ (1:ℝ) : Coord) 2 := by
  have e : (fun z => sphericalMetric A B z i j) = fun z => Fg A B i j z * gB i j (z 2) :=
    funext fun z => g_repr A B z i j
  rw [e]
  exact pd_prod2 _ _ _ y (Fg_diff ha hb i j) (gB_deriv (y 2) i j) μ

theorem inv_g (A B : ℝ → ℝ → ℝ) (y : Coord) (hA0 : aa A y ≠ 0) (hB0 : aa B y ≠ 0)
    (hr : y 1 ≠ 0) (hs : Real.sin (y 2) ≠ 0) :
    invMetric (sphericalMetric A B) y = Matrix.diagonal
      ![(-aa A y)⁻¹, (aa B y)⁻¹, (y 1 ^ 2)⁻¹, (y 1 ^ 2 * Real.sin (y 2) ^ 2)⁻¹] := by
  have h1 : A (y 1) (y 0) ≠ 0 := hA0
  have h2 : B (y 1) (y 0) ≠ 0 := hB0
  unfold invMetric sphericalMetric
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp [aa] <;> field_simp

theorem chr_eq (A B : ℝ → ℝ → ℝ) (y : Coord) (ha : DifferentiableAt ℝ (aa A) y)
    (hb : DifferentiableAt ℝ (aa B) y) (hA0 : aa A y ≠ 0) (hB0 : aa B y ≠ 0)
    (hr : y 1 ≠ 0) (hs : Real.sin (y 2) ≠ 0) (σ μ ν : Fin 4) :
    christoffel (sphericalMetric A B) σ μ ν y = aF A B σ μ ν y * bF σ μ ν (y 2) := by
  have zA2 := pa_z A (μ := 2) (Or.inl rfl) y
  have zA3 := pa_z A (μ := 3) (Or.inr rfl) y
  have zB2 := pa_z B (μ := 2) (Or.inl rfl) y
  have zB3 := pa_z B (μ := 3) (Or.inr rfl) y
  simp only [christoffel, pd_g ha hb, inv_g A B y hA0 hB0 hr hs]
  fin_cases σ <;> fin_cases μ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, Fg, gB, gB', aF, bF, Matrix.diagonal, Pi.single_apply, pd_neg',
      pd_sq1, pdc, zA2, zA3, zB2, zB3] <;> (try field_simp) <;> (try ring)

theorem dq2 {P Q : Coord → ℝ} {x : Coord} (hP : DifferentiableAt ℝ P x)
    (hQ : DifferentiableAt ℝ Q x) (hQ0 : Q x ≠ 0) :
    DifferentiableAt ℝ (fun y : Coord => P y / (2 * Q y)) x :=
  dq hP (hQ.const_mul 2) (mul_ne_zero two_ne_zero hQ0)

theorem aF_diff {A B : ℝ → ℝ → ℝ} {y : Coord} (ha : DifferentiableAt ℝ (aa A) y)
    (hb : DifferentiableAt ℝ (aa B) y)
    (ha0 : DifferentiableAt ℝ (partialD 0 (aa A)) y) (ha1 : DifferentiableAt ℝ (partialD 1 (aa A)) y)
    (hb0 : DifferentiableAt ℝ (partialD 0 (aa B)) y) (hb1 : DifferentiableAt ℝ (partialD 1 (aa B)) y)
    (hA0 : aa A y ≠ 0) (hB0 : aa B y ≠ 0) (hr : y 1 ≠ 0) (σ μ ν : Fin 4) :
    DifferentiableAt ℝ (aF A B σ μ ν) y := by
  fin_cases σ <;> fin_cases μ <;> fin_cases ν <;>
    first
    | exact differentiableAt_const _
    | exact dq2 ha0 ha hA0
    | exact dq2 ha1 ha hA0
    | exact dq2 hb0 ha hA0
    | exact dq2 ha1 hb hB0
    | exact dq2 hb0 hb hB0
    | exact dq2 hb1 hb hB0
    | exact dq (P := fun y : Coord => -(y 1)) (by fun_prop) hb hB0
    | exact dq (P := fun _ : Coord => (1:ℝ)) (Q := fun y : Coord => y 1)
        (differentiableAt_const _) (by fun_prop) hr

theorem pd_aF {A B : ℝ → ℝ → ℝ} {y : Coord} (ha : DifferentiableAt ℝ (aa A) y)
    (hb : DifferentiableAt ℝ (aa B) y)
    (ha0 : DifferentiableAt ℝ (partialD 0 (aa A)) y) (ha1 : DifferentiableAt ℝ (partialD 1 (aa A)) y)
    (hb0 : DifferentiableAt ℝ (partialD 0 (aa B)) y) (hb1 : DifferentiableAt ℝ (partialD 1 (aa B)) y)
    (hA0 : aa A y ≠ 0) (hB0 : aa B y ≠ 0) (hr : y 1 ≠ 0) (α σ μ ν : Fin 4) :
    partialD α (aF A B σ μ ν) y = aFd A B y α σ μ ν := by
  fin_cases σ <;> fin_cases μ <;> fin_cases ν <;>
    first
    | exact pdc 0 y α
    | exact pdc 1 y α
    | exact pdc (-1) y α
    | exact pdq2 ha0 ha hA0 α
    | exact pdq2 ha1 ha hA0 α
    | exact pdq2 hb0 ha hA0 α
    | exact pdq2 ha1 hb hB0 α
    | exact pdq2 hb0 hb hB0 α
    | exact pdq2 hb1 hb hB0 α
    | exact pdnq hb hB0 α
    | exact pdi1 hr α

theorem pd_chr (A B : ℝ → ℝ → ℝ) (U : Set Coord) (hU : IsOpen U)
    (ha : ContDiffOn ℝ ∞ (aa A) U) (hb : ContDiffOn ℝ ∞ (aa B) U)
    (hpos : ∀ y ∈ U, aa A y ≠ 0 ∧ aa B y ≠ 0 ∧ y 1 ≠ 0 ∧ Real.sin (y 2) ≠ 0)
    (x : Coord) (hx : x ∈ U) (α σ μ ν : Fin 4) :
    partialD α (christoffel (sphericalMetric A B) σ μ ν) x
      = aFd A B x α σ μ ν * bF σ μ ν (x 2)
        + aF A B σ μ ν x * bF' σ μ ν (x 2) * (Pi.single α (1:ℝ) : Coord) 2 := by
  obtain ⟨hA0, hB0, hr, hs⟩ := hpos x hx
  have heq : christoffel (sphericalMetric A B) σ μ ν =ᶠ[𝓝 x]
      fun y => aF A B σ μ ν y * bF σ μ ν (y 2) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    obtain ⟨h1, h2, h3, h4⟩ := hpos y hy
    exact chr_eq A B y (dAt hU ha hy) (dAt hU hb hy) h1 h2 h3 h4 σ μ ν
  have hd := aF_diff (dAt hU ha hx) (dAt hU hb hx) (dAt hU (pd_smooth hU ha 0) hx)
    (dAt hU (pd_smooth hU ha 1) hx) (dAt hU (pd_smooth hU hb 0) hx)
    (dAt hU (pd_smooth hU hb 1) hx) hA0 hB0 hr σ μ ν
  have hp := pd_prod2 _ _ _ x hd (bF_deriv (x 2) hs σ μ ν) α
  rw [pd_aF (dAt hU ha hx) (dAt hU hb hx) (dAt hU (pd_smooth hU ha 0) hx)
    (dAt hU (pd_smooth hU ha 1) hx) (dAt hU (pd_smooth hU hb 0) hx)
    (dAt hU (pd_smooth hU hb 1) hx) hA0 hB0 hr α σ μ ν] at hp
  have e : partialD α (christoffel (sphericalMetric A B) σ μ ν) x
      = partialD α (fun y => aF A B σ μ ν y * bF σ μ ν (y 2)) x := by
    unfold partialD
    rw [heq.fderiv_eq]
  rw [e, hp]


theorem ric01 (A B : ℝ → ℝ → ℝ) (U : Set Coord) (hU : IsOpen U)
    (ha : ContDiffOn ℝ ∞ (aa A) U) (hb : ContDiffOn ℝ ∞ (aa B) U)
    (hpos : ∀ y ∈ U, aa A y ≠ 0 ∧ aa B y ≠ 0 ∧ y 1 ≠ 0 ∧ Real.sin (y 2) ≠ 0) (x : Coord) (hx : x ∈ U) :
    ricci (sphericalMetric A B) 0 1 x = partialD 0 (aa B) x / (x 1 * aa B x) := by
  obtain ⟨hA0, hB0, hr, hs⟩ := hpos x hx
  have yA2 : ∀ y, partialD 2 (aa A) y = 0 := pa_z A (Or.inl rfl)
  have yA3 : ∀ y, partialD 3 (aa A) y = 0 := pa_z A (Or.inr rfl)
  have yB2 : ∀ y, partialD 2 (aa B) y = 0 := pa_z B (Or.inl rfl)
  have yB3 : ∀ y, partialD 3 (aa B) y = 0 := pa_z B (Or.inr rfl)
  have zA2 : ∀ ν y, partialD 2 (partialD ν (aa A)) y = 0 := paa_z A (Or.inl rfl)
  have zA3 : ∀ ν y, partialD 3 (partialD ν (aa A)) y = 0 := paa_z A (Or.inr rfl)
  have zB2 : ∀ ν y, partialD 2 (partialD ν (aa B)) y = 0 := paa_z B (Or.inl rfl)
  have zB3 : ∀ ν y, partialD 3 (partialD ν (aa B)) y = 0 := paa_z B (Or.inr rfl)
  have hsym := pd_pd_comm hU ha hx 0 1
  simp only [ricci, riemann, Fin.sum_univ_four, pd_chr A B U hU ha hb hpos x hx,
    chr_eq A B x (dAt hU ha hx) (dAt hU hb hx) hA0 hB0 hr hs]
  simp [aF, aFd, bF, bF', Pi.single_apply, hsym, yA2, yA3, yB2, yB3, zA2, zA3, zB2, zB3]
  field_simp
  ring

theorem ric0011 (A B : ℝ → ℝ → ℝ) (U : Set Coord) (hU : IsOpen U)
    (ha : ContDiffOn ℝ ∞ (aa A) U) (hb : ContDiffOn ℝ ∞ (aa B) U)
    (hpos : ∀ y ∈ U, aa A y ≠ 0 ∧ aa B y ≠ 0 ∧ y 1 ≠ 0 ∧ Real.sin (y 2) ≠ 0) (hb0 : ∀ y ∈ U, partialD 0 (aa B) y = 0) (x : Coord) (hx : x ∈ U) :
    ricci (sphericalMetric A B) 0 0 x * aa B x / aa A x + ricci (sphericalMetric A B) 1 1 x
      = (partialD 1 (aa A) x / aa A x + partialD 1 (aa B) x / aa B x) / x 1 := by
  obtain ⟨hA0, hB0, hr, hs⟩ := hpos x hx
  have yA2 : ∀ y, partialD 2 (aa A) y = 0 := pa_z A (Or.inl rfl)
  have yA3 : ∀ y, partialD 3 (aa A) y = 0 := pa_z A (Or.inr rfl)
  have yB2 : ∀ y, partialD 2 (aa B) y = 0 := pa_z B (Or.inl rfl)
  have yB3 : ∀ y, partialD 3 (aa B) y = 0 := pa_z B (Or.inr rfl)
  have zA2 : ∀ ν y, partialD 2 (partialD ν (aa A)) y = 0 := paa_z A (Or.inl rfl)
  have zA3 : ∀ ν y, partialD 3 (partialD ν (aa A)) y = 0 := paa_z A (Or.inr rfl)
  have zB2 : ∀ ν y, partialD 2 (partialD ν (aa B)) y = 0 := paa_z B (Or.inl rfl)
  have zB3 : ∀ ν y, partialD 3 (partialD ν (aa B)) y = 0 := paa_z B (Or.inr rfl)
  have hsym := pd_pd_comm hU ha hx 0 1
  have e0 : partialD 0 (aa B) x = 0 := hb0 x hx
  have e1 : ∀ μ, partialD μ (partialD 0 (aa B)) x = 0 := pd_eq_zero_of hU hb0 hx
  have hsb := pd_pd_comm hU hb hx 0 1
  simp only [ricci, riemann, Fin.sum_univ_four, pd_chr A B U hU ha hb hpos x hx,
    chr_eq A B x (dAt hU ha hx) (dAt hU hb hx) hA0 hB0 hr hs]
  simp [aF, aFd, bF, bF', Pi.single_apply, hsym, yA2, yA3, yB2, yB3, zA2, zA3, zB2, zB3, e0, e1, hsb]
  field_simp
  ring

theorem ric22 (A B : ℝ → ℝ → ℝ) (U : Set Coord) (hU : IsOpen U)
    (ha : ContDiffOn ℝ ∞ (aa A) U) (hb : ContDiffOn ℝ ∞ (aa B) U)
    (hpos : ∀ y ∈ U, aa A y ≠ 0 ∧ aa B y ≠ 0 ∧ y 1 ≠ 0 ∧ Real.sin (y 2) ≠ 0) (x : Coord) (hx : x ∈ U) :
    ricci (sphericalMetric A B) 2 2 x = 1 - 1 / aa B x + x 1 * partialD 1 (aa B) x / (2 * aa B x ^ 2)
      - x 1 * partialD 1 (aa A) x / (2 * aa A x * aa B x) := by
  obtain ⟨hA0, hB0, hr, hs⟩ := hpos x hx
  have yA2 : ∀ y, partialD 2 (aa A) y = 0 := pa_z A (Or.inl rfl)
  have yA3 : ∀ y, partialD 3 (aa A) y = 0 := pa_z A (Or.inr rfl)
  have yB2 : ∀ y, partialD 2 (aa B) y = 0 := pa_z B (Or.inl rfl)
  have yB3 : ∀ y, partialD 3 (aa B) y = 0 := pa_z B (Or.inr rfl)
  have zA2 : ∀ ν y, partialD 2 (partialD ν (aa A)) y = 0 := paa_z A (Or.inl rfl)
  have zA3 : ∀ ν y, partialD 3 (partialD ν (aa A)) y = 0 := paa_z A (Or.inr rfl)
  have zB2 : ∀ ν y, partialD 2 (partialD ν (aa B)) y = 0 := paa_z B (Or.inl rfl)
  have zB3 : ∀ ν y, partialD 3 (partialD ν (aa B)) y = 0 := paa_z B (Or.inr rfl)
  have hsym := pd_pd_comm hU ha hx 0 1
  simp only [ricci, riemann, Fin.sum_univ_four, pd_chr A B U hU ha hb hpos x hx,
    chr_eq A B x (dAt hU ha hx) (dAt hU hb hx) hA0 hB0 hr hs]
  simp [aF, aFd, bF, bF', Pi.single_apply, hsym, yA2, yA3, yB2, yB3, zA2, zA3, zB2, zB3]
  field_simp
  ring

theorem const_Ioo {f : ℝ → ℝ} {p q : ℝ} (h : ∀ s ∈ Set.Ioo p q, HasDerivAt f 0 s) {u v : ℝ}
    (hu : u ∈ Set.Ioo p q) (hv : v ∈ Set.Ioo p q) : f u = f v :=
  isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun s hs => (h s hs).differentiableAt.differentiableWithinAt) (fun s hs => (h s hs).deriv) hu hv

theorem hline0 (r t : ℝ) :
    HasDerivAt (fun s : ℝ => (![s, r, Real.pi / 2, 0] : Coord)) (Pi.single 0 (1:ℝ)) t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa using hasDerivAt_id' t
  · simpa using hasDerivAt_const t r
  · simpa using hasDerivAt_const t (Real.pi / 2)
  · simpa using hasDerivAt_const t (0:ℝ)

theorem hline1 (r t : ℝ) :
    HasDerivAt (fun s : ℝ => (![t, s, Real.pi / 2, 0] : Coord)) (Pi.single 1 (1:ℝ)) r := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa using hasDerivAt_const r t
  · simpa using hasDerivAt_id' r
  · simpa using hasDerivAt_const r (Real.pi / 2)
  · simpa using hasDerivAt_const r (0:ℝ)

theorem dT {F : ℝ → ℝ → ℝ} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ (aa F) U)
    (r t : ℝ) (hm : (![t, r, Real.pi / 2, 0] : Coord) ∈ U) :
    HasDerivAt (fun s => F r s) (partialD 0 (aa F) (![t, r, Real.pi / 2, 0] : Coord)) t := by
  have hd := dAt hU hf hm
  have h := hd.hasFDerivAt.comp_hasDerivAt t (hline0 r t)
  have e : (aa F ∘ fun s : ℝ => (![s, r, Real.pi / 2, 0] : Coord)) = fun s => F r s := by
    funext s; simp [aa]
  rw [e] at h
  exact h

theorem dR {F : ℝ → ℝ → ℝ} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ (aa F) U)
    (r t : ℝ) (hm : (![t, r, Real.pi / 2, 0] : Coord) ∈ U) :
    HasDerivAt (fun s => F s t) (partialD 1 (aa F) (![t, r, Real.pi / 2, 0] : Coord)) r := by
  have hd := dAt hU hf hm
  have h := hd.hasFDerivAt.comp_hasDerivAt r (hline1 r t)
  have e : (aa F ∘ fun s : ℝ => (![t, s, Real.pi / 2, 0] : Coord)) = fun s => F s t := by
    funext s; simp [aa]
  rw [e] at h
  exact h


theorem ricZ (A B : ℝ → ℝ → ℝ) (U : Set Coord) (hU : IsOpen U)
    (ha : ContDiffOn ℝ ∞ (aa A) U) (hb : ContDiffOn ℝ ∞ (aa B) U)
    (hpos : ∀ y ∈ U, aa A y ≠ 0 ∧ aa B y ≠ 0 ∧ y 1 ≠ 0 ∧ Real.sin (y 2) ≠ 0)
    (hb0 : ∀ y ∈ U, partialD 0 (aa B) y = 0) (x : Coord) (hx : x ∈ U) (c G G' : ℝ)
    (hrc : x 1 - c ≠ 0) (hG : G ≠ 0)
    (eA : aa A x = G * (1 - c / x 1))
    (eA0 : partialD 0 (aa A) x = G' * (1 - c / x 1))
    (eA1 : partialD 1 (aa A) x = G * (c / x 1 ^ 2))
    (eA01 : partialD 0 (partialD 1 (aa A)) x = G' * (c / x 1 ^ 2))
    (eA11 : partialD 1 (partialD 1 (aa A)) x = G * (-2 * c / x 1 ^ 3))
    (eB : aa B x = x 1 / (x 1 - c))
    (eB1 : partialD 1 (aa B) x = -c / (x 1 - c) ^ 2)
    (eB11 : partialD 1 (partialD 1 (aa B)) x = 2 * c / (x 1 - c) ^ 3)
    (μ ν : Fin 4) : ricci (sphericalMetric A B) μ ν x = 0 := by
  obtain ⟨hA0, hB0, hr, hs⟩ := hpos x hx
  have yA2 : ∀ y, partialD 2 (aa A) y = 0 := pa_z A (Or.inl rfl)
  have yA3 : ∀ y, partialD 3 (aa A) y = 0 := pa_z A (Or.inr rfl)
  have yB2 : ∀ y, partialD 2 (aa B) y = 0 := pa_z B (Or.inl rfl)
  have yB3 : ∀ y, partialD 3 (aa B) y = 0 := pa_z B (Or.inr rfl)
  have zA2 : ∀ ν y, partialD 2 (partialD ν (aa A)) y = 0 := paa_z A (Or.inl rfl)
  have zA3 : ∀ ν y, partialD 3 (partialD ν (aa A)) y = 0 := paa_z A (Or.inr rfl)
  have zB2 : ∀ ν y, partialD 2 (partialD ν (aa B)) y = 0 := paa_z B (Or.inl rfl)
  have zB3 : ∀ ν y, partialD 3 (partialD ν (aa B)) y = 0 := paa_z B (Or.inr rfl)
  have hsym := pd_pd_comm hU ha hx 0 1
  have eA10 : partialD 1 (partialD 0 (aa A)) x = G' * (c / x 1 ^ 2) := by rw [← hsym]; exact eA01
  have e0 : partialD 0 (aa B) x = 0 := hb0 x hx
  have e1 : ∀ μ, partialD μ (partialD 0 (aa B)) x = 0 := pd_eq_zero_of hU hb0 hx
  have hsb := pd_pd_comm hU hb hx 0 1
  have eB01 : partialD 0 (partialD 1 (aa B)) x = 0 := by rw [hsb]; exact e1 1
  have hc1 : x 1 - c ≠ 0 := hrc
  simp only [ricci, riemann, Fin.sum_univ_four, pd_chr A B U hU ha hb hpos x hx,
    chr_eq A B x (dAt hU ha hx) (dAt hU hb hx) hA0 hB0 hr hs]
  fin_cases μ <;> fin_cases ν <;>
    simp [aF, aFd, bF, bF', Pi.single_apply, yA2, yA3, yB2, yB3, zA2, zA3, zB2, zB3, e0, e1,
      eB01, eA10, eA01, eA, eA0, eA1, eA11, eB, eB1, eB11] <;>
    (try field_simp) <;> (try ring_nf) <;> (try simp [Real.sin_sq_add_cos_sq]) <;> (try ring)


theorem pd_comp1 {φ : ℝ → ℝ} {φ' : ℝ} {x : Coord} (h : HasDerivAt φ φ' (x 1)) (α : Fin 4) :
    partialD α (fun z : Coord => φ (z 1)) x = φ' * (Pi.single α (1:ℝ) : Coord) 1 := by
  have p1 : HasFDerivAt (fun f : Coord => f 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1 : Coord →L[ℝ] ℝ) x :=
    hasFDerivAt_apply 1 x
  have h2 := h.comp_hasFDerivAt (f := fun f : Coord => f 1) x p1
  unfold partialD
  rw [show (fun z : Coord => φ (z 1)) = (φ ∘ fun f : Coord => f 1) from rfl, h2.fderiv]
  simp
  try ring

theorem pd_prod01 {g k : ℝ → ℝ} {g' k' : ℝ} {x : Coord} (hg : HasDerivAt g g' (x 0))
    (hk : HasDerivAt k k' (x 1)) (α : Fin 4) :
    partialD α (fun z : Coord => g (z 0) * k (z 1)) x
      = g' * k (x 1) * (Pi.single α (1:ℝ) : Coord) 0
        + g (x 0) * k' * (Pi.single α (1:ℝ) : Coord) 1 := by
  have p0 : HasFDerivAt (fun f : Coord => f 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0 : Coord →L[ℝ] ℝ) x :=
    hasFDerivAt_apply 0 x
  have p1 : HasFDerivAt (fun f : Coord => f 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1 : Coord →L[ℝ] ℝ) x :=
    hasFDerivAt_apply 1 x
  have h0 := hg.comp_hasFDerivAt (f := fun f : Coord => f 0) x p0
  have h1 := hk.comp_hasFDerivAt (f := fun f : Coord => f 1) x p1
  have h := h0.mul h1
  unfold partialD
  have e : fderiv ℝ (fun z : Coord => g (z 0) * k (z 1)) x = _ := h.fderiv
  rw [e]
  simp
  ring

theorem pd_congrU {f f' : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (h : ∀ z ∈ U, f z = f' z)
    {x : Coord} (hx : x ∈ U) (α : Fin 4) : partialD α f x = partialD α f' x := by
  have e : f =ᶠ[𝓝 x] f' := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact h z hz
  unfold partialD
  rw [e.fderiv_eq]

theorem hk_d (c r : ℝ) (hr : r ≠ 0) : HasDerivAt (fun r : ℝ => 1 - c / r) (c / r ^ 2) r := by
  have h := (hasDerivAt_const r (1:ℝ)).sub ((hasDerivAt_const r c).div (hasDerivAt_id r) hr)
  refine h.congr_deriv ?_
  simp only [id, Pi.pow_apply]
  field_simp
  try ring

theorem hk1_d (c r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun r : ℝ => c / r ^ 2) (-2 * c / r ^ 3) r := by
  have h := (hasDerivAt_const r c).div ((hasDerivAt_id r).pow 2) (pow_ne_zero 2 hr)
  refine h.congr_deriv ?_
  simp only [id, Pi.pow_apply]
  field_simp
  try ring

theorem hphi_d (c r : ℝ) (hrc : r - c ≠ 0) :
    HasDerivAt (fun r : ℝ => r / (r - c)) (-c / (r - c) ^ 2) r := by
  have h := (hasDerivAt_id r).div ((hasDerivAt_id r).sub_const c) hrc
  refine h.congr_deriv ?_
  simp only [id, Pi.pow_apply]
  field_simp
  try ring

theorem hphi1_d (c r : ℝ) (hrc : r - c ≠ 0) :
    HasDerivAt (fun r : ℝ => -c / (r - c) ^ 2) (2 * c / (r - c) ^ 3) r := by
  have h := (hasDerivAt_const r (-c)).div (((hasDerivAt_id r).sub_const c).pow 2)
    (pow_ne_zero 2 hrc)
  refine h.congr_deriv ?_
  simp only [id, Pi.pow_apply]
  field_simp
  try ring

theorem rev (A B : ℝ → ℝ → ℝ) (r₁ r₂ t₁ t₂ c : ℝ) (hr₁ : 0 ≤ r₁)
    (hA : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => A p.1 p.2) (Set.Ioo r₁ r₂ ×ˢ Set.Ioo t₁ t₂))
    (hB : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => B p.1 p.2) (Set.Ioo r₁ r₂ ×ˢ Set.Ioo t₁ t₂))
    (hApos : ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂, 0 < A r t)
    (hBpos : ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂, 0 < B r t)
    (f : ℝ → ℝ)
    (hrep : ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂,
      0 < f t ∧ A r t = f t * (1 - c / r) ∧ B r t = (1 - c / r)⁻¹)
    (x : Coord) (hx : x ∈ UU r₁ r₂ t₁ t₂) (μ ν : Fin 4) :
    ricci (sphericalMetric A B) μ ν x = 0 := by
  have hU := UU_open r₁ r₂ t₁ t₂
  have ha := aa_smooth hA
  have hb := aa_smooth hB
  have hpos : ∀ y ∈ UU r₁ r₂ t₁ t₂, aa A y ≠ 0 ∧ aa B y ≠ 0 ∧ y 1 ≠ 0 ∧
      Real.sin (y 2) ≠ 0 := by
    intro y hy
    obtain ⟨h1, h0, h2⟩ := hy
    exact ⟨(hApos _ h1 _ h0).ne', (hBpos _ h1 _ h0).ne', (lt_of_le_of_lt hr₁ h1.1).ne',
      (Real.sin_pos_of_pos_of_lt_pi h2.1 h2.2).ne'⟩
  have hz1 : ∀ z ∈ UU r₁ r₂ t₁ t₂, 0 < z 1 := fun z hz => lt_of_le_of_lt hr₁ hz.1.1
  have hzc : ∀ z ∈ UU r₁ r₂ t₁ t₂, z 1 - c ≠ 0 := by
    intro z hz
    have h1 := hBpos _ hz.1 _ hz.2.1
    rw [(hrep _ hz.1 _ hz.2.1).2.2] at h1
    have h2 : 0 < 1 - c / z 1 := inv_pos.mp h1
    have h3 := hz1 z hz
    have h4 : 0 < z 1 - c := by
      have h5 := mul_pos h2 h3
      rwa [sub_mul, div_mul_cancel₀ _ h3.ne', one_mul] at h5
    exact h4.ne'
  have eBz : ∀ z ∈ UU r₁ r₂ t₁ t₂, aa B z = z 1 / (z 1 - c) := by
    intro z hz
    show B (z 1) (z 0) = _
    rw [(hrep _ hz.1 _ hz.2.1).2.2, one_sub_div (hz1 z hz).ne', inv_div]
  have hb0 : ∀ y ∈ UU r₁ r₂ t₁ t₂, partialD 0 (aa B) y = 0 := by
    intro y hy
    rw [pd_congrU hU eBz hy, pd_comp1 (hphi_d c (y 1) (hzc y hy)) 0]
    simp
  have eB1z : ∀ z ∈ UU r₁ r₂ t₁ t₂, partialD 1 (aa B) z = -c / (z 1 - c) ^ 2 := by
    intro z hz
    rw [pd_congrU hU eBz hz, pd_comp1 (hphi_d c (z 1) (hzc z hz)) 1]
    simp
  have eB11 : partialD 1 (partialD 1 (aa B)) x = 2 * c / (x 1 - c) ^ 3 := by
    rw [pd_congrU hU eB1z hx, pd_comp1 (hphi1_d c (x 1) (hzc x hx)) 1]
    simp
  have hx1c : 1 - c / x 1 ≠ 0 := by
    rw [one_sub_div (hz1 x hx).ne']
    exact div_ne_zero (hzc x hx) (hz1 x hx).ne'
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℝ, g = fun t => A (x 1) t / (1 - c / x 1) := ⟨_, rfl⟩
  have eAz : ∀ z ∈ UU r₁ r₂ t₁ t₂, aa A z = g (z 0) * (1 - c / z 1) := by
    intro z hz
    rw [hgdef]
    show A (z 1) (z 0) = A (x 1) (z 0) / (1 - c / x 1) * (1 - c / z 1)
    rw [(hrep _ hz.1 _ hz.2.1).2.1, (hrep _ hx.1 _ hz.2.1).2.1]
    field_simp
  have hgc : ContDiffOn ℝ ∞ g (Set.Ioo t₁ t₂) := by
    have hL : ContDiff ℝ ∞ (fun t : ℝ => (x 1, t)) := by fun_prop
    rw [hgdef]
    exact (hA.comp hL.contDiffOn (fun t ht => ⟨hx.1, ht⟩)).div_const _
  have hg : ∀ t ∈ Set.Ioo t₁ t₂, HasDerivAt g (deriv g t) t := by
    intro t ht
    exact ((hgc.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
  have eA1z : ∀ z ∈ UU r₁ r₂ t₁ t₂, partialD 1 (aa A) z = g (z 0) * (c / z 1 ^ 2) := by
    intro z hz
    rw [pd_congrU hU eAz hz, pd_prod01 (hg _ hz.2.1) (hk_d c (z 1) (hz1 z hz).ne') 1]
    simp
  have eA0 : partialD 0 (aa A) x = deriv g (x 0) * (1 - c / x 1) := by
    rw [pd_congrU hU eAz hx, pd_prod01 (hg _ hx.2.1) (hk_d c (x 1) (hz1 x hx).ne') 0]
    simp
  have eA01 : partialD 0 (partialD 1 (aa A)) x = deriv g (x 0) * (c / x 1 ^ 2) := by
    rw [pd_congrU hU eA1z hx, pd_prod01 (hg _ hx.2.1) (hk1_d c (x 1) (hz1 x hx).ne') 0]
    simp
  have eA11 : partialD 1 (partialD 1 (aa A)) x = g (x 0) * (-2 * c / x 1 ^ 3) := by
    rw [pd_congrU hU eA1z hx, pd_prod01 (hg _ hx.2.1) (hk1_d c (x 1) (hz1 x hx).ne') 1]
    simp
  have eA := eAz x hx
  have hG : g (x 0) ≠ 0 := by
    have h := (hpos x hx).1
    rw [eA] at h
    exact left_ne_zero_of_mul h
  exact ricZ A B _ hU ha hb hpos hb0 x hx c (g (x 0)) (deriv g (x 0)) (hzc x hx) hG eA eA0
    (eA1z x hx) eA01 eA11 (eBz x hx) (eB1z x hx) eB11 μ ν

end BirkB

open CarrollGR in open scoped ContDiff in
theorem BirkB_fwd (GN : ℝ) (hGN : 0 < GN) (A B : ℝ → ℝ → ℝ) (r₁ r₂ t₁ t₂ : ℝ) (hr₁ : 0 ≤ r₁)
    (hA : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => A p.1 p.2) (Set.Ioo r₁ r₂ ×ˢ Set.Ioo t₁ t₂))
    (hB : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => B p.1 p.2) (Set.Ioo r₁ r₂ ×ˢ Set.Ioo t₁ t₂))
    (hApos : ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂, 0 < A r t)
    (hBpos : ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂, 0 < B r t)
    (hvac : ∀ x : Coord, x 1 ∈ Set.Ioo r₁ r₂ → x 0 ∈ Set.Ioo t₁ t₂ → x 2 ∈ Set.Ioo 0 Real.pi →
      ∀ μ ν : Fin 4, ricci (sphericalMetric A B) μ ν x = 0) :
    ∃ m : ℝ, ∃ f : ℝ → ℝ, ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂,
      0 < f t ∧ A r t = f t * (1 - 2 * GN * m / r) ∧ B r t = (1 - 2 * GN * m / r)⁻¹ := by
  by_cases hJ : r₁ < r₂
  swap
  · exact ⟨0, fun _ => 1, fun r hr => absurd (hr.1.trans hr.2) hJ⟩
  by_cases hI : t₁ < t₂
  swap
  · exact ⟨0, fun _ => 1, fun r _ t ht => absurd (ht.1.trans ht.2) hI⟩
  have hU := BirkB.UU_open r₁ r₂ t₁ t₂
  have ha := BirkB.aa_smooth hA
  have hb := BirkB.aa_smooth hB
  have hpos : ∀ y ∈ BirkB.UU r₁ r₂ t₁ t₂, BirkB.aa A y ≠ 0 ∧ BirkB.aa B y ≠ 0 ∧ y 1 ≠ 0 ∧
      Real.sin (y 2) ≠ 0 := by
    intro y hy
    obtain ⟨h1, h0, h2⟩ := hy
    exact ⟨(hApos _ h1 _ h0).ne', (hBpos _ h1 _ h0).ne', (lt_of_le_of_lt hr₁ h1.1).ne',
      (Real.sin_pos_of_pos_of_lt_pi h2.1 h2.2).ne'⟩
  have hvac' : ∀ y ∈ BirkB.UU r₁ r₂ t₁ t₂, ∀ μ ν : Fin 4,
      ricci (sphericalMetric A B) μ ν y = 0 := fun y hy => hvac y hy.1 hy.2.1 hy.2.2
  have hb0 : ∀ y ∈ BirkB.UU r₁ r₂ t₁ t₂, partialD 0 (BirkB.aa B) y = 0 := by
    intro y hy
    have h := hvac' y hy 0 1
    rw [BirkB.ric01 A B _ hU ha hb hpos y hy] at h
    obtain ⟨_, hB0, hr, _⟩ := hpos y hy
    rcases div_eq_zero_iff.1 h with h | h
    · exact h
    · exact absurd h (mul_ne_zero hr hB0)
  have hcomb : ∀ y ∈ BirkB.UU r₁ r₂ t₁ t₂,
      partialD 1 (BirkB.aa A) y / BirkB.aa A y + partialD 1 (BirkB.aa B) y / BirkB.aa B y = 0 := by
    intro y hy
    have h := BirkB.ric0011 A B _ hU ha hb hpos hb0 y hy
    rw [hvac' y hy 0 0, hvac' y hy 1 1] at h
    obtain ⟨_, _, hr, _⟩ := hpos y hy
    have h' : (partialD 1 (BirkB.aa A) y / BirkB.aa A y
        + partialD 1 (BirkB.aa B) y / BirkB.aa B y) / y 1 = 0 := by
      rw [← h]; ring
    exact (div_eq_zero_iff.1 h').resolve_right hr
  have h22 : ∀ y ∈ BirkB.UU r₁ r₂ t₁ t₂,
      1 - 1 / BirkB.aa B y + y 1 * partialD 1 (BirkB.aa B) y / BirkB.aa B y ^ 2 = 0 := by
    intro y hy
    have h := BirkB.ric22 A B _ hU ha hb hpos y hy
    rw [hvac' y hy 2 2] at h
    have hc := hcomb y hy
    obtain ⟨hA0, hB0, hr, _⟩ := hpos y hy
    linear_combination (-1 : ℝ) * h + (y 1 / (2 * BirkB.aa B y)) * hc
  have memP : ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂,
      (![t, r, Real.pi / 2, 0] : Coord) ∈ BirkB.UU r₁ r₂ t₁ t₂ := by
    intro r hr t ht
    refine ⟨hr, ht, ?_⟩
    show Real.pi / 2 ∈ Set.Ioo 0 Real.pi
    constructor <;> linarith [Real.pi_pos]
  obtain ⟨tm, htm⟩ : ∃ tm, tm ∈ Set.Ioo t₁ t₂ := ⟨(t₁ + t₂) / 2, by constructor <;> linarith⟩
  obtain ⟨rm, hrm⟩ : ∃ rm, rm ∈ Set.Ioo r₁ r₂ := ⟨(r₁ + r₂) / 2, by constructor <;> linarith⟩
  have hBt : ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂, B r t = B r tm := by
    intro r hr t ht
    refine BirkB.const_Ioo (f := fun s => B r s) (fun s hs => ?_) ht htm
    have h := BirkB.dT hU hb r s (memP r hr s hs)
    rwa [hb0 _ (memP r hr s hs)] at h
  have hk : ∀ r ∈ Set.Ioo r₁ r₂, r - r / B r tm = rm - rm / B rm tm := by
    intro r hr
    refine BirkB.const_Ioo (f := fun s => s - s / B s tm) (fun s hs => ?_) hr hrm
    have hd := BirkB.dR hU hb s tm (memP s hs tm htm)
    have hBne : B s tm ≠ 0 := (hBpos s hs tm htm).ne'
    have h := (hasDerivAt_id' s).sub ((hasDerivAt_id' s).div hd hBne)
    have e : 1 - 1 / B s tm
        + s * partialD 1 (BirkB.aa B) (![tm, s, Real.pi / 2, 0] : Coord) / B s tm ^ 2 = 0 :=
      h22 _ (memP s hs tm htm)
    refine h.congr_deriv ?_
    set d := partialD 1 (BirkB.aa B) (![tm, s, Real.pi / 2, 0] : Coord) with hd'
    rw [show (1:ℝ) - (1 * B s tm - s * d) / B s tm ^ 2 = 1 - 1 / B s tm + s * d / B s tm ^ 2 by
      field_simp; ring]
    exact e
  set C := rm - rm / B rm tm with hC
  have hBform : ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂, 1 - C / r = (B r t)⁻¹ := by
    intro r hr t ht
    rw [hBt r hr t ht, ← hk r hr]
    have hr0 : r ≠ 0 := (lt_of_le_of_lt hr₁ hr.1).ne'
    have hB0 : B r tm ≠ 0 := (hBpos r hr tm htm).ne'
    field_simp
    ring
  have hAB : ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂, A r t * B r t = A rm t * B rm t := by
    intro r hr t ht
    refine BirkB.const_Ioo (f := fun s => A s t * B s t) (fun s hs => ?_) hr hrm
    have hdA := BirkB.dR hU ha s t (memP s hs t ht)
    have hdB := BirkB.dR hU hb s t (memP s hs t ht)
    have hc : partialD 1 (BirkB.aa A) (![t, s, Real.pi / 2, 0] : Coord) / A s t
        + partialD 1 (BirkB.aa B) (![t, s, Real.pi / 2, 0] : Coord) / B s t = 0 :=
      hcomb _ (memP s hs t ht)
    have hA0 : A s t ≠ 0 := (hApos s hs t ht).ne'
    have hB0 : B s t ≠ 0 := (hBpos s hs t ht).ne'
    refine (hdA.mul hdB).congr_deriv ?_
    have e : partialD 1 (BirkB.aa A) (![t, s, Real.pi / 2, 0] : Coord) * B s t
        + A s t * partialD 1 (BirkB.aa B) (![t, s, Real.pi / 2, 0] : Coord)
        = (A s t * B s t) * (partialD 1 (BirkB.aa A) (![t, s, Real.pi / 2, 0] : Coord) / A s t
          + partialD 1 (BirkB.aa B) (![t, s, Real.pi / 2, 0] : Coord) / B s t) := by
      field_simp
    rw [e, hc, mul_zero]
  refine ⟨C / (2 * GN), fun t => A rm t * B rm t, fun r hr t ht => ?_⟩
  have hm : 2 * GN * (C / (2 * GN)) = C := by field_simp
  rw [hm, hBform r hr t ht, inv_inv]
  refine ⟨mul_pos (hApos rm hrm t ht) (hBpos rm hrm t ht), ?_, rfl⟩
  show A r t = A rm t * B rm t * (B r t)⁻¹
  rw [← hAB r hr t ht]
  have hB0 : B r t ≠ 0 := (hBpos r hr t ht).ne'
  field_simp


open CarrollGR in open scoped ContDiff in
theorem solution (GN : ℝ) (hGN : 0 < GN) (A B : ℝ → ℝ → ℝ)
    (r₁ r₂ t₁ t₂ : ℝ) (hr₁ : 0 ≤ r₁)
    (hA : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => A p.1 p.2) (Set.Ioo r₁ r₂ ×ˢ Set.Ioo t₁ t₂))
    (hB : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => B p.1 p.2) (Set.Ioo r₁ r₂ ×ˢ Set.Ioo t₁ t₂))
    (hApos : ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂, 0 < A r t)
    (hBpos : ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂, 0 < B r t) :
    (∀ x : Coord, x 1 ∈ Set.Ioo r₁ r₂ → x 0 ∈ Set.Ioo t₁ t₂ → x 2 ∈ Set.Ioo 0 Real.pi →
        ∀ μ ν : Fin 4, ricci (sphericalMetric A B) μ ν x = 0) ↔
      ∃ m : ℝ, ∃ f : ℝ → ℝ, ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂,
        0 < f t ∧ A r t = f t * (1 - 2 * GN * m / r) ∧ B r t = (1 - 2 * GN * m / r)⁻¹ := by
  constructor
  · intro hvac
    exact BirkB_fwd GN hGN A B r₁ r₂ t₁ t₂ hr₁ hA hB hApos hBpos hvac
  · rintro ⟨m, f, hf⟩ x h1 h0 h2 μ ν
    exact BirkB.rev A B r₁ r₂ t₁ t₂ (2 * GN * m) hr₁ hA hB hApos hBpos f hf x ⟨h1, h0, h2⟩ μ ν
