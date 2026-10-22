-- Prove2me | solution 1 for BirkhoffGlobalSection.saddle_center_local_ambient_rotation_growth
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-28T03:39:51.506986+00:00
-- url     : https://prove2.me/submissions/df39b75b-8016-40a2-872f-4efdfc007c51

import Theorems.Thm_BirkhoffGlobalSection_saddle_center_linear_system_rotation_growth
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_leviCivita_explicit_derivatives
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_BirkhoffGlobalSection_AmbientRotation
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Linarith

namespace BirkhoffGlobalSection.TangentialHessian

noncomputable section
open scoped ContDiff

/-- Smoothness of the Levi-Civita Hamiltonian away from its unregularized collision. -/
theorem leviCivita_contDiffAt_on_U (μ c : ℝ) (s : Phase) (hs : s ∈ U) :
    ContDiffAt ℝ ∞ (leviCivitaHamiltonian μ c) s := by
  have hD : ContDiffAt ℝ ∞ secondCollisionDistanceSq s := by
    unfold secondCollisionDistanceSq
    fun_prop
  have hpos : 0 < secondCollisionDistanceSq s := hs
  have hsqrt : ContDiffAt ℝ ∞ (fun x => Real.sqrt (secondCollisionDistanceSq x)) s :=
    hD.sqrt (ne_of_gt hpos)
  have hnz : Real.sqrt (secondCollisionDistanceSq s) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  unfold leviCivitaHamiltonian wNormSq zNormSq
  fun_prop

/-- Exact ambient linearization of the Levi-Civita Hamiltonian vector field. -/
theorem leviCivita_vectorField_fderiv (μ c : ℝ) (s : Phase) (hs : s ∈ U) (v : Phase) :
    fderiv ℝ (hamiltonianVectorField (leviCivitaHamiltonian μ c)) s v =
      qI.mulVec ((kHess μ c s).mulVec v) := by
  have hF := leviCivita_contDiffAt_on_U μ c s hs
  have hp : ∀ i, DifferentiableAt ℝ
      (fun x => partialDerivative (leviCivitaHamiltonian μ c) x i) s := by
    intro i
    unfold partialDerivative
    exact ((hF.fderiv_right (m := 1) (by decide)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hX : DifferentiableAt ℝ (hamiltonianVectorField (leviCivitaHamiltonian μ c)) s := by
    apply differentiableAt_pi.2
    intro i
    fin_cases i
    · simpa [hamiltonianVectorField] using hp 2
    · simpa [hamiltonianVectorField] using hp 3
    · simpa [hamiltonianVectorField, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        using (hp 0).neg
    · simpa [hamiltonianVectorField, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        using (hp 1).neg
  have hc (i : Fin 4) :
      (fderiv ℝ (hamiltonianVectorField (leviCivitaHamiltonian μ c)) s v) i =
        fderiv ℝ (fun x => hamiltonianVectorField (leviCivitaHamiltonian μ c) x i) s v := by
    simpa using (congrArg (fun A => A v) (fderiv_apply hX i)).symm
  have he (i : Fin 4) :
      fderiv ℝ (fun x => partialDerivative (leviCivitaHamiltonian μ c) x i) s v =
        ∑ l, v l * kHess μ c s i l := by
    have h := (leviCivita_explicit_derivatives μ c).2.1 s hs (coordinateVector i) v
    simpa [partialDerivative, coordinateVector] using h
  ext i
  rw [hc]
  fin_cases i <;>
    simp [hamiltonianVectorField, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, fderiv_neg, hp, he, qI, Matrix.mulVec,
      dotProduct, Fin.sum_univ_four, mul_comm]

/-- Symmetry of the explicit Levi-Civita Hessian at every totalized input. -/
theorem kHess_symmetric (μ c : ℝ) (s : Phase) (i j : Fin 4) :
    kHess μ c s i j = kHess μ c s j i := by
  have hp : hP μ c s i j = hP μ c s j i := by
    fin_cases i <;> fin_cases j <;>
      simp [hP, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have hz : hZ i j = hZ j i := by
    fin_cases i <;> fin_cases j <;>
      simp [hZ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have hd : hD s i j = hD s j i := by
    fin_cases i <;> fin_cases j <;>
      simp [hD, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  unfold kHess kHessR
  rw [hp, hz, hd]
  ring

end
end BirkhoffGlobalSection.TangentialHessian

namespace BirkhoffGlobalSection

open TangentialHessian

theorem hamiltonian_pairing_constant
    (K : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (hK : ∀ t, (K t).IsSymm)
    (u v : ℝ → Phase)
    (hu : ∀ t, HasDerivAt u (qI.mulVec ((K t).mulVec (u t))) t)
    (hv : ∀ t, HasDerivAt v (qI.mulVec ((K t).mulVec (v t))) t)
    (t : ℝ) :
    u t ⬝ᵥ qI.mulVec (v t) = u 0 ⬝ᵥ qI.mulVec (v 0) := by
  let f : ℝ → ℝ := fun s =>
    u s 0 * v s 2 + u s 1 * v s 3 - u s 2 * v s 0 - u s 3 * v s 1
  have hf : ∀ s, HasDerivAt f 0 s := by
    intro s
    have hu' := (hasDerivAt_pi.mp (hu s))
    have hv' := (hasDerivAt_pi.mp (hv s))
    have h := (((hu' 0).mul (hv' 2)).add ((hu' 1).mul (hv' 3))).sub
      ((hu' 2).mul (hv' 0))
    have h' := h.sub ((hu' 3).mul (hv' 1))
    have hs01 := (hK s).apply 0 1
    have hs02 := (hK s).apply 0 2
    have hs03 := (hK s).apply 0 3
    have hs12 := (hK s).apply 1 2
    have hs13 := (hK s).apply 1 3
    have hs23 := (hK s).apply 2 3
    convert h' using 1 <;> (try rfl) <;>
      (try simp [f, qI, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        hs01, hs02, hs03, hs12, hs13, hs23]) <;> ring
  have heq : f t = f 0 :=
    is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt)
      (fun s => (hf s).deriv) t 0
  simpa [f, qI, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, sub_eq_add_neg,
    mul_add, add_mul, mul_neg, neg_mul, add_assoc] using heq

theorem symmetric_variational_solution_preserves_symplectic
    (K : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (hK : ∀ t, (K t).IsSymm)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase)
    (hY : ∀ (t : ℝ) (v : Phase), HasDerivAt (fun s => Y s v)
      (qI.mulVec ((K t).mulVec (Y t v))) t)
    (t : ℝ) (u v : Phase) :
    (Y t u) ⬝ᵥ qI.mulVec (Y t v) = u ⬝ᵥ qI.mulVec v := by
  have h := hamiltonian_pairing_constant K hK (fun s => Y s u) (fun s => Y s v)
    (fun s => hY s u) (fun s => hY s v) t
  simpa only [hY0, ContinuousLinearMap.id_apply] using h

end BirkhoffGlobalSection

namespace BirkhoffGlobalSection

open TangentialHessian

/-- Every selected-component trajectory remains in the smooth regularization domain. -/
theorem leviCivita_trajectory_mem_U (μ c : ℝ) (x : ℝ → Phase)
    (hx : ∀ t, x t ∈ leftEnergyComponent μ c) (t : ℝ) : x t ∈ U := by
  have hs : x t ∈ regularEnergyLocus μ c :=
    connectedComponentIn_subset _ _ (hx t)
  exact hs.2

/-- The explicit Hessian is continuous along a global Hamiltonian trajectory. -/
theorem leviCivita_hessian_continuous_along (μ c : ℝ) (x : ℝ → Phase)
    (hx : ∀ t, x t ∈ leftEnergyComponent μ c)
    (hflow : ∀ t, HasDerivAt x
      (hamiltonianVectorField (leviCivitaHamiltonian μ c) (x t)) t) :
    Continuous (fun t => kHess μ c (x t)) := by
  have hxc : Continuous x := continuous_iff_continuousAt.2
    (fun t => (hflow t).continuousAt)
  exact (leviCivita_explicit_derivatives μ c).2.2.2.comp_continuous hxc
    (leviCivita_trajectory_mem_U μ c x hx)

/-- The abstract variational equation is the explicit matrix Hamiltonian system. -/
theorem leviCivita_variational_vector_equation (μ c : ℝ) (x : ℝ → Phase)
    (hx : ∀ t, x t ∈ leftEnergyComponent μ c)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution (leviCivitaHamiltonian μ c) x Y)
    (t : ℝ) (v : Phase) :
    HasDerivAt (fun s => Y s v)
      (qI.mulVec ((kHess μ c (x t)).mulVec (Y t v))) t := by
  have hv := (hY.2 t).clm_apply (hasDerivAt_const t v)
  simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero,
    leviCivita_vectorField_fderiv μ c (x t) (leviCivita_trajectory_mem_U μ c x hx t)]
    using hv

/-- Identity-normalized Levi-Civita variational solutions preserve the symplectic form. -/
theorem leviCivita_variational_symplectic (μ c : ℝ) (x : ℝ → Phase)
    (hx : ∀ t, x t ∈ leftEnergyComponent μ c)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution (leviCivitaHamiltonian μ c) x Y)
    (t : ℝ) (u v : Phase) :
    (Y t u) ⬝ᵥ qI.mulVec (Y t v) = u ⬝ᵥ qI.mulVec v := by
  have hK : ∀ s, (kHess μ c (x s)).IsSymm := by
    intro s
    ext i j
    exact kHess_symmetric μ c (x s) j i
  exact symmetric_variational_solution_preserves_symplectic
    (fun s => kHess μ c (x s)) hK Y hY.1
    (leviCivita_variational_vector_equation μ c x hx Y hY) t u v

end BirkhoffGlobalSection

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian

noncomputable section
open scoped Matrix.Norms.Elementwise

private def zeroEnergyC (p : ℝ × Phase) : ℝ :=
  -leviCivitaHamiltonian p.1 0 p.2 / zNormSq p.2

private def zeroEnergyHess (p : ℝ × Phase) : Matrix (Fin 4) (Fin 4) ℝ :=
  kHess p.1 (zeroEnergyC p) p.2

private theorem zeroEnergyC_cont (p : ℝ × Phase) (hd_pos : 0 < secondCollisionDistanceSq p.2)
    (hz_ne : zNormSq p.2 ≠ 0) : ContinuousAt zeroEnergyC p := by
  have hr : Real.sqrt (secondCollisionDistanceSq p.2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd_pos)
  unfold zeroEnergyC leviCivitaHamiltonian wNormSq zNormSq secondCollisionDistanceSq
  fun_prop (disch := assumption)

private theorem hess_joint_cont (p : ℝ × Phase) (hd_pos : 0 < secondCollisionDistanceSq p.2)
    (hz_ne : zNormSq p.2 ≠ 0) : ContinuousAt zeroEnergyHess p := by
  have hrpos : 0 < rD p.2 := Real.sqrt_pos.2 hd_pos
  have hc : ContinuousAt zeroEnergyC p := zeroEnergyC_cont p hd_pos hz_ne
  have hrcont : ContinuousAt (fun p : ℝ × Phase => rD p.2) p := by
    unfold rD secondCollisionDistanceSq
    fun_prop
  unfold zeroEnergyHess kHess kHessR
  apply continuousAt_pi.2
  intro i
  apply continuousAt_pi.2
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [hP, hZ, dZ, dD, hD, zNormSq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] <;>
    fun_prop (disch := positivity)

private theorem hess_at_saddle (e : ℝ) (he : e = 1 ∨ e = -1) :
    zeroEnergyHess ((1 / 2 : ℝ), (![e / 2, 0, 0, 0] : Phase)) =
      !![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] := by
  rcases he with rfl | rfl <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [zeroEnergyHess, zeroEnergyC, leviCivitaHamiltonian,
      wNormSq, kHess, kHessR, rD, secondCollisionDistanceSq, hP, hZ, dZ, dD, hD,
      zNormSq, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

private theorem zeroEnergyC_eq (μ c : ℝ) (s : Phase) (hz_ne : zNormSq s ≠ 0)
    (henergy : leviCivitaHamiltonian μ c s = 0) : zeroEnergyC (μ, s) = c := by
  have hlin : leviCivitaHamiltonian μ c s = leviCivitaHamiltonian μ 0 s + c * zNormSq s := by
    unfold leviCivitaHamiltonian
    ring
  unfold zeroEnergyC
  dsimp
  apply (div_eq_iff hz_ne).2
  linarith [hlin]

/-- The zero-energy condition makes the full Hessian uniformly close to the
saddle-center Hessian when the mass and spatial point are sufficiently close. -/
theorem BirkhoffGlobalSection.saddle_zero_energy_hessian_localization
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : Set Phase,
      IsOpen V ∧ (![1 / 2, 0, 0, 0] : Phase) ∈ V ∧
      (![-1 / 2, 0, 0, 0] : Phase) ∈ V ∧
      ∀ μ c : ℝ, ∀ s : Phase, |μ - 1 / 2| < ε → s ∈ V →
        leviCivitaHamiltonian μ c s = 0 →
        ‖kHess μ c s -
          !![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1]‖ < δ := by
  let sp : Phase := ![1 / 2, 0, 0, 0]
  let sm : Phase := ![-1 / 2, 0, 0, 0]
  have hdp : 0 < secondCollisionDistanceSq sp := by
    norm_num [sp, secondCollisionDistanceSq]
  have hdm : 0 < secondCollisionDistanceSq sm := by
    norm_num [sm, secondCollisionDistanceSq]
  have hzp : zNormSq sp ≠ 0 := by norm_num [sp, zNormSq]
  have hzm : zNormSq sm ≠ 0 := by norm_num [sm, zNormSq]
  obtain ⟨rp, hrp, hp⟩ := Metric.continuousAt_iff.1
    (hess_joint_cont ((1 / 2 : ℝ), sp) hdp hzp) δ hδ
  obtain ⟨rm, hrm, hm⟩ := Metric.continuousAt_iff.1
    (hess_joint_cont ((1 / 2 : ℝ), sm) hdm hzm) δ hδ
  let V : Set Phase := (Metric.ball sp rp ∪ Metric.ball sm rm) ∩ {s | zNormSq s ≠ 0}
  have hZcont : Continuous zNormSq := by unfold zNormSq; fun_prop
  have hV : IsOpen V :=
    (Metric.isOpen_ball.union Metric.isOpen_ball).inter (isOpen_ne.preimage hZcont)
  refine ⟨min rp rm, lt_min hrp hrm, V, hV, ?_, ?_, ?_⟩
  · exact ⟨Or.inl (Metric.mem_ball_self hrp), hzp⟩
  · exact ⟨Or.inr (Metric.mem_ball_self hrm), hzm⟩
  intro μ c s hμ hs henergy
  have heq : zeroEnergyHess (μ, s) = kHess μ c s := by
    unfold zeroEnergyHess
    rw [zeroEnergyC_eq μ c s hs.2 henergy]
  rcases hs.1 with hsp | hsm
  · have hdist : dist (μ, s) ((1 / 2 : ℝ), sp) < rp := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by simpa [Real.dist_eq] using lt_of_lt_of_le hμ (min_le_left rp rm), hsp⟩
    have h := hp hdist
    rw [heq] at h
    have hbase := hess_at_saddle 1 (Or.inl rfl)
    change zeroEnergyHess ((1 / 2 : ℝ), sp) = _ at hbase
    rw [hbase] at h
    simpa [dist_eq_norm] using h
  · have hdist : dist (μ, s) ((1 / 2 : ℝ), sm) < rm := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by simpa [Real.dist_eq] using lt_of_lt_of_le hμ (min_le_right rp rm), hsm⟩
    have h := hm hdist
    rw [heq] at h
    have hbase := hess_at_saddle (-1) (Or.inr rfl)
    change zeroEnergyHess ((1 / 2 : ℝ), sm) = _ at hbase
    rw [hbase] at h
    simpa [dist_eq_norm] using h


/-- Uniform Hessian control near both lifted saddle-centers, in a common mass neighborhood. -/
theorem BirkhoffGlobalSection.saddleCenter_local_hessian_control
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ V : Set Phase, IsOpen V ∧ (![1 / 2, 0, 0, 0] : Phase) ∈ V ∧
      (![-1 / 2, 0, 0, 0] : Phase) ∈ V ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ μ c : ℝ, |μ - 1 / 2| < ε → ∀ s : Phase, s ∈ V →
        leviCivitaHamiltonian μ c s = 0 →
        ‖kHess μ c s -
          !![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1]‖ < δ := by
  obtain ⟨ε, hε, V, hV, hsp, hsm, hclose⟩ := saddle_zero_energy_hessian_localization δ hδ
  exact ⟨V, hV, hsp, hsm, ε, hε, fun μ c hμ s hs henergy => hclose μ c s hμ hs henergy⟩

end

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian
open scoped ContDiff Matrix.Norms.Elementwise

theorem solution (R : ℝ) :
    ∃ U : Set Phase, IsOpen U ∧
      (![1 / 2, 0, 0, 0] : Phase) ∈ U ∧ (![-(1 / 2), 0, 0, 0] : Phase) ∈ U ∧
      ∃ ε η L : ℝ, 0 < ε ∧ 0 < η ∧ 0 < L ∧
        ∀ μ c : ℝ, 0 < μ → μ < 1 →
          |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
          ∀ x : ℝ → Phase,
            (∀ t : ℝ, x t ∈ leftEnergyComponent μ c) →
            (∀ t : ℝ, HasDerivAt x
              (hamiltonianVectorField (leviCivitaHamiltonian μ c) (x t)) t) →
            ∀ Y : ℝ → (Phase →L[ℝ] Phase),
              IsHamiltonianVariationalSolution (leviCivitaHamiltonian μ c) x Y →
              ∀ α : ℝ → ℝ, IsAmbientRotationAngle Y α →
                ∀ a : ℝ, (∀ t ∈ Set.Icc a (a + L), x t ∈ U) →
                  R < α (a + L) - α a := by
  obtain ⟨δ, L, hδ, hL, hgrowth⟩ := saddle_center_linear_system_rotation_growth R
  obtain ⟨V, hV, hp, hm, ε, hε, hclose⟩ := saddleCenter_local_hessian_control δ hδ
  refine ⟨V, hV, hp, by simpa only [neg_div] using hm, ε, 1, L, hε, by norm_num, hL, ?_⟩
  intro μ c _ _ hμ _ _ x hx hflow Y hY α hα a hresident
  apply hgrowth a (fun t => kHess μ c (x t))
    (leviCivita_hessian_continuous_along μ c x hx hflow).continuousOn
  · intro t _ i j
    exact kHess_symmetric μ c (x t) i j
  · intro t ht
    have hs : x t ∈ regularEnergyLocus μ c := connectedComponentIn_subset _ _ (hx t)
    exact hclose μ c hμ (x t) (hresident t ht) hs.1
  · exact leviCivita_variational_symplectic μ c x hx Y hY a
  · intro t _ v
    exact leviCivita_variational_vector_equation μ c x hx Y hY t v
  · exact hα
