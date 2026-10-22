-- Prove2me | solution 2 for BirkhoffGlobalSection.TangentialHessian.quadPos_tHess_of_det_pos
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-26T18:00:42.218011+00:00
-- url     : https://prove2.me/submissions/c22b4106-4ba3-4870-981f-e0d29401d7ac

import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_quadPos_tHess_leftCollisionPoint
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian Matrix
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 200000

private def quadratic (A : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * a j * A i j

private lemma quadratic_dot (A : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) :
    quadratic A a = star a ⬝ᵥ (A *ᵥ a) := by
  simp only [quadratic, dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma quadratic_smul (A : Matrix (Fin 3) (Fin 3) ℝ)
    (a : Fin 3 → ℝ) (r : ℝ) :
    quadratic A (r • a) = r ^ 2 * quadratic A a := by
  simp only [quadratic, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma quadPos_iff_unit (A : Matrix (Fin 3) (Fin 3) ℝ) :
    QuadPos A ↔ ∀ a : Fin 3 → ℝ, ‖a‖ = 1 → 0 < quadratic A a := by
  constructor
  · intro h a ha
    exact h a (by intro hz; simp [hz] at ha)
  · intro h a ha
    have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    have hu : ‖(‖a‖)⁻¹ • a‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg a)),
        inv_mul_cancel₀ hn]
    have hp := h ((‖a‖)⁻¹ • a) hu
    rw [quadratic_smul] at hp
    exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero (inv_ne_zero hn))).mp hp

private lemma isOpen_quadPos :
    IsOpen {A : Matrix (Fin 3) (Fin 3) ℝ | QuadPos A} := by
  rw [isOpen_iff_mem_nhds]
  intro A hA
  have hq : Continuous (fun p : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ) =>
      quadratic p.1 p.2) := by unfold quadratic; fun_prop
  have he := (isCompact_sphere (0 : Fin 3 → ℝ) 1).eventually_forall_of_forall_eventually
    (P := fun B a => 0 < quadratic B a) (x₀ := A) (by
      intro a ha
      have ha' : ‖a‖ = 1 := by simpa using ha
      exact (isOpen_lt continuous_const hq).mem_nhds ((quadPos_iff_unit A).mp hA a ha'))
  filter_upwards [he] with B hB
  apply (quadPos_iff_unit B).mpr
  intro a ha
  exact hB a (by simpa using ha)

private lemma quadPos_iff_nonneg (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A.IsHermitian) (hd : A.det ≠ 0) :
    QuadPos A ↔ ∀ a, 0 ≤ quadratic A a := by
  constructor
  · intro h a
    by_cases ha : a = 0
    · simp [ha, quadratic]
    · exact (h a ha).le
  · intro h
    have hp : A.PosSemidef := Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨hA, fun a => by rw [← quadratic_dot]; exact h a⟩
    have hd' : A.PosDef := hp.posDef_iff_det_ne_zero.mpr hd
    intro a ha
    change 0 < quadratic A a
    rw [quadratic_dot]
    exact hd'.dotProduct_mulVec_pos ha

private lemma continuous_tHess (μ c : ℝ) :
    Continuous (fun s : U => tHess μ c s) := by
  have hr : Continuous (fun s : U => rD s) := by
    apply Continuous.comp (g := rD) _ continuous_subtype_val
    unfold rD secondCollisionDistanceSq
    fun_prop
  have hr0 (s : U) : rD s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr s.property)
  have hZ : Continuous (fun s : U => zNormSq s) :=
    (show Continuous zNormSq by unfold zNormSq; fun_prop).comp continuous_subtype_val
  have hdP : Continuous (fun s : U => dP μ c s) :=
    (show Continuous (dP μ c) by unfold dP; fun_prop).comp continuous_subtype_val
  have hhP : Continuous (fun s : U => hP μ c s) :=
    (show Continuous (hP μ c) by unfold hP; fun_prop).comp continuous_subtype_val
  have hdZ : Continuous (fun s : U => dZ s) :=
    (show Continuous dZ by unfold dZ; fun_prop).comp continuous_subtype_val
  have hdD : Continuous (fun s : U => dD s) :=
    (show Continuous dD by unfold dD; fun_prop).comp continuous_subtype_val
  have hhD : Continuous (fun s : U => hD s) :=
    (show Continuous hD by unfold hD; fun_prop).comp continuous_subtype_val
  have hi1 : Continuous (fun s : U => (rD s)⁻¹) := hr.inv₀ hr0
  have hi3 : Continuous (fun s : U => (2 * rD s ^ 3)⁻¹) :=
    (continuous_const.mul (hr.pow 3)).inv₀
      (fun s => mul_ne_zero (by norm_num) (pow_ne_zero _ (hr0 s)))
  have hi5 : Continuous (fun s : U => (4 * rD s ^ 5)⁻¹) :=
    (continuous_const.mul (hr.pow 5)).inv₀
      (fun s => mul_ne_zero (by norm_num) (pow_ne_zero _ (hr0 s)))
  have hg : Continuous (fun s : U => kGradR μ c (rD s) s) := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp hdP).sub (continuous_const.mul
      ((((continuous_apply i).comp hdZ).div hr hr0).sub
        ((hZ.mul ((continuous_apply i).comp hdD)).mul hi3)))
  have hh : Continuous (fun s : U => kHessR μ c (rD s) s) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [kHessR, div_eq_mul_inv]
    exact (hhP.matrix_elem i j).sub (continuous_const.mul
      (((continuous_const.mul hi1).sub
        (((((continuous_apply i).comp hdZ).mul ((continuous_apply j).comp hdD)).add
          (((continuous_apply j).comp hdZ).mul ((continuous_apply i).comp hdD))).mul hi3)).sub
        ((hZ.mul (hhD.matrix_elem i j)).mul hi3) |>.add
        (((((continuous_const.mul hZ).mul ((continuous_apply i).comp hdD)).mul
          ((continuous_apply j).comp hdD))).mul hi5)))
  have hf : Continuous (fun s : U => frame (kGradR μ c (rD s) s)) := by
    unfold frame
    exact (continuous_const.matrix_mulVec hg).matrixVecCons
      ((continuous_const.matrix_mulVec hg).matrixVecCons
        ((continuous_const.matrix_mulVec hg).matrixVecCons continuous_const))
  have hM (i j : Fin 3) : Continuous (fun s : U =>
      frameHess (kGradR μ c (rD s) s) (kHessR μ c (rD s) s) i j) := by
    unfold frameHess
    exact continuous_finsetSum _ (fun k _ => continuous_finsetSum _ (fun l _ =>
      ((hf.matrix_elem i k).mul (hf.matrix_elem j l)).mul (hh.matrix_elem k l)))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((hM i j).add (hM j i)).div_const 2

theorem solution (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c)
    (hdet : ∀ s ∈ leftEnergyComponent μ c, 0 < (tHess μ c s).det) :
    ∀ s ∈ leftEnergyComponent μ c, QuadPos (tHess μ c s) := by
  let M : LeftEnergyState μ c → Matrix (Fin 3) (Fin 3) ℝ := fun s => tHess μ c s
  have hU (s : LeftEnergyState μ c) : (s : Phase) ∈ U :=
    (connectedComponentIn_subset _ _ s.property).2
  have hinc : Continuous (fun s : LeftEnergyState μ c => (⟨(s : Phase), hU s⟩ : U)) :=
    continuous_subtype_val.subtype_mk hU
  have hM := (continuous_tHess μ c).comp hinc
  change Continuous M at hM
  have hsym (s : LeftEnergyState μ c) : (M s).IsHermitian := by
    apply Matrix.ext
    intro i j
    change star ((M s) j i) = (M s) i j
    rw [star_trivial]
    change (_ + _) / (2 : ℝ) = (_ + _) / 2
    exact congrArg (fun x : ℝ => x / 2) (add_comm _ _)
  have hopen : IsOpen {s | QuadPos (M s)} := isOpen_quadPos.preimage hM
  have hclosed : IsClosed {s | QuadPos (M s)} := by
    have heq : {s | QuadPos (M s)} = ⋂ a, {s | 0 ≤ quadratic (M s) a} := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      exact quadPos_iff_nonneg (M s) (hsym s) (ne_of_gt (hdet s s.property))
    rw [heq]
    apply isClosed_iInter
    intro a
    apply isClosed_le continuous_const
    unfold quadratic
    exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
      continuous_const.mul (hM.matrix_elem i j)))
  have hbase : leftCollisionPoint μ ∈ leftEnergyComponent μ c := by
    apply mem_connectedComponentIn
    have hsqrt := Real.sq_sqrt (show 0 ≤ 1 - μ by linarith)
    constructor
    · simp [leviCivitaHamiltonian, leftCollisionPoint, wNormSq, zNormSq, hsqrt]
    · norm_num [secondCollisionDistanceSq, leftCollisionPoint]
  let : PreconnectedSpace (LeftEnergyState μ c) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponentIn
  have hall : {s | QuadPos (M s)} = Set.univ :=
    (show IsClopen {s | QuadPos (M s)} from ⟨hclosed, hopen⟩).eq_univ
      ⟨⟨leftCollisionPoint μ, hbase⟩, quadPos_tHess_leftCollisionPoint μ c hμ0 hμhalf hc0⟩
  intro s hs
  have hmem : (⟨s, hs⟩ : LeftEnergyState μ c) ∈ {s | QuadPos (M s)} := by
    rw [hall]
    trivial
  exact hmem
