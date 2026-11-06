-- Prove2me | solution 1 for ExpConeIPM.Corrector.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T12:15:13.583215+00:00
-- url     : https://prove2.me/submissions/895c5ac4-f166-427b-b584-39fa0536e766

import Mathlib
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_ExpConeIPM_Corrector_HomogeneousModel
import Definitions.Def_ExpConeIPM_Corrector_SearchDirections

open scoped InnerProductSpace

namespace L4Aux
open SelfScaledIPM.ShortStep

/-- Euler identity `F'(y)[y] = -ν` from logarithmic homogeneity along the ray through `y`. -/
lemma euler1 {N : ℕ} (F : EuclideanSpace ℝ (Fin N) → ℝ) (ν : ℝ) (y : EuclideanSpace ℝ (Fin N))
    (hd : DifferentiableAt ℝ F y)
    (hh : ∀ t : ℝ, 0 < t → F (t • y) = F y - ν * Real.log t) :
    fderiv ℝ F y y = -ν := by
  have h2 : HasDerivAt (fun t : ℝ => t • y) y 1 := by
    simpa using (hasDerivAt_id (1:ℝ)).smul_const y
  have h1 : HasDerivAt (fun t : ℝ => F (t • y)) (fderiv ℝ F y y) 1 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (1:ℝ) h2 (by simp)
  have h3 : HasDerivAt (fun t : ℝ => F y - ν * Real.log t) (-ν) 1 := by
    have := ((Real.hasDerivAt_log one_ne_zero).const_mul ν).const_sub (F y)
    simpa using this
  have h4 : (fun t : ℝ => F (t • y)) =ᶠ[nhds 1] (fun t : ℝ => F y - ν * Real.log t) := by
    filter_upwards [lt_mem_nhds (show (0:ℝ) < 1 by norm_num)] with t ht
    exact hh t ht
  exact h1.unique (h3.congr_of_eventuallyEq h4)

section
variable {N : ℕ} (F : EuclideanSpace ℝ (Fin N) → ℝ) (ν : ℝ) (U : Set (EuclideanSpace ℝ (Fin N)))
  (hU : IsOpen U) (hcone : ∀ y ∈ U, ∀ t : ℝ, 0 < t → t • y ∈ U)
  (hC : ContDiffOn ℝ 3 F U)
  (hh : ∀ y ∈ U, ∀ t : ℝ, 0 < t → F (t • y) = F y - ν * Real.log t)
include hU hC

lemma diffF {y} (hy : y ∈ U) : DifferentiableAt ℝ F y :=
  (hC.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)

lemma grad_eq : gradient F = fun y => (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ F y) := by
  funext y; rfl

lemma contDiffOn_grad : ContDiffOn ℝ 2 (gradient F) U := by
  rw [grad_eq F U hU hC]
  have h := hC.fderiv_of_isOpen hU (m := 2) (by norm_num)
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm.contDiff.comp_contDiffOn h

lemma diffGrad {y} (hy : y ∈ U) : DifferentiableAt ℝ (gradient F) y :=
  ((contDiffOn_grad F U hU hC).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)

lemma contDiffOn_hess : ContDiffOn ℝ 1 (hess F) U :=
  (contDiffOn_grad F U hU hC).fderiv_of_isOpen hU (by norm_num)

lemma diffHess {y} (hy : y ∈ U) : DifferentiableAt ℝ (hess F) y :=
  ((contDiffOn_hess F U hU hC).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)

lemma hess_inner {y} (hy : y ∈ U) (a b : EuclideanSpace ℝ (Fin N)) :
    ⟪b, hess F y a⟫_ℝ = fderiv ℝ (fderiv ℝ F) y a b := by
  have e : (fun z => ⟪b, gradient F z⟫_ℝ) = fun z => fderiv ℝ F z b := by
    funext z; rw [real_inner_comm]; simp [gradient]
  have d1 : HasFDerivAt (fun z => ⟪b, gradient F z⟫_ℝ)
      ((innerSL ℝ b).comp (hess F y)) y :=
    (innerSL ℝ b).hasFDerivAt.comp y (diffGrad F U hU hC hy).hasFDerivAt
  have hdf : DifferentiableAt ℝ (fderiv ℝ F) y :=
    ((hC.fderiv_of_isOpen hU (m := 2) (by norm_num)).contDiffAt
      (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have d2 : HasFDerivAt (fun z => fderiv ℝ F z b)
      ((ContinuousLinearMap.apply ℝ ℝ b).comp (fderiv ℝ (fderiv ℝ F) y)) y :=
    (ContinuousLinearMap.apply ℝ ℝ b).hasFDerivAt.comp y hdf.hasFDerivAt
  rw [e] at d1
  have := congrArg (fun L => L a) (d1.unique d2)
  simpa using this

lemma hess_symm {y} (hy : y ∈ U) (a b : EuclideanSpace ℝ (Fin N)) :
    ⟪b, hess F y a⟫_ℝ = ⟪hess F y b, a⟫_ℝ := by
  rw [show ⟪hess F y b, a⟫_ℝ = ⟪a, hess F y b⟫_ℝ from real_inner_comm _ _,
    hess_inner F U hU hC hy, hess_inner F U hU hC hy]
  have hs := (hC.contDiffAt (hU.mem_nhds hy)).isSymmSndFDerivAt (n := 3) (by simp; norm_cast)
  exact hs a b

include hcone hh

lemma fderiv_scale {y} (hy : y ∈ U) {t : ℝ} (ht : 0 < t) :
    fderiv ℝ F (t • y) = t⁻¹ • fderiv ℝ F y := by
  have hty := hcone y hy t ht
  have d1 : HasFDerivAt (fun z => F (t • z)) ((fderiv ℝ F (t • y)).comp (t • ContinuousLinearMap.id ℝ _)) y :=
    (diffF F U hU hC hty).hasFDerivAt.comp y ((ContinuousLinearMap.id ℝ _).hasFDerivAt.const_smul t)
  have d2 : HasFDerivAt (fun z => F z - ν * Real.log t) (fderiv ℝ F y) y :=
    (diffF F U hU hC hy).hasFDerivAt.sub_const _
  have e : (fun z => F (t • z)) =ᶠ[nhds y] (fun z => F z - ν * Real.log t) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact hh z hz t ht
  have := d1.unique (d2.congr_of_eventuallyEq e)
  ext v
  have hv := congrArg (fun L => L (t⁻¹ • v)) this
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.id_apply, smul_smul, mul_inv_cancel₀ ht.ne', one_smul] at hv
  rw [hv, FunLike.coe_smul, Pi.smul_apply, map_smul]

lemma grad_scale {y} (hy : y ∈ U) {t : ℝ} (ht : 0 < t) :
    gradient F (t • y) = t⁻¹ • gradient F y := by
  rw [grad_eq F U hU hC]
  simp only
  rw [fderiv_scale F ν U hU hcone hC hh hy ht, map_smul]

lemma hess_euler {y} (hy : y ∈ U) : hess F y y = -gradient F y := by
  have h2 : HasDerivAt (fun t : ℝ => t • y) y 1 := by
    simpa using (hasDerivAt_id (1:ℝ)).smul_const y
  have h1 : HasDerivAt (fun t : ℝ => gradient F (t • y)) (hess F y y) 1 :=
    (diffGrad F U hU hC hy).hasFDerivAt.comp_hasDerivAt_of_eq (1:ℝ) h2 (by simp)
  have h3 : HasDerivAt (fun t : ℝ => t⁻¹ • gradient F y) (-gradient F y) 1 := by
    have := (hasDerivAt_inv (one_ne_zero (α := ℝ))).smul_const (gradient F y)
    simpa using this
  have h4 : (fun t : ℝ => gradient F (t • y)) =ᶠ[nhds 1] (fun t : ℝ => t⁻¹ • gradient F y) := by
    filter_upwards [lt_mem_nhds (show (0:ℝ) < 1 by norm_num)] with t ht
    exact grad_scale F ν U hU hcone hC hh hy ht
  exact h1.unique (h3.congr_of_eventuallyEq h4)

lemma third_euler {x} (hx : x ∈ U) (u : EuclideanSpace ℝ (Fin N)) :
    fderiv ℝ (hess F) x u x = (-2 : ℝ) • hess F x u := by
  have d1 : HasFDerivAt (fun z => hess F z z + gradient F z)
      (((hess F x).comp (ContinuousLinearMap.id ℝ _) + (fderiv ℝ (hess F) x).flip x) + hess F x) x :=
    ((diffHess F U hU hC hx).hasFDerivAt.clm_apply (hasFDerivAt_id x)).add
      (diffGrad F U hU hC hx).hasFDerivAt
  have e : (fun z => hess F z z + gradient F z) =ᶠ[nhds x] (fun _ => 0) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    rw [hess_euler F ν U hU hcone hC hh hz]; simp
  have := d1.unique ((hasFDerivAt_const 0 x).congr_of_eventuallyEq e)
  have hv := congrArg (fun L => L u) this
  simp at hv
  have : fderiv ℝ (hess F) x u x = -(hess F x u + hess F x u) := by
    rw [← sub_eq_zero]; rw [← hv]; abel
  rw [this]; module

lemma third_symm {x} (hx : x ∈ U) (u a b : EuclideanSpace ℝ (Fin N)) :
    ⟪b, fderiv ℝ (hess F) x u a⟫_ℝ = ⟪fderiv ℝ (hess F) x u b, a⟫_ℝ := by
  have hd := (diffHess F U hU hC hx).hasFDerivAt
  have hA : HasFDerivAt (fun z => hess F z a)
      ((hess F x).comp (0 : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) +
        (fderiv ℝ (hess F) x).flip a) x := hd.clm_apply (hasFDerivAt_const a x)
  have hB : HasFDerivAt (fun z => hess F z b)
      ((hess F x).comp (0 : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) +
        (fderiv ℝ (hess F) x).flip b) x := hd.clm_apply (hasFDerivAt_const b x)
  have d1 := (innerSL ℝ b).hasFDerivAt.comp x hA
  have d2' := (innerSL ℝ a).hasFDerivAt.comp x hB
  have d2 := d2'.congr_of_eventuallyEq (f₁ := fun z => ⟪hess F z b, a⟫_ℝ) (by
    filter_upwards with z
    simp [real_inner_comm])
  have e : (fun z => ⟪b, hess F z a⟫_ℝ) =ᶠ[nhds x] (fun z => ⟪hess F z b, a⟫_ℝ) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact hess_symm F U hU hC hz a b
  have := (d1.congr_of_eventuallyEq (f₁ := fun z => ⟪b, hess F z a⟫_ℝ) (by
    filter_upwards with z; rfl)).unique (d2.congr_of_eventuallyEq e)
  have hv := congrArg (fun L => L u) this
  simpa [real_inner_comm] using hv

lemma inner_corrector {x} (hx : x ∈ U) (dxa dsa : EuclideanSpace ℝ (Fin N))
    (horth : ⟪dxa, dsa⟫_ℝ = 0) :
    ⟪x, ExpConeIPM.Corrector.corrector F x dxa dsa⟫_ℝ = 0 := by
  unfold ExpConeIPM.Corrector.corrector
  rw [inner_smul_right, third_symm F ν U hU hcone hC hh hx, third_euler F ν U hU hcone hC hh hx,
    inner_smul_left]
  by_cases hH : (hess F x).IsInvertible
  · obtain ⟨e, he⟩ := hH
    rw [← real_inner_comm, hess_symm F U hU hC hx, ← he, ContinuousLinearMap.inverse_equiv]
    simp [real_inner_comm, horth]
  · rw [ContinuousLinearMap.inverse_of_not_isInvertible hH]; simp
end


section aug
open ExpConeIPM.Corrector

variable {n : ℕ}

noncomputable def hatL : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := hatPart
      map_add' := fun x y => by ext i; simp [hatPart]
      map_smul' := fun c x => by ext i; simp [hatPart] }

noncomputable def lastL : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := lastCoord
      map_add' := fun x y => by simp [lastCoord]
      map_smul' := fun c x => by simp [lastCoord] }

lemma hatL_apply (x : EuclideanSpace ℝ (Fin (n+1))) : hatL x = hatPart x := rfl
lemma lastL_apply (x : EuclideanSpace ℝ (Fin (n+1))) : lastL x = lastCoord x := rfl

lemma hatPart_add (x y : EuclideanSpace ℝ (Fin (n+1))) : hatPart (x + y) = hatPart x + hatPart y :=
  map_add (hatL (n := n)) x y
lemma hatPart_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin (n+1))) : hatPart (c • x) = c • hatPart x :=
  map_smul (hatL (n := n)) c x
lemma lastCoord_add (x y : EuclideanSpace ℝ (Fin (n+1))) :
    lastCoord (x + y) = lastCoord x + lastCoord y := map_add (lastL (n := n)) x y
lemma lastCoord_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    lastCoord (c • x) = c * lastCoord x := map_smul (lastL (n := n)) c x

lemma mem_U {Khat : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin (n+1))}
    (hx : x ∈ interior (augCone Khat)) : hatPart x ∈ interior Khat ∧ 0 < lastCoord x := by
  have hs1 : Function.Surjective ((hatL (n := n)).toLinearMap) := by
    intro y
    refine ⟨WithLp.toLp 2 (Fin.snoc (fun i => y i) 0 : Fin (n+1) → ℝ), ?_⟩
    ext i; simp [hatL_apply, hatPart, Fin.snoc_castSucc]
  have hs2 : Function.Surjective ((lastL (n := n)).toLinearMap) := by
    intro r
    refine ⟨WithLp.toLp 2 (fun _ => r), ?_⟩
    simp [lastL_apply, lastCoord]
  have ho1 := LinearMap.isOpenMap_of_finiteDimensional _ hs1
  have ho2 := LinearMap.isOpenMap_of_finiteDimensional _ hs2
  have i1 : hatPart '' interior (augCone Khat) ⊆ interior Khat :=
    interior_maximal (by rintro _ ⟨z, hz, rfl⟩; exact (interior_subset hz).1)
      (ho1 _ isOpen_interior)
  have i2 : lastCoord '' interior (augCone Khat) ⊆ interior (Set.Ici 0) :=
    interior_maximal (by rintro _ ⟨z, hz, rfl⟩; exact (interior_subset hz).2)
      (ho2 _ isOpen_interior)
  rw [interior_Ici] at i2
  exact ⟨i1 ⟨x, hx, rfl⟩, i2 ⟨x, hx, rfl⟩⟩

lemma inner_split (x s : EuclideanSpace ℝ (Fin (n+1))) :
    ⟪x, s⟫_ℝ = ⟪hatPart x, hatPart s⟫_ℝ + lastCoord x * lastCoord s := by
  simp [PiLp.inner_apply, Fin.sum_univ_castSucc, hatPart, lastCoord]
  ring

lemma Winner (W : EuclideanSpace ℝ (Fin (n+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (a b : EuclideanSpace ℝ (Fin (n+1))) : ⟪W a, invT W b⟫_ℝ = ⟪a, b⟫_ℝ := by
  unfold invT
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp

noncomputable def P {m : ℕ} (x : EuclideanSpace ℝ (Fin (n+1))) (y : EuclideanSpace ℝ (Fin m))
    (r : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) × ℝ) : ℝ :=
  ⟪y, r.1⟫_ℝ + ⟪hatPart x, r.2.1⟫_ℝ + lastCoord x * r.2.2

lemma P_smul {m : ℕ} (x : EuclideanSpace ℝ (Fin (n+1))) (y : EuclideanSpace ℝ (Fin m)) (k : ℝ)
    (r : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) × ℝ) :
    P x y (k • r) = k * P x y r := by
  simp only [P, Prod.smul_fst, Prod.smul_snd, inner_smul_right, smul_eq_mul]; ring

lemma skew {m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (x s : EuclideanSpace ℝ (Fin (n + 1))) (y : EuclideanSpace ℝ (Fin m))
    (x' s' : EuclideanSpace ℝ (Fin (n + 1))) (y' : EuclideanSpace ℝ (Fin m)) :
    P x' y' (residual A b c x s y) + P x y (residual A b c x' s' y') =
      -(⟪x', s⟫_ℝ + ⟪x, s'⟫_ℝ) := by
  simp only [P, ExpConeIPM.Corrector.residual, inner_split, inner_add_right, inner_sub_right, inner_neg_right,
    inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_comm b y', real_inner_comm b y, real_inner_comm c (hatPart x),
    real_inner_comm c (hatPart x'), real_inner_comm (A (hatPart x)) y',
    real_inner_comm (A (hatPart x')) y]
  ring

lemma orth_of {m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (x s : EuclideanSpace ℝ (Fin (n + 1))) (y : EuclideanSpace ℝ (Fin m))
    (dx ds : EuclideanSpace ℝ (Fin (n + 1))) (dy : EuclideanSpace ℝ (Fin m)) (k : ℝ)
    (hres : residual A b c dx ds dy = (-k) • residual A b c x s y)
    (hlin : ⟪s, dx⟫_ℝ + ⟪x, ds⟫_ℝ = -k * ⟪x, s⟫_ℝ) : ⟪dx, ds⟫_ℝ = 0 := by
  have h1 := skew A b c x s y x s y
  have h2 := skew A b c x s y dx ds dy
  have h3 := skew A b c dx ds dy dx ds dy
  rw [hres, P_smul] at h2 h3
  rw [real_inner_comm s dx] at h2
  linear_combination (1/2 : ℝ) * h3 + k * h2 + (k^2/2) * h1 - k * hlin

lemma residual_lin {m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (x s : EuclideanSpace ℝ (Fin (n + 1))) (y : EuclideanSpace ℝ (Fin m))
    (dx ds : EuclideanSpace ℝ (Fin (n + 1))) (dy : EuclideanSpace ℝ (Fin m)) (α : ℝ) :
    residual A b c (x + α • dx) (s + α • ds) (y + α • dy) =
      residual A b c x s y + α • residual A b c dx ds dy := by
  simp only [ExpConeIPM.Corrector.residual, hatPart_add, hatPart_smul, lastCoord_add, lastCoord_smul, map_add,
    map_smul, inner_add_right, inner_smul_right, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only; module
  · simp only; module
  · simp only; ring

end aug

end L4Aux

open scoped Pointwise in
open ExpConeIPM.Corrector L4Aux in
theorem solution {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (hA : Function.Surjective A)
    (Khat : Set (EuclideanSpace ℝ (Fin n))) (Fhat : EuclideanSpace ℝ (Fin n) → ℝ) (ϑhat : ℝ)
    (hK : SelfScaledIPM.ShortStep.IsProperCone Khat)
    (hF : SelfScaledIPM.ShortStep.IsLogHomBarrier Khat Fhat ϑhat)
    (x s : EuclideanSpace ℝ (Fin (n + 1))) (y : EuclideanSpace ℝ (Fin m))
    (hz : IsInteriorIterate Khat x s)
    (W : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (hW : IsDoubleSecantScaling (augCone Khat) (augBarrier Fhat) x s W)
    (dxa dsa : EuclideanSpace ℝ (Fin (n + 1))) (dya : EuclideanSpace ℝ (Fin m))
    (ha : IsAffineDirection A b c x s y W dxa dsa dya)
    (γ : ℝ) (hγ : 0 < γ)
    (dx ds : EuclideanSpace ℝ (Fin (n + 1))) (dy : EuclideanSpace ℝ (Fin m))
    (hd : IsCombinedDirection A b c Khat Fhat ϑhat x s y W
      (corrector (augBarrier Fhat) x dxa dsa) γ dx ds dy) :
    ⟪s, dx⟫_ℝ + ⟪x, ds⟫_ℝ = -(1 - γ) * ⟪x, s⟫_ℝ ∧ ⟪dx, ds⟫_ℝ = 0 ∧
      ∀ α : ℝ,
        residual A b c (x + α • dx) (s + α • ds) (y + α • dy) =
            (1 - α * (1 - γ)) • residual A b c x s y ∧
          ⟪x + α • dx, s + α • ds⟫_ℝ = (1 - α * (1 - γ)) * ⟪x, s⟫_ℝ := by
  obtain ⟨hxK, -⟩ := hz
  obtain ⟨hKcl, hKcv, hKcone, -, -⟩ := hK
  obtain ⟨⟨-, hFC, -⟩, -, hFpar, hFhom, hFpd⟩ := hF
  set F := augBarrier Fhat with hFdef
  set U : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {y | hatPart y ∈ interior Khat ∧ 0 < lastCoord y} with hUdef
  have hU : IsOpen U :=
    (isOpen_interior.preimage (hatL (n := n)).continuous).inter
      (isOpen_Ioi.preimage (lastL (n := n)).continuous)
  have hint : ∀ v ∈ interior Khat, ∀ t : ℝ, 0 < t → t • v ∈ interior Khat := by
    intro v hv t ht
    have h1 : t • interior Khat ⊆ interior Khat := by
      rw [← interior_smul₀ ht.ne']
      apply interior_mono
      rintro _ ⟨w, hw, rfl⟩
      exact hKcone w hw t ht.le
    exact h1 ⟨v, hv, rfl⟩
  have hcone : ∀ y ∈ U, ∀ t : ℝ, 0 < t → t • y ∈ U := by
    intro y hy t ht
    refine ⟨?_, ?_⟩
    · rw [hatPart_smul]; exact hint _ hy.1 t ht
    · rw [lastCoord_smul]; exact mul_pos ht hy.2
  have hC : ContDiffOn ℝ 3 F U := by
    have h1 : ContDiffOn ℝ 3 (fun y => Fhat (hatL y)) U :=
      hFC.comp (hatL (n := n)).contDiff.contDiffOn (fun y hy => hy.1)
    have h2 : ContDiffOn ℝ 3 (fun y => Real.log (lastL y)) U :=
      Real.contDiffOn_log.comp (lastL (n := n)).contDiff.contDiffOn
        (fun y hy => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hy.2.ne')
    exact h1.sub h2
  have hh : ∀ y ∈ U, ∀ t : ℝ, 0 < t → F (t • y) = F y - (ϑhat + 1) * Real.log t := by
    intro y hy t ht
    simp only [hFdef, augBarrier, hatPart_smul, lastCoord_smul]
    rw [hFhom _ hy.1 t ht, Real.log_mul ht.ne' hy.2.ne']
    ring
  have hxU : x ∈ U := mem_U hxK
  -- ϑ̂ ≥ 0
  have hϑ : 0 ≤ ϑhat := by
    have hx1 := hxU.1
    have hdF : DifferentiableAt ℝ Fhat (hatPart x) :=
      diffF Fhat (interior Khat) isOpen_interior hFC hx1
    have he := euler1 Fhat ϑhat (hatPart x) hdF (fun t ht => hFhom _ hx1 t ht)
    have hp := hFpar _ hx1 (hatPart x)
    rw [he] at hp
    by_cases h0 : hatPart x = 0
    · rw [h0, map_zero] at he; linarith
    · have hq := hFpd _ hx1 _ h0
      nlinarith
  -- affine direction: linear identity and orthogonality
  obtain ⟨hv, hvt⟩ := hW
  have hA1 : ⟪s, dxa⟫_ℝ + ⟪x, dsa⟫_ℝ = -⟪x, s⟫_ℝ := by
    have e := congrArg (fun z => ⟪W x, z⟫_ℝ) ha.2
    simp only [inner_add_right, inner_neg_right] at e
    have f1 : ⟪W x, W dxa⟫_ℝ = ⟪s, dxa⟫_ℝ := by
      rw [hv, real_inner_comm, Winner, real_inner_comm]
    have f3 : ⟪W x, W x⟫_ℝ = ⟪x, s⟫_ℝ := by
      rw [show ⟪W x, W x⟫_ℝ = ⟪W x, invT W s⟫_ℝ by rw [← hv], Winner]
    rw [f1, Winner, f3] at e
    exact e
  have hAorth : ⟪dxa, dsa⟫_ℝ = 0 :=
    orth_of A b c x s y dxa dsa dya 1 (by rw [ha.1, neg_one_smul]) (by rw [hA1]; ring)
  have hη : ⟪x, corrector F x dxa dsa⟫_ℝ = 0 :=
    inner_corrector F (ϑhat + 1) U hU hcone hC hh hxU dxa dsa hAorth
  have hE : fderiv ℝ F x x = -(ϑhat + 1) :=
    euler1 F _ x (diffF F U hU hC hxU) (fun t ht => hh x hxU t ht)
  have hxs : ⟪x, shadowS F x⟫_ℝ = ϑhat + 1 := by
    unfold shadowS
    rw [inner_neg_right, real_inner_comm, grad_eq F U hU hC]
    simp only [InnerProductSpace.toDual_symm_apply]
    rw [hE]; ring
  -- first identity
  have hL : ⟪s, dx⟫_ℝ + ⟪x, ds⟫_ℝ = -(1 - γ) * ⟪x, s⟫_ℝ := by
    have e := congrArg (fun z => ⟪W x, z⟫_ℝ) hd.2
    simp only [inner_add_right, inner_sub_right, inner_neg_right, inner_smul_right] at e
    have f1 : ⟪W x, W dx⟫_ℝ = ⟪s, dx⟫_ℝ := by
      rw [hv, real_inner_comm, Winner, real_inner_comm]
    have f3 : ⟪W x, W x⟫_ℝ = ⟪x, s⟫_ℝ := by
      rw [show ⟪W x, W x⟫_ℝ = ⟪W x, invT W s⟫_ℝ by rw [← hv], Winner]
    have f4 : ⟪W x, W (shadowX (augCone Khat) (augBarrier Fhat) s)⟫_ℝ = ϑhat + 1 := by
      rw [hvt, Winner]; exact hxs
    rw [f1, Winner, f3, f4, Winner, hη] at e
    rw [e]
    unfold mu augParam
    field_simp
    ring
  have hO : ⟪dx, ds⟫_ℝ = 0 :=
    orth_of A b c x s y dx ds dy (1 - γ) hd.1 hL
  refine ⟨hL, hO, fun α => ⟨?_, ?_⟩⟩
  · rw [residual_lin, hd.1, smul_smul]
    module
  · simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    rw [hO, real_inner_comm s dx]
    linear_combination α * hL
