-- Prove2me | solution 1 for ExpConeIPM.Corrector.homogeneity_identities
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T12:19:14.83773+00:00
-- url     : https://prove2.me/submissions/830b7b1d-73c4-4cf6-a09a-8578bab335cd

import Mathlib
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_ExpConeIPM_Corrector_HomogeneousModel
import Definitions.Def_ExpConeIPM_Corrector_SearchDirections

open scoped InnerProductSpace

namespace HomAux
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

lemma hess_scale {y} (hy : y ∈ U) {t : ℝ} (ht : 0 < t) :
    hess F (t • y) = (t ^ 2)⁻¹ • hess F y := by
  have hty := hcone y hy t ht
  have d1 : HasFDerivAt (fun z => gradient F (t • z))
      ((hess F (t • y)).comp (t • ContinuousLinearMap.id ℝ _)) y :=
    (diffGrad F U hU hC hty).hasFDerivAt.comp y
      ((ContinuousLinearMap.id ℝ _).hasFDerivAt.const_smul t)
  have d2 : HasFDerivAt (fun z => t⁻¹ • gradient F z) (t⁻¹ • hess F y) y :=
    (diffGrad F U hU hC hy).hasFDerivAt.const_smul (t⁻¹ : ℝ)
  have e : (fun z => gradient F (t • z)) =ᶠ[nhds y] (fun z => t⁻¹ • gradient F z) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact grad_scale F ν U hU hcone hC hh hz ht
  have := d1.unique (d2.congr_of_eventuallyEq e)
  ext1 v
  have hv := congrArg (fun L => L v) this
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.id_apply, map_smul] at hv
  rw [FunLike.coe_smul, Pi.smul_apply]
  have h' : hess F (t • y) v = t⁻¹ • (t • hess F (t • y) v) := by
    rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  rw [h', hv, smul_smul]
  congr 1; field_simp

lemma third_ray {y} (hy : y ∈ U) : fderiv ℝ (hess F) y y = (-2 : ℝ) • hess F y := by
  have h2 : HasDerivAt (fun t : ℝ => t • y) y 1 := by
    simpa using (hasDerivAt_id (1:ℝ)).smul_const y
  have h1 : HasDerivAt (fun t : ℝ => hess F (t • y)) (fderiv ℝ (hess F) y y) 1 :=
    (diffHess F U hU hC hy).hasFDerivAt.comp_hasDerivAt_of_eq (1:ℝ) h2 (by simp)
  have h3 : HasDerivAt (fun t : ℝ => (t ^ 2)⁻¹ • hess F y) ((-2 : ℝ) • hess F y) 1 := by
    have := ((hasDerivAt_pow 2 (1:ℝ)).inv (by norm_num)).smul_const (hess F y)
    exact this.congr_deriv (by norm_num; module)
  have h4 : (fun t : ℝ => hess F (t • y)) =ᶠ[nhds 1] (fun t : ℝ => (t ^ 2)⁻¹ • hess F y) := by
    filter_upwards [lt_mem_nhds (show (0:ℝ) < 1 by norm_num)] with t ht
    exact hess_scale F ν U hU hcone hC hh hy ht
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

end HomAux

open scoped Pointwise in
open ExpConeIPM.Corrector HomAux in
theorem solution {N : ℕ} (K : Set (EuclideanSpace ℝ (Fin N)))
    (F : EuclideanSpace ℝ (Fin N) → ℝ) (ϑ : ℝ)
    (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (hF : SelfScaledIPM.ShortStep.IsLogHomBarrier K F ϑ)
    (x : EuclideanSpace ℝ (Fin N)) (hx : x ∈ interior K) (τ : ℝ) (hτ : 0 < τ) :
    gradient F (τ • x) = (1 / τ) • gradient F x ∧
      SelfScaledIPM.ShortStep.hess F (τ • x) = (1 / τ ^ 2) • SelfScaledIPM.ShortStep.hess F x ∧
      SelfScaledIPM.ShortStep.hess F x x = -gradient F x ∧
      fderiv ℝ (SelfScaledIPM.ShortStep.hess F) x x = (-2 : ℝ) • SelfScaledIPM.ShortStep.hess F x ∧
      ⟪gradient F x, x⟫_ℝ = -ϑ := by
  obtain ⟨-, -, hKcone, -, -⟩ := hK
  obtain ⟨⟨-, hFC, -⟩, -, -, hFhom, -⟩ := hF
  have hint : ∀ v ∈ interior K, ∀ t : ℝ, 0 < t → t • v ∈ interior K := by
    intro v hv t ht
    have h1 : t • interior K ⊆ interior K := by
      rw [← interior_smul₀ ht.ne']
      apply interior_mono
      rintro _ ⟨w, hw, rfl⟩
      exact hKcone w hw t ht.le
    exact h1 ⟨v, hv, rfl⟩
  have hU : IsOpen (interior K) := isOpen_interior
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [one_div]; exact grad_scale F ϑ _ hU hint hFC hFhom hx hτ
  · rw [one_div]; exact hess_scale F ϑ _ hU hint hFC hFhom hx hτ
  · exact hess_euler F ϑ _ hU hint hFC hFhom hx
  · exact third_ray F ϑ _ hU hint hFC hFhom hx
  · rw [grad_eq F _ hU hFC]
    simp only [InnerProductSpace.toDual_symm_apply]
    exact euler1 F ϑ x (diffF F _ hU hFC hx) (fun t ht => hFhom x hx t ht)
