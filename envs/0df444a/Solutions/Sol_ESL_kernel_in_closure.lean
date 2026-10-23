-- Prove2me | solution 1 for ESL.kernel_in_closure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:29:35.878948+00:00
-- url     : https://prove2.me/submissions/3c6b6626-2833-4b87-b6ec-995b72c4c270

import Mathlib
import Definitions.Def_ESL_alg
import Definitions.Def_ESL_tor

open ESL


theorem esl84_theta {n : ℕ} {PB_D PB_M HhatD HhatM Pi : Type*}
    [Group PB_D] [Group PB_M] [Group HhatD] [Group HhatM] [Group Pi]
    (W : StringLinkExactWorld n PB_D PB_M HhatD HhatM Pi) :
    ∃ thetahat : HhatM →* Pi, ∀ x : PB_M, thetahat (W.qM x) = W.theta x := by
  have hs : Function.Surjective W.qM := W.qMsurj
  let e := QuotientGroup.quotientKerEquivOfSurjective W.qM hs
  have hle : W.qM.ker ≤ W.theta.ker := by
    rw [W.qMker]; intro x hx; exact W.thetaKill x hx
  refine ⟨(QuotientGroup.lift W.qM.ker W.theta hle).comp e.symm.toMonoidHom, fun x => ?_⟩
  have : e.symm (W.qM x) = (x : PB_M ⧸ W.qM.ker) := by
    apply e.injective; simp only [MulEquiv.apply_symm_apply]; rfl
  simp [this]

theorem esl84_finj {n : ℕ} {PB_D PB_M HhatD HhatM Pi : Type*}
    [Group PB_D] [Group PB_M] [Group HhatD] [Group HhatM] [Group Pi]
    (W : StringLinkExactWorld n PB_D PB_M HhatD HhatM Pi) :
    ∀ fhat : HhatD →* HhatM, (∀ x : PB_D, fhat (W.qD x) = W.qM (W.f x)) →
      ∀ y z : HhatD, fhat y = fhat z → y = z := by
  intro fhat hf
  have key : ∀ y, fhat y = 1 → y = 1 := by
    intro y hy
    obtain ⟨x, rfl⟩ := W.qDsurj y
    rw [hf] at hy
    have h1 : W.f x ∈ W.HM := by rw [← W.qMker]; exact hy
    have h2 := W.diskTrivial x h1
    rw [← W.qDker] at h2; exact h2
  intro y z h
  have := key (y * z⁻¹) (by rw [map_mul, map_inv, h, mul_inv_cancel])
  exact mul_inv_eq_one.mp this

theorem esl84_img {n : ℕ} {PB_D PB_M HhatD HhatM Pi : Type*}
    [Group PB_D] [Group PB_M] [Group HhatD] [Group HhatM] [Group Pi]
    (W : StringLinkExactWorld n PB_D PB_M HhatD HhatM Pi) :
    ∀ fhat : HhatD →* HhatM, (∀ x : PB_D, fhat (W.qD x) = W.qM (W.f x)) →
      ∀ thetahat : HhatM →* Pi, (∀ x : PB_M, thetahat (W.qM x) = W.theta x) →
        ∀ y : HhatM, (∃ x : HhatD, fhat x = y) → thetahat y = 1 := by
  rintro fhat hf thetahat ht y ⟨x, rfl⟩
  obtain ⟨z, rfl⟩ := W.qDsurj x
  rw [hf, ht]
  have : W.f z ∈ W.theta.ker := by
    rw [W.goldberg]; exact Subgroup.subset_normalClosure ⟨z, rfl⟩
  exact this

theorem esl84_cl {n : ℕ} {PB_D PB_M HhatD HhatM Pi : Type*}
    [Group PB_D] [Group PB_M] [Group HhatD] [Group HhatM] [Group Pi]
    (W : StringLinkExactWorld n PB_D PB_M HhatD HhatM Pi) :
    ∀ fhat : HhatD →* HhatM, (∀ x : PB_D, fhat (W.qD x) = W.qM (W.f x)) →
      ∀ thetahat : HhatM →* Pi, (∀ x : PB_M, thetahat (W.qM x) = W.theta x) →
        Subgroup.normalClosure (Set.range fhat) ≤ MonoidHom.ker thetahat := by
  intro fhat hf thetahat ht
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨x, rfl⟩
  exact esl84_img W fhat hf thetahat ht _ ⟨x, rfl⟩

theorem esl84_ker {n : ℕ} {PB_D PB_M HhatD HhatM Pi : Type*}
    [Group PB_D] [Group PB_M] [Group HhatD] [Group HhatM] [Group Pi]
    (W : StringLinkExactWorld n PB_D PB_M HhatD HhatM Pi) :
    ∀ fhat : HhatD →* HhatM, (∀ x : PB_D, fhat (W.qD x) = W.qM (W.f x)) →
      ∀ thetahat : HhatM →* Pi, (∀ x : PB_M, thetahat (W.qM x) = W.theta x) →
        MonoidHom.ker thetahat ≤ Subgroup.normalClosure (Set.range fhat) := by
  intro fhat hf thetahat ht c hc
  obtain ⟨x, rfl⟩ := W.qMsurj c
  rw [MonoidHom.mem_ker, ht] at hc
  have hx : x ∈ Subgroup.normalClosure (Set.range W.f) := by
    rw [← W.goldberg]; exact hc
  have hle : Subgroup.normalClosure (Set.range W.f) ≤
      (Subgroup.normalClosure (Set.range fhat)).comap W.qM := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨y, rfl⟩
    show W.qM (W.f y) ∈ Subgroup.normalClosure (Set.range fhat)
    rw [← hf]; exact Subgroup.subset_normalClosure ⟨_, rfl⟩
  exact hle hx

theorem esl84_surj {n : ℕ} {PB_D PB_M HhatD HhatM Pi : Type*}
    [Group PB_D] [Group PB_M] [Group HhatD] [Group HhatM] [Group Pi]
    (W : StringLinkExactWorld n PB_D PB_M HhatD HhatM Pi) :
    ∀ thetahat : HhatM →* Pi, (∀ x : PB_M, thetahat (W.qM x) = W.theta x) →
      ∀ y : Pi, ∃ c : HhatM, thetahat c = y := by
  intro thetahat ht y
  obtain ⟨x, rfl⟩ := W.thetaSurj y
  exact ⟨W.qM x, ht x⟩

/-- Counterexample world: `f = id` on `Multiplicative (ZMod 2)`, `HD = ⊤`, `HM = ⊥`. -/
abbrev Z2 := Multiplicative (ZMod 2)

def esl84_world : StringLinkExactWorld 0 Z2 Z2 Unit Z2 Unit where
  HD := ⊤
  HDnormal := inferInstance
  HM := ⊥
  HMnormal := inferInstance
  qD := 1
  qDker := by ext; simp
  qDsurj := fun _ => ⟨1, rfl⟩
  qM := MonoidHom.id _
  qMker := by ext; simp
  qMsurj := fun y => ⟨y, rfl⟩
  f := MonoidHom.id _
  diskTrivial := fun _ _ => Subgroup.mem_top _
  theta := 1
  thetaSurj := fun _ => ⟨1, rfl⟩
  thetaKill := fun _ _ => rfl
  goldberg := by
    rw [MonoidHom.ker_one, MonoidHom.coe_id, Set.range_id]
    exact (eq_top_iff.mpr (fun x _ => Subgroup.subset_normalClosure (Set.mem_univ x))).symm

theorem esl84_nofhat : ¬ ∃ fhat : Unit →* Z2,
    ∀ x : Z2, fhat (esl84_world.qD x) = esl84_world.qM (esl84_world.f x) := by
  rintro ⟨fhat, h⟩
  have := h (Multiplicative.ofAdd 1)
  have h1 : fhat (esl84_world.qD (Multiplicative.ofAdd 1)) = 1 := by
    have : esl84_world.qD (Multiplicative.ofAdd 1) = 1 := rfl
    rw [this, map_one]
  rw [h1] at this
  exact absurd this.symm (by decide)


/-!  Milestone 6 (Lemma 3.4): the kernel of theta-hat is contained in the
normal closure of the image of f-hat. A class killed by theta-hat is
represented by a pure braid whose theta_n image is trivial; by Goldberg's
theorem such a braid lies in the normal closure of the image of f_n, and
passing to the quotient exhibits the class in the normal closure of the
image of f-hat. -/
theorem solution {n : ℕ} {PB_D PB_M HhatD HhatM Pi : Type*}
    [Group PB_D] [Group PB_M] [Group HhatD] [Group HhatM] [Group Pi]
    (W : StringLinkExactWorld n PB_D PB_M HhatD HhatM Pi) :
    ∀ fhat : HhatD →* HhatM, (∀ x : PB_D, fhat (W.qD x) = W.qM (W.f x)) →
      ∀ thetahat : HhatM →* Pi, (∀ x : PB_M, thetahat (W.qM x) = W.theta x) →
        MonoidHom.ker thetahat ≤ Subgroup.normalClosure (Set.range fhat) := by
  exact esl84_ker W


