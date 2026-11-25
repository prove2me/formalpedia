-- Prove2me | solution 1 for Formalism.L2.Pj.GenericSectionMinimum.IsDer.ofLoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:45.965031+00:00
-- url     : https://prove2.me/submissions/1302b1c6-f957-4046-9b34-07b6d7607a0f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open Formalism.L2.Pj.GenericSectionMinimum.IsDer
variable {A : Type*} [CommRing A] {δ : A → A}
namespace Formalism.L2.Pj.GenericSectionMinimum.IsDer
theorem _root_.solution {B : Type*} [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B] (d : A → B)
    (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = algebraMap A B x * d y + algebraMap A B y * d x) :
    ∃ δ' : B → B, IsDer δ' ∧ ∀ a, δ' (algebraMap A B a) = d a := by
  have d1 : d 1 = 0 := by
    have e := hmul 1 1
    simp only [mul_one, map_one, one_mul] at e
    linear_combination -e
  have d0 : d 0 = 0 := by
    have e := hadd 0 0
    simp only [add_zero] at e
    linear_combination -e

  let ψ : A →+* TrivSqZeroExt B B :=
    { toFun := fun a => TrivSqZeroExt.inl (algebraMap A B a) + TrivSqZeroExt.inr (d a)
      map_one' := by ext <;> simp [d1]
      map_mul' := fun x y => by
        ext
        · simp
        · simp [hmul, TrivSqZeroExt.snd_mul]; ring
      map_zero' := by ext <;> simp [d0]
      map_add' := fun x y => by
        ext
        · simp
        · simp [hadd] }
  have hψ : ∀ s : S, IsUnit (ψ s) := by
    intro s
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa [ψ] using IsLocalization.map_units B s
  let φ : B →+* TrivSqZeroExt B B := IsLocalization.lift hψ
  have hφ : ∀ a, φ (algebraMap A B a) = ψ a := IsLocalization.lift_eq hψ
  let fst : TrivSqZeroExt B B →+* B :=
    { toFun := TrivSqZeroExt.fst
      map_one' := rfl
      map_mul' := fun x y => TrivSqZeroExt.fst_mul x y
      map_zero' := rfl
      map_add' := fun x y => rfl }
  have hfst : ∀ x, (φ x).fst = x := by
    have e : fst.comp φ = RingHom.id B := by
      apply IsLocalization.ringHom_ext S
      ext a
      simp only [RingHom.comp_apply, RingHom.id_apply, hφ]
      show TrivSqZeroExt.fst (ψ a) = _
      simp [ψ]
    intro x
    exact congrArg (fun f : B →+* B => f x) e
  refine ⟨fun x => (φ x).snd, ⟨fun x y => by simp, fun x y => ?_⟩, fun a => by simp [hφ, ψ]⟩
  simp only [map_mul, TrivSqZeroExt.snd_mul, hfst, smul_eq_mul, op_smul_eq_mul]
  ring
end Formalism.L2.Pj.GenericSectionMinimum.IsDer
