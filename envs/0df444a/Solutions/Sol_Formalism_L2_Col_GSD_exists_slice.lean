-- Prove2me | solution 1 for Formalism.L2.Col.GSD.exists_slice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:37.510074+00:00
-- url     : https://prove2.me/submissions/28b9aff0-fec8-495a-b376-ff37095bdfc4

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GSD
variable (S : GSD K)
variable (A : Type) [Group A] [MulAction A S.D]
namespace Formalism.L2.Col.GSD
theorem _root_.solution [SMulCommClass A S.G S.D] (hf : S.FreeOnCl A) : Nonempty (S.Slice A) := by
  have := SMulCommClass.symm A S.G S.D
  let r : Setoid S.D :=
    { r := fun d d' => ∃ (a : A) (g : S.G), a • g • d' = d
      iseqv :=
        { refl := fun d => ⟨1, 1, by rw [one_smul, one_smul]⟩
          symm := by
            rintro d d' ⟨a, g, rfl⟩
            exact ⟨a⁻¹, g⁻¹, by rw [smul_comm a⁻¹ g⁻¹, inv_smul_smul, inv_smul_smul]⟩
          trans := by
            rintro d d' d'' ⟨a, g, rfl⟩ ⟨a', g', rfl⟩
            exact ⟨a * a', g * g', by rw [mul_smul, mul_smul, smul_comm g a' (g' • d'')]⟩ } }
  let o : S.D → S.D := fun d => Quotient.out (Quotient.mk r d)
  have ho : ∀ d, ∃ (a : A) (g : S.G), a • g • d = o d := fun d => Quotient.exact (Quotient.out_eq (Quotient.mk r d))
  have hog : ∀ (g : S.G) d, o (g • d) = o d := by
    intro g d
    have : Quotient.mk r (g • d) = Quotient.mk r d := Quotient.sound ⟨1, g, by rw [one_smul]⟩
    show Quotient.out (Quotient.mk r (g • d)) = _
    rw [this]
  have hoa : ∀ (a : A) d, o (a • d) = o d := by
    intro a d
    have : Quotient.mk r (a • d) = Quotient.mk r d := Quotient.sound ⟨a, 1, by rw [one_smul]⟩
    show Quotient.out (Quotient.mk r (a • d)) = _
    rw [this]
  refine ⟨⟨{ carrier := {d | S.cls d = S.cls (o d)}, smul_mem' := ?_ }, ?_⟩⟩
  · intro g d hd
    show S.cls (g • d) = S.cls (o (g • d))
    rw [hog, S.cls_smul]
    exact hd
  · intro d
    obtain ⟨a, g, hag⟩ := ho d
    refine ⟨a, ?_, ?_⟩
    · show S.cls (a • d) = S.cls (o (a • d))
      rw [hoa, ← hag, smul_comm, S.cls_smul]
    · intro b hb
      have hb' : S.cls (b • d) = S.cls (o (b • d)) := hb
      have ha' : S.cls (a • d) = S.cls (o d) := by rw [← hag, smul_comm, S.cls_smul]
      rw [hoa, ← ha'] at hb'
      have h1 : (b * a⁻¹) • (a • d) = b • d := by rw [mul_smul, inv_smul_smul]
      rw [← h1] at hb'
      have h2 := hf _ _ hb'
      exact mul_inv_eq_one.mp h2
end Formalism.L2.Col.GSD
