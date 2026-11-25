-- Prove2me | solution 1 for CompanionTheory.Split.reps_Umax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:41.034218+00:00
-- url     : https://prove2.me/submissions/0081c006-27ac-4b1a-a52e-f91aa7bcd21a

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
import Theorems.Thm_CompanionTheory_Split_ALint_eq
import Theorems.Thm_CompanionTheory_Split_mem_UJ_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_ClassSetFinite
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_Final_StabStd
import Theorems.Thm_Formalism_UG_Final_StdFormDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut TensorProduct Formalism.UG Formalism.L2
noncomputable section
open CompanionTheory CompanionTheory.Split
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => maximalRealSubfield L
namespace CompanionTheory.Split
theorem _root_.solution : ∃ T : Set (GA L n), T.Finite ∧ ∀ g, ∃ γ ∈ GQ L n, ∃ t ∈ T, ∃ κ ∈ Umax L n, g = γ * t * κ := by
  let σ : L →ₐ[L⁺] L := (IsCMField.complexConj L).toAlgHom
  have hσ : ∀ τ : L →+* ℂ, τ.comp (σ : L →+* L) = (starRingEnd ℂ).comp τ := fun τ =>
    RingHom.ext fun x => IsCMField.complexEmbedding_complexConj L τ x
  obtain ⟨h1, h2, -⟩ := Final.StdFormDef L⁺ L (Fin n) σ hσ
    (fun e he => ⟨⟨e, (IsCMField.complexConj_eq_self_iff L e).1 he⟩, rfl⟩) inferInstance
  have hfin := Final.ClassSetFinite L⁺ L (Fin n) σ 1 hσ h1 (by simp) h2
  have hU : ∀ g, g ∈ UPts σ (1 : Matrix (Fin n) (Fin n) L) (AFplus L) ↔ g ∈ GA L n := fun g => by
    rw [UPts, Matrix.map_one _ (map_zero _) (map_one _)]
    exact mem_UJ_one _ (conjAL_conjAL L) g
  let e : UPts σ (1 : Matrix (Fin n) (Fin n) L) (AFplus L) → GA L n := fun x => ⟨x, (hU x).1 x.2⟩
  refine ⟨Set.range fun q : ClassSet _ _ => e q.out, @Set.finite_range _ _ _ hfin, fun g => ?_⟩
  set q := DoubleCoset.mk ((ratPts σ (1 : Matrix (Fin n) (Fin n) L) (AFplus L)).subgroupOf _)
    ((levelAf σ 1).subgroupOf _) (⟨g, (hU g).2 g.2⟩ : UPts σ (1 : Matrix (Fin n) (Fin n) L) (AFplus L)) with hq
  obtain ⟨γ, κ, hγ, hκ, h⟩ := DoubleCoset.mk_out_eq_mul
    ((ratPts σ (1 : Matrix (Fin n) (Fin n) L) (AFplus L)).subgroupOf _) ((levelAf σ 1).subgroupOf _) ⟨g, (hU g).2 g.2⟩
  refine ⟨(e γ)⁻¹, (GQ L n).inv_mem ?_, e q.out, ⟨q, rfl⟩, (e κ)⁻¹, (Umax L n).inv_mem (show e κ ∈ Umax L n from fun i j => ?_), ?_⟩
  · obtain ⟨γ₀, h0, e0⟩ := Subgroup.mem_subgroupOf.1 hγ
    exact Subgroup.mem_subgroupOf.2 ⟨γ₀, (mem_UJ_one _ (complexConj_invol L) γ₀).1 h0, e0⟩
  · have := (Subgroup.mem_subgroupOf.1 hκ).2
    rw [Final.StabStd _ _ _ Subtype.val_injective] at this
    obtain ⟨a, ha⟩ := this
    rw [ALint_eq]
    have e1 := congrArg (fun M : GL (Fin n) (AL L) => (M : Matrix (Fin n) (Fin n) (AL L)) i j) ha
    refine (show ((κ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ tensInt (F := L⁺) (AFplus L) (intOE L) (intAd L⁺) from ?_)
    rw [← e1]
    exact ((a : Matrix (Fin n) (Fin n) (tensInt (F := L⁺) (AFplus L) (intOE L) (intAd L⁺))) i j).2
  · have h' : (q.out : GL (Fin n) (AL L)) = γ * g * κ := congrArg Subtype.val h
    refine Subtype.ext ?_
    show (g : GL (Fin n) (AL L)) = ((γ : GL (Fin n) (AL L)))⁻¹ * q.out * ((κ : GL (Fin n) (AL L)))⁻¹
    rw [h']
    group
end CompanionTheory.Split
