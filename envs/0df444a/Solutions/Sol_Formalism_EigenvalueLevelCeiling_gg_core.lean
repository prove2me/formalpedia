-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.gg_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:47.906421+00:00
-- url     : https://prove2.me/submissions/21edb7e3-923c-41c6-9d2c-49318c082e07

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_gg_len_range
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_gg_len_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable {R : Type*} [CommRing R] {Y Q : Type*} [AddCommGroup Y] [Module R Y] [AddCommGroup Q]
  [Module R Q]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution {Z : Type*} [AddCommGroup Z] [Module R Z] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : R) (A A' C B B' : Submodule R Z) (s t : ι → Z →ₗ[R] Z)
    (hsA : ∀ i, ∀ a ∈ A, s i a ∈ B) (hsA' : ∀ i, ∀ a ∈ A', s i a ∈ B')
    (htB : ∀ i, ∀ b ∈ B, t i b ∈ A) (htB' : ∀ i, ∀ b ∈ B', t i b ∈ A')
    (hts : ∀ i j, ∀ a ∈ A, t i (s j a) = if i = j then n • a else 0)
    (hC : ∀ c ∈ C, c ∈ A → ∃ a ∈ A, c = n • a) :
    (Fintype.card ι : ℕ∞) * Module.length R (A ⧸ A'.comap A.subtype) ≤
      Module.length R (B ⧸ B'.comap B.subtype) +
        (Fintype.card ι : ℕ∞) * Module.length R (A ⧸ C.comap A.subtype) := by
  have hs' : ∀ i, A'.comap A.subtype ≤ (B'.comap B.subtype).comap ((s i).restrict (hsA i)) := by
    intro i x hx
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.coe_restrict_apply]
    exact hsA' i _ hx
  have ht' : ∀ i, B'.comap B.subtype ≤ (A'.comap A.subtype).comap ((t i).restrict (htB i)) := by
    intro i x hx
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.coe_restrict_apply]
    exact htB' i _ hx
  let sb : ι → (A ⧸ A'.comap A.subtype) →ₗ[R] (B ⧸ B'.comap B.subtype) := fun i =>
    Submodule.mapQ _ _ ((s i).restrict (hsA i)) (hs' i)
  let tb : ι → (B ⧸ B'.comap B.subtype) →ₗ[R] (A ⧸ A'.comap A.subtype) := fun i =>
    Submodule.mapQ _ _ ((t i).restrict (htB i)) (ht' i)
  have hb : ∀ i j y, tb i (sb j y) = if i = j then n • y else 0 := by
    intro i j y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      dsimp only [sb, tb]
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply]
      have e : ((t i).restrict (htB i)) (((s j).restrict (hsA j)) x) =
          if i = j then n • x else 0 := by
        apply Subtype.ext
        rw [LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply, hts i j _ x.2]
        split_ifs <;> simp
      rw [e]
      split_ifs <;> simp
  have k1 := gg_len_range n sb tb hb
  have k2 := gg_len_split (n • (LinearMap.id : (A ⧸ A'.comap A.subtype) →ₗ[R] _))
  have k3 : Module.length R ((A ⧸ A'.comap A.subtype) ⧸
      LinearMap.range (n • (LinearMap.id : (A ⧸ A'.comap A.subtype) →ₗ[R] _))) ≤
      Module.length R (A ⧸ C.comap A.subtype) := by
    let F : (A ⧸ C.comap A.subtype) →ₗ[R] ((A ⧸ A'.comap A.subtype) ⧸
      LinearMap.range (n • (LinearMap.id : (A ⧸ A'.comap A.subtype) →ₗ[R] _))) :=
      Submodule.liftQ _ ((Submodule.mkQ _) ∘ₗ (Submodule.mkQ _)) (by
        intro x hx
        obtain ⟨a, ha, hxa⟩ := hC _ hx x.2
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
        rw [LinearMap.smul_apply, LinearMap.id_apply, ← Submodule.Quotient.mk_smul]
        congr 1
        apply Subtype.ext
        exact hxa.symm)
    refine Module.length_le_of_surjective F ?_
    intro y
    obtain ⟨y1, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨y2, rfl⟩ := Submodule.mkQ_surjective _ y1
    exact ⟨Submodule.Quotient.mk y2, rfl⟩
  rw [k2, mul_add]
  exact add_le_add k1 (mul_le_mul_right k3 _)
end Formalism.EigenvalueLevelCeiling
