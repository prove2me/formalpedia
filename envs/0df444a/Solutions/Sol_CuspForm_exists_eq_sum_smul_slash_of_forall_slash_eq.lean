-- Prove2me | solution 1 for CuspForm.exists_eq_sum_smul_slash_of_forall_slash_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/f98ba9cb-1ec0-579c-8f14-7150b806672e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_eq_sum_smul_slash_of_forall_slash_eq

set_option autoImplicit false

open scoped ModularForm MatrixGroups Manifold
open UpperHalfPlane OnePoint Matrix.SpecialLinearGroup

namespace SolRD4Aux

lemma isCusp_SL2Z_map_smul {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) (β : GL (Fin 2) ℚ) :
    IsCusp (β.map (Rat.castHom ℝ) • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  refine ⟨β • c₀, ?_⟩
  have h := OnePoint.map_smul (Rat.castHom ℝ) β c₀
  simpa only [Rat.coe_castHom] using h

lemma isCusp_SL2Z_of_isCusp_map {Γ : Subgroup SL(2, ℤ)} {c : OnePoint ℝ}
    (hc : IsCusp c (Subgroup.map (mapGL ℝ) Γ)) : IsCusp c 𝒮ℒ :=
  hc.mono (Subgroup.map_le_range _ _)

lemma isZeroAt_slash_map {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (β : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsZeroAt ((⇑g) ∣[(2 : ℤ)] β.map (Rat.castHom ℝ)) 2 := by
  rw [← OnePoint.IsZeroAt.smul_iff]
  apply CuspFormClass.zero_at_cusps g
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
  exact isCusp_SL2Z_map_smul hc β

lemma isZeroAt_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → UpperHalfPlane → ℂ)
    {x : OnePoint ℝ} (hf : ∀ i ∈ s, x.IsZeroAt (f i) 2) :
    x.IsZeroAt (∑ i ∈ s, c i • f i) 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro γ _
    simp
    exact Filter.zero_zeroAtFilter _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine OnePoint.IsZeroAt.add ?_ (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    intro γ hγ
    rw [ModularForm.smul_slash]
    exact (hf a (Finset.mem_insert_self a s) γ hγ).smul _

lemma mdifferentiable_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → UpperHalfPlane → ℂ)
    (hf : ∀ i ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => (simp; exact mdifferentiable_const)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ((hf a (Finset.mem_insert_self a s)).const_smul _).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end SolRD4Aux

open SolRD4Aux in
open _root_.CuspForm _root_.ModularForm.CuspForm in
theorem solution
    {M N : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    {ι : Type} [Fintype ι] (c : ι → ℂ) (β : ι → GL (Fin 2) ℚ)
    (F : UpperHalfPlane → ℂ)
    (hF : F = ∑ i, c i • ((⇑g) ∣[(2 : ℤ)] (β i).map (Rat.castHom ℝ)))
    (hinv : ∀ γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N),
      F ∣[(2 : ℤ)] γ = F) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma0 N) 2, ⇑h = F :=
  ⟨{ toFun := F
     slash_action_eq' := hinv
     holo' := by
       subst hF
       exact mdifferentiable_sum _ _ _ fun i _ => (CuspFormClass.holo g).slash _ _
     zero_at_cusps' := fun hc => by
       subst hF
       exact isZeroAt_sum _ _ _ fun i _ => isZeroAt_slash_map g (β i) (isCusp_SL2Z_of_isCusp_map hc) },
   rfl⟩

end S_CuspForm_exists_eq_sum_smul_slash_of_forall_slash_eq
end P2MW
export P2MW.S_CuspForm_exists_eq_sum_smul_slash_of_forall_slash_eq (solution)
