-- Prove2me | solution 1 for AutomorphicForm.typeSubmodule_inf_typeSubmodule_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2fc755c7-6c32-50b0-9929-864fa95401a0

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_typeSubmodule_inf_typeSubmodule_eq_bot

set_option autoImplicit false

open AutomorphicForm

noncomputable section

section Generic

variable {H G : Type*} [Group H] [Group G]

private def rightTranslationRep (ι : H →* G) : Representation ℂ H (G → ℂ) where
  toFun k :=
    { toFun := fun f x => f (x * ι k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext f x
    simp
  map_mul' k₁ k₂ := by
    ext f x
    simp [mul_assoc]

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private def intertwiningOfEquivariant {ι : H →* G} {ρ : Representation ℂ H W} {T : W →ₗ[ℂ] (G → ℂ)}
    (hT : IsRightEquivariant ι ρ T) : ρ.IntertwiningMap (rightTranslationRep ι) where
  toLinearMap := T
  isIntertwining' k := by
    ext v x
    exact hT k v x

private theorem intertwiningOfEquivariant_apply {ι : H →* G} {ρ : Representation ℂ H W}
    {T : W →ₗ[ℂ] (G → ℂ)} (hT : IsRightEquivariant ι ρ T) (v : W) :
    intertwiningOfEquivariant hT v = T v := rfl

private abbrev asModuleMap (ι : H →* G) (ρ : Representation ℂ H W)
    (φ : ρ.IntertwiningMap (rightTranslationRep ι)) :
    ρ.asModule →ₗ[MonoidAlgebra ℂ H] (rightTranslationRep ι).asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := rightTranslationRep ι) φ

private def nonzeroRanges (ι : H →* G) (ρ : Representation ℂ H W) :
    Set (Submodule (MonoidAlgebra ℂ H) (rightTranslationRep ι).asModule) :=
  {m | ∃ φ : ρ.IntertwiningMap (rightTranslationRep ι), LinearMap.range (asModuleMap ι ρ φ) = m ∧ m ≠ ⊥}

set_option backward.isDefEq.respectTransparency false in

private theorem nonzeroRanges_equiv (ι : H →* G) (ρ : Representation ℂ H W) [ρ.IsIrreducible] :
    ∀ m ∈ nonzeroRanges ι ρ, Nonempty (m ≃ₗ[MonoidAlgebra ℂ H] ρ.asModule) := by
  rintro m ⟨φ, rfl, hm⟩
  rcases LinearMap.injective_or_eq_zero (asModuleMap ι ρ φ) with hinj | hzero
  · exact ⟨(LinearEquiv.ofInjective _ hinj).symm⟩
  · exact absurd (by rw [hzero, LinearMap.range_zero]) hm

private theorem mem_sSup_nonzeroRanges (ι : H →* G) (ρ : Representation ℂ H W) {f : G → ℂ}
    (hf : f ∈ typeSubmodule ι ρ) :
    (rightTranslationRep ι).asModuleEquiv.symm f ∈ sSup (nonzeroRanges ι ρ) := by
  refine Submodule.span_induction
    (p := fun f _ => (rightTranslationRep ι).asModuleEquiv.symm f ∈ sSup (nonzeroRanges ι ρ))
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    have hle : LinearMap.range (asModuleMap ι ρ (intertwiningOfEquivariant hT)) ≤ sSup (nonzeroRanges ι ρ) := by
      by_cases hbot : LinearMap.range (asModuleMap ι ρ (intertwiningOfEquivariant hT)) = ⊥
      · rw [hbot]
        exact bot_le
      · exact le_sSup ⟨intertwiningOfEquivariant hT, rfl, hbot⟩
    exact hle (LinearMap.mem_range_self (asModuleMap ι ρ (intertwiningOfEquivariant hT)) (ρ.asModuleEquiv.symm v))
  · simp
  · intro _ _ _ _ hu hw
    rw [map_add]
    exact (sSup (nonzeroRanges ι ρ)).add_mem hu hw
  · intro c _ _ hu
    rw [Representation.asModuleEquiv_symm_map_smul]
    exact (sSup (nonzeroRanges ι ρ)).smul_mem _ hu

end Generic

private theorem nonempty_linearEquiv_of_mem_sSup_of_mem_sSup
    {R M S S' : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup S] [Module R S] [IsSimpleModule R S] [AddCommGroup S'] [Module R S'] [IsSimpleModule R S']
    {s s' : Set (Submodule R M)} (hs : ∀ m ∈ s, Nonempty (m ≃ₗ[R] S)) (hs' : ∀ m ∈ s', Nonempty (m ≃ₗ[R] S'))
    {x : M} (hx : x ≠ 0) (h1 : x ∈ sSup s) (h2 : x ∈ sSup s') : Nonempty (S ≃ₗ[R] S') := by
  haveI simple_s : ∀ m : s, IsSimpleModule R m := fun m => IsSimpleModule.congr (hs m m.2).some
  haveI simple_s' : ∀ m : s', IsSimpleModule R m := fun m => IsSimpleModule.congr (hs' m m.2).some
  haveI hsemi : IsSemisimpleModule R ↥(sSup s) := by
    rw [sSup_eq_iSup]
    exact isSemisimpleModule_biSup_of_isSemisimpleModule_submodule (p := fun m : Submodule R M => m)
      (fun m hm => by
        haveI := simple_s ⟨m, hm⟩
        exact inferInstance)
  haveI hP : IsSemisimpleModule R ↥(sSup s ⊓ sSup s') :=
    IsSemisimpleModule.of_injective (Submodule.inclusion (inf_le_left : sSup s ⊓ sSup s' ≤ sSup s))
      (Submodule.inclusion_injective _)
  rcases IsSemisimpleModule.eq_bot_or_exists_simple_le (sSup s ⊓ sSup s') with hbot | ⟨N, hNle, hN⟩
  · have hmem : x ∈ sSup s ⊓ sSup s' := Submodule.mem_inf.2 ⟨h1, h2⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact (hx hmem).elim
  · haveI := hN
    obtain ⟨m, hm, ⟨e₁⟩⟩ := Submodule.linearEquiv_of_le_sSup N s (le_trans hNle inf_le_left)
    obtain ⟨m', hm', ⟨e₂⟩⟩ := Submodule.linearEquiv_of_le_sSup N s' (le_trans hNle inf_le_right)
    exact ⟨(((hs m hm).some.symm.trans e₁.symm).trans e₂).trans (hs' m' hm').some⟩

section EquivOfModules

variable {H : Type*} [Group H] {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private def equivOfAsModule {ρ : Representation ℂ H W} {ρ' : Representation ℂ H W'}
    (e : ρ.asModule ≃ₗ[MonoidAlgebra ℂ H] ρ'.asModule) : ρ.Equiv ρ' :=
  let φ : ρ.IntertwiningMap ρ' :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := ρ')).symm e.toLinearMap
  have hbij : Function.Bijective φ.toLinearMap := e.bijective
  Representation.Equiv.mk (LinearEquiv.ofBijective φ.toLinearMap hbij) fun g => by
    ext v
    exact LinearMap.congr_fun (φ.isIntertwining' g) v

end EquivOfModules

section MeetOfPieces

variable {H G : Type*} [Group H] [Group G] {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W']
  [Module ℂ W']

set_option backward.isDefEq.respectTransparency false in

private theorem nonempty_equiv_of_mem_inf (ι : H →* G) (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W')
    [ρ.IsIrreducible] [ρ'.IsIrreducible] {f : G → ℂ} (hf₁ : f ∈ typeSubmodule ι ρ)
    (hf₂ : f ∈ typeSubmodule ι ρ') (hf0 : f ≠ 0) : Nonempty (ρ.Equiv ρ') := by
  have hx : (rightTranslationRep ι).asModuleEquiv.symm f ≠ 0 := fun h =>
    hf0 ((LinearEquiv.map_eq_zero_iff _).1 h)
  obtain ⟨e⟩ := nonempty_linearEquiv_of_mem_sSup_of_mem_sSup (nonzeroRanges_equiv ι ρ)
    (nonzeroRanges_equiv ι ρ') hx (mem_sSup_nonzeroRanges ι ρ hf₁) (mem_sSup_nonzeroRanges ι ρ' hf₂)
  exact ⟨equivOfAsModule e⟩

end MeetOfPieces

theorem solution
    {H G : Type*} [Group H] [Group G]
    {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ι : H →* G) (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W')
    [ρ.IsIrreducible] [ρ'.IsIrreducible] (hne : IsEmpty (ρ.Equiv ρ')) :
    typeSubmodule ι ρ ⊓ typeSubmodule ι ρ' = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  by_contra hf0
  exact hne.elim (nonempty_equiv_of_mem_inf ι ρ ρ' (Submodule.mem_inf.1 hf).1 (Submodule.mem_inf.1 hf).2 hf0).some

end

#print axioms solution

end S_AutomorphicForm_typeSubmodule_inf_typeSubmodule_eq_bot
end P2MW
export P2MW.S_AutomorphicForm_typeSubmodule_inf_typeSubmodule_eq_bot (solution)
