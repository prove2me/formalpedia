-- Prove2me | solution 1 for ExtCitation.LocalLevel.isZero_groupCohomology_one_res_units
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/43b3c355-8d18-5c97-90ef-3567c27c33c9

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_groupCohomology_subsingleton_H1_ofMulDistribMulAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_isZero_groupCohomology_one_res_units

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

namespace Ws25H90

theorem isMulCoboundary₁_of_faithful {Γ F : Type} [Group Γ] [Field F] [MulSemiringAction Γ F] [Finite Γ] [FaithfulSMul Γ F]
    [MulDistribMulAction Γ Fˣ] (hcompat : ∀ (γ : Γ) (u : Fˣ), ((γ • u : Fˣ) : F) = γ • (u : F))
    (c : Γ → Fˣ) (hc : IsMulCocycle₁ c) : IsMulCoboundary₁ c := by

  obtain ⟨e, he⟩ : ∃ e : Γ ≃* (F ≃ₐ[FixedPoints.subfield Γ F] F), ∀ (γ : Γ) (x : F), e γ x = γ • x := by
    refine ⟨FixedPoints.toAlgAutMulEquiv Γ F, fun γ x => ?_⟩
    simp only [FixedPoints.toAlgAutMulEquiv, MulEquiv.ofBijective_apply, MulSemiringAction.toAlgAut_apply,
      MulSemiringAction.toAlgEquiv_apply]

  have hact : ∀ (σ : F ≃ₐ[FixedPoints.subfield Γ F] F) (u : Fˣ), σ • u = (e.symm σ) • u := by
    intro σ u
    apply Units.ext
    simp only [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe]
    rw [hcompat, ← he, MulEquiv.apply_symm_apply]

  have hF : IsMulCocycle₁ (fun σ => c (e.symm σ)) := by
    intro σ τ
    show c (e.symm (σ * τ)) = σ • c (e.symm τ) * c (e.symm σ)
    rw [map_mul, hc, hact]
  obtain ⟨u, hu⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units _ hF
  refine ⟨u, fun γ => ?_⟩
  have := hu (e γ)
  rw [hact, MulEquiv.symm_apply_apply] at this
  rw [this]
  exact congrArg c (e.symm_apply_apply γ)

end Ws25H90

theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (Γ : Type) [Group Γ] (f : Γ →* G) (hf : Function.Injective f) :
    CategoryTheory.Limits.IsZero (groupCohomology (Rep.res f (Rep.ofMulDistribMulAction G (↥L)ˣ)) 1) := by
  letI : MulSemiringAction Γ L := MulSemiringAction.compHom L f
  letI : MulDistribMulAction Γ (↥L)ˣ := MulDistribMulAction.compHom (↥L)ˣ f
  haveI : Finite Γ := Finite.of_injective f hf
  haveI : FaithfulSMul Γ L :=
    ⟨fun {γ γ'} h => hf (FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := L) (fun x => h x))⟩

  have hres : Rep.res f (Rep.ofMulDistribMulAction G (↥L)ˣ) = Rep.ofMulDistribMulAction Γ (↥L)ˣ := rfl
  rw [hres]
  haveI : Subsingleton (H1 (Rep.ofMulDistribMulAction Γ (↥L)ˣ)) :=
    groupCohomology.subsingleton_H1_ofMulDistribMulAction
      (Ws25H90.isMulCoboundary₁_of_faithful (fun γ u => hcompat (f γ) u))
  exact ModuleCat.isZero_of_subsingleton _

end S_ExtCitation_LocalLevel_isZero_groupCohomology_one_res_units
end P2MW
export P2MW.S_ExtCitation_LocalLevel_isZero_groupCohomology_one_res_units (solution)
