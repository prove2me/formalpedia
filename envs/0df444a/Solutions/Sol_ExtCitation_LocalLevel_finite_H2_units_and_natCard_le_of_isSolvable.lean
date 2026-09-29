-- Prove2me | solution 1 for ExtCitation.LocalLevel.finite_H2_units_and_natCard_le_of_isSolvable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/93da84f8-5678-58a6-bacf-0275b75e9289

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_ExtCitation_LocalLevel_exists_fixedLevel_quotientToInvariants_iso
import Theorems.Thm_ExtCitation_LocalLevel_natCard_H2_units_eq_natCard_of_isCyclic
import Theorems.Thm_groupCohomology_finite_H2_and_natCard_H2_le_of_isSolvable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_finite_H2_units_and_natCard_le_of_isSolvable
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_finite_H2_units_and_natCard_le_of_isSolvable.ExtCitation.LocalLevel IsLocalRing groupCohomology"

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.exists_fixedLevel_quotientToInvariants_iso LocalLevel.natCard_H2_units_eq_natCard_of_isCyclic"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "exists_fixedLevel_quotientToInvariants_iso natCard_H2_units_eq_natCard_of_isCyclic"
namespace Br8b
p2m_open "ExtCitation.LocalLevel ExtCitation"

private theorem isMulCoboundary₁_of_faithful {L : Type} [Field L] (H : Type) [Group H] [Finite H]
    [MulSemiringAction H L] [FaithfulSMul H L] [MulDistribMulAction H Lˣ]
    (hcompatH : ∀ (h : H) (u : Lˣ), ((h • u : Lˣ) : L) = h • (u : L))
    (f : H → Lˣ) (hf : IsMulCocycle₁ f) : IsMulCoboundary₁ f := by
  let e := FixedPoints.toAlgAutMulEquiv H L
  have he : ∀ (g : H) (x : L), e g x = g • x := fun _ _ => rfl
  have hsmul : ∀ (τ : L ≃ₐ[FixedPoints.subfield H L] L) (u : Lˣ), τ • u = e.symm τ • u :=
    fun τ u => Units.ext (by rw [hcompatH, ← he, MulEquiv.apply_symm_apply]; rfl)
  have hf' : IsMulCocycle₁ (f ∘ e.symm) := fun τ₁ τ₂ => by
    simp only [Function.comp_apply, map_mul, hsmul]
    exact hf _ _
  obtain ⟨x, hx⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units (f ∘ e.symm) hf'
  refine ⟨x, fun g => ?_⟩
  have := hx (e g)
  rwa [hsmul, Function.comp_apply, MulEquiv.symm_apply_apply] at this

private theorem subsingleton_H1_res {L : Type} [Field L] {G : Type} [Group G] [Finite G]
    [MulSemiringAction G L] [FaithfulSMul G L] [MulDistribMulAction G Lˣ]
    (hcompat : ∀ (g : G) (u : Lˣ), ((g • u : Lˣ) : L) = g • (u : L))
    (H : Type) [Group H] [Finite H] (φ : H →* G) (hφ : Function.Injective φ) :
    Subsingleton (H1 (Rep.res φ (Rep.ofMulDistribMulAction G Lˣ))) := by
  letI iA : MulSemiringAction H L := MulSemiringAction.compHom L φ
  letI iU : MulDistribMulAction H Lˣ := MulDistribMulAction.compHom _ φ
  haveI iF : FaithfulSMul H L := ⟨fun {h₁ h₂} hh =>
    hφ (FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := L) fun x => hh x)⟩
  have hcompatH : ∀ (h : H) (u : Lˣ), ((h • u : Lˣ) : L) = h • (u : L) := fun h u => hcompat (φ h) u
  refine ⟨fun a b => ?_⟩
  suffices hz : ∀ x : H1 (Rep.res φ (Rep.ofMulDistribMulAction G Lˣ)), x = 0 by rw [hz a, hz b]
  intro x
  induction x using H1_induction_on with | h c =>
  rw [H1π_eq_zero_iff]
  let f : H → Lˣ := fun h => Additive.toMul (show Additive Lˣ from c h)
  have hf : IsMulCocycle₁ f := fun h₁ h₂ =>
    congrArg Additive.toMul ((mem_cocycles₁_iff (⇑c)).1 c.2 h₁ h₂)
  obtain ⟨y, hy⟩ := isMulCoboundary₁_of_faithful H hcompatH f hf
  refine ⟨(Additive.ofMul y : Additive Lˣ), funext fun h => ?_⟩
  rw [d₀₁_hom_apply]
  exact congrArg Additive.ofMul (hy h)

end ExtCitation.LocalLevel.Br8b

theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] (hsolv : Group.IsSolvable G) [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L)) :
    Finite (groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) ∧
      Nat.card (groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) ≤ Nat.card G := by
  classical
  haveI := hsolv
  refine groupCohomology.finite_H2_and_natCard_H2_le_of_isSolvable (Rep.ofMulDistribMulAction G (↥L)ˣ)
    (fun H _ _ φ hφ => ExtCitation.LocalLevel.Br8b.subsingleton_H1_res hcompat H φ hφ) ?_
  intro H _ _ φ hφ N _ hprime
  letI iA : MulSemiringAction H L := MulSemiringAction.compHom L φ
  letI iU : MulDistribMulAction H (↥L)ˣ := MulDistribMulAction.compHom _ φ
  haveI iF : FaithfulSMul H L := ⟨fun {h₁ h₂} hh =>
    hφ (FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := L) fun x => hh x)⟩
  have hGH : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x :=
    fun h x => hG (φ h) x
  have hcompatH : ∀ (h : H) (u : (↥L)ˣ), ((h • u : (↥L)ˣ) : L) = h • (u : L) :=
    fun h u => hcompat (φ h) u
  obtain ⟨L', iFD, iA', iF', iU', hG', hcompat', ⟨e⟩⟩ :=
    ExtCitation.LocalLevel.exists_fixedLevel_quotientToInvariants_iso q L H hGH hcompatH N
  haveI : Fact (Nat.card (H ⧸ N)).Prime := ⟨hprime⟩
  haveI : IsCyclic (H ⧸ N) := isCyclic_of_prime_card (p := Nat.card (H ⧸ N)) rfl
  have h6 := ExtCitation.LocalLevel.natCard_H2_units_eq_natCard_of_isCyclic q L' (H ⧸ N) hG' hcompat'
  have e2 := ((groupCohomology.functor ℤ (H ⧸ N) 2).mapIso e).toLinearEquiv.toEquiv
  have hcard : Nat.card (H2 ((Rep.res φ (Rep.ofMulDistribMulAction G (↥L)ˣ)).quotientToInvariants N))
      = Nat.card (H ⧸ N) := (Nat.card_congr e2).trans h6
  exact ⟨Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne'), hcard.le⟩

end S_ExtCitation_LocalLevel_finite_H2_units_and_natCard_le_of_isSolvable
end P2MW
export P2MW.S_ExtCitation_LocalLevel_finite_H2_units_and_natCard_le_of_isSolvable (solution)
