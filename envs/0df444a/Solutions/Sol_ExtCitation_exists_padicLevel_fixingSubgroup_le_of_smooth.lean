-- Prove2me | solution 1 for ExtCitation.exists_padicLevel_fixingSubgroup_le_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/97a8e010-6a51-542f-8395-b390f475c024

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_LevelSubgroup
import Theorems.Thm_Representation_exists_isGalois_level_forall_apply_eq_self
import Theorems.Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_exists_padicLevel_fixingSubgroup_le_of_smooth

set_option autoImplicit false
set_option maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation

namespace P2mS26HFIN2

open IntermediateField in

theorem exists_isGalois_ge (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] :
    ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F' ∧ IsGalois ℚ F' ∧ F ≤ F' := by
  haveI : Normal ℚ (AlgebraicClosure ℚ) := by
    convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) inferInstance
    rfl
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ L := normalClosure.is_finiteDimensional ℚ F (AlgebraicClosure ℚ)
  haveI : Normal ℚ L := normalClosure.normal ℚ F (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ L := ⟨⟩
  exact ⟨L, inferInstance, inferInstance, IntermediateField.le_normalClosure F⟩

end P2mS26HFIN2

open P2mS26HFIN2 in
theorem solution
    (p : ℕ) [Fact p.Prime] (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    {k : Type} [CommRing k] (N : Rep k S) [Module.Finite k N]
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) :
    ∃ K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)), FiniteDimensional ℚ_[(q : ℕ)] K ∧
      (∃ ζ : K, IsPrimitiveRoot ζ p) ∧
      (∃ F₁ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₁ ∧
        F₁.fixingSubgroup.comap (primeLocalToGlobal q) ≤ K.fixingSubgroup) ∧
      (K.fixingSubgroup : Subgroup (primeLocalGaloisGroup q)).FiniteIndex ∧
      (∀ s : primeLocalGaloisGroup q, s ∈ K.fixingSubgroup → s ∈ S) ∧
      (∀ s : S, (s : primeLocalGaloisGroup q) ∈ K.fixingSubgroup → ∀ n : N, N.ρ s n = n) := by
  classical
  obtain ⟨F₀, hF₀, hF₀S⟩ := hS
  obtain ⟨FN, hFN, -, hFNtriv⟩ := Representation.exists_isGalois_level_forall_apply_eq_self
      ((primeLocalToGlobal q).comp S.subtype) N.ρ hsm
  haveI := hF₀; haveI := hFN

  let P : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ)) → Prop := fun U =>
    ∀ g, g ∈ U → ∃ hg : g ∈ S, ∀ n : N, N.ρ ⟨g, hg⟩ n = n
  have hP : ∀ U V, V ≤ U → P U → P V := fun U V hVU hU g hg => hU g (hVU hg)
  have hP₂ : P ((F₀ ⊔ FN).fixingSubgroup.comap (localGaloisToGlobal (q : ℕ))) := by
    intro g hg
    rw [Subgroup.mem_comap] at hg
    have hg₀ : g ∈ S := hF₀S (by
      rw [Subgroup.mem_comap]
      exact IntermediateField.fixingSubgroup_antitone le_sup_left hg)
    exact ⟨hg₀, fun n => hFNtriv ⟨g, hg₀⟩ (IntermediateField.fixingSubgroup_antitone le_sup_right hg) n⟩

  obtain ⟨K₁, hK₁, hPK₁⟩ := (exists_finiteDimensional_comap_localGaloisToGlobal_iff (q : ℕ) P hP).1
    ⟨F₀ ⊔ FN, inferInstance, hP₂⟩
  haveI := hK₁

  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl (q : ℕ)) p
  let K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)) := K₁ ⊔ IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ}
  haveI : FiniteDimensional ℚ_[(q : ℕ)] (IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
  haveI : FiniteDimensional ℚ_[(q : ℕ)] K := IntermediateField.finiteDimensional_sup _ _
  have hζK : ζ ∈ K := (le_sup_right : _ ≤ K) (IntermediateField.mem_adjoin_simple_self _ ζ)
  have hPK : P K.fixingSubgroup :=
    hP _ _ (IntermediateField.fixingSubgroup_antitone (le_sup_left : K₁ ≤ K)) hPK₁

  obtain ⟨F₁, hF₁, hF₁K⟩ := (exists_finiteDimensional_comap_localGaloisToGlobal_iff (q : ℕ)
      (fun U => U ≤ K.fixingSubgroup) (fun U V hVU hU => hVU.trans hU)).2 ⟨K, inferInstance, le_rfl⟩
  haveI := hF₁

  obtain ⟨F₂, hF₂, hG₂, h₁₂⟩ := exists_isGalois_ge F₁
  haveI := hF₂; haveI := hG₂
  have hle₂ : F₂.fixingSubgroup.comap (localGaloisToGlobal (q : ℕ)) ≤ K.fixingSubgroup :=
    (Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone h₁₂)).trans hF₁K
  haveI : (F₂.fixingSubgroup.comap (localGaloisToGlobal (q : ℕ))).FiniteIndex :=
    groupCohomology.finiteIndex_comap_fixingSubgroup (localGaloisToGlobal (q : ℕ)) F₂
  have hfi : (K.fixingSubgroup).FiniteIndex := Subgroup.finiteIndex_of_le hle₂
  refine ⟨K, inferInstance, ⟨⟨ζ, hζK⟩, ?_⟩, ⟨F₁, hF₁, hF₁K⟩, hfi,
    fun g hg => (hPK g hg).elim fun hg' _ => hg', fun s hs n => ?_⟩
  · exact (IsPrimitiveRoot.coe_submonoidClass_iff (ζ := (⟨ζ, hζK⟩ : K))).1 hζ
  · exact (hPK (s : primeLocalGaloisGroup q) hs).elim fun _ h => h n

end S_ExtCitation_exists_padicLevel_fixingSubgroup_le_of_smooth
end P2MW
export P2MW.S_ExtCitation_exists_padicLevel_fixingSubgroup_le_of_smooth (solution)
