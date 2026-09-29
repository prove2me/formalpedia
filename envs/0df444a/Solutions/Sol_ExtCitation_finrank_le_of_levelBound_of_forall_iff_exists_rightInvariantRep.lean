-- Prove2me | solution 1 for ExtCitation.finrank_le_of_levelBound_of_forall_iff_exists_rightInvariantRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f6320be0-7cde-51c9-8068-9acde444bac2

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Theorems.Thm_groupCohomology_inflationImage_antitone
import Theorems.Thm_groupCohomology_finiteDimensional_inflationImage
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_finrank_le_of_levelBound_of_forall_iff_exists_rightInvariantRep

set_option autoImplicit false

universe u

p2m_open "CategoryTheory groupCohomology ExtCitation P2MW.S_ExtCitation_finrank_le_of_levelBound_of_forall_iff_exists_rightInvariantRep.ExtCitation"

namespace P2mS17A9

section GC
variable {k G : Type u} [CommRing k] [Group G]

theorem cocycles₁_apply_mul_right_eq_iff_apply_eq_zero {M : Rep k G} (c : cocycles₁ M) (u : G) :
    (∀ g : G, c (g * u) = c g) ↔ c u = 0 := by
  constructor
  · intro h; have := h 1; rwa [one_mul, cocycles₁_map_one] at this
  · intro h g; rw [(mem_cocycles₁_iff (⇑c)).1 c.2 g u, h, map_zero, zero_add]

theorem H1π_mem_inflationImage_of_forall_apply_eq_zero (M : Rep k G) (N : Subgroup G) [N.Normal]
    (c : cocycles₁ M) (h : ∀ n ∈ N, c n = 0) : H1π M c ∈ inflationImage M N := by
  have hex := H1InfRes_exact M N
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range] at hex
  change H1π M c ∈ LinearMap.range ((H1InfRes M N).f).hom
  apply hex
  rw [LinearMap.mem_ker]
  show (H1π M ≫ (H1InfRes M N).g) c = 0
  have e : H1π M ≫ (H1InfRes M N).g = mapCocycles₁ N.subtype (𝟙 (Rep.res N.subtype M)) ≫ H1π (Rep.res N.subtype M) := by
    rw [H1InfRes_g]; exact H1π_comp_map _ _
  rw [e]
  show H1π (Rep.res N.subtype M) (mapCocycles₁ N.subtype (𝟙 _) c) = 0
  rw [H1π_eq_zero_iff]
  exact ⟨0, by funext s; simp [coe_mapCocycles₁ (N.subtype), h s.1 s.2]⟩
end GC

section LA
variable {k : Type*} [Field k]

theorem exists_mem_forall_of_finset_of_directed {V : Type*} [AddCommGroup V] [Module k V]
    {ι : Type*} [Nonempty ι] (T : ι → Submodule k V) (hdir : Directed (· ≤ ·) T)
    (s : Finset V) (hs : ∀ x ∈ s, ∃ i, x ∈ T i) : ∃ j, ∀ x ∈ s, x ∈ T j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | insert a s ha ih =>
    obtain ⟨j, hj⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
    obtain ⟨i, hi⟩ := hs a (Finset.mem_insert_self a s)
    obtain ⟨l, hil, hjl⟩ := hdir i j
    exact ⟨l, fun x hx => by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hil hi
      · exact hjl (hj x hx)⟩

theorem finrank_le_of_directed_cover {V : Type*} [AddCommGroup V] [Module k V]
    {ι : Type*} [Nonempty ι] (S : Submodule k V) (T : ι → Submodule k V)
    (hdir : Directed (· ≤ ·) T) (hcov : ∀ x ∈ S, ∃ i, x ∈ T i) (b : ℕ)
    (hT : ∀ i, FiniteDimensional k (T i) ∧ Module.finrank k (T i) ≤ b) :
    Module.finrank k S ≤ b := by
  classical
  have key : ∀ s : Finset S, LinearIndependent k (fun x : s => (x : S)) → s.card ≤ b := by
    intro s hs
    obtain ⟨j, hj⟩ := exists_mem_forall_of_finset_of_directed T hdir (s.image (fun x : S => (x : V)))
      (fun x hx => by obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx; exact hcov y y.2)
    haveI := (hT j).1
    have hs' : LinearIndependent k (fun x : s => (⟨((x : S) : V), hj _ (Finset.mem_image_of_mem _ x.2)⟩ : T j)) := by
      apply LinearIndependent.of_comp (T j).subtype
      have : (T j).subtype ∘ (fun x : s => (⟨((x : S) : V), hj _ (Finset.mem_image_of_mem _ x.2)⟩ : T j))
          = S.subtype ∘ (fun x : s => (x : S)) := rfl
      rw [this]; exact hs.map' S.subtype (Submodule.ker_subtype S)
    have := hs'.fintype_card_le_finrank
    simp only [Fintype.card_coe] at this
    exact this.trans (hT j).2
  have hrank : Module.rank k S ≤ b := _root_.rank_le key
  haveI : Module.Finite k S := Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0 (n := b)))
  exact Module.finrank_le_of_rank_le hrank
end LA

section Plumbing

theorem levelSubgroup_eq_ker (q : Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    (F.fixingSubgroup).comap (primeLocalToGlobal q)
      = ((AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).comp (primeLocalToGlobal q)).ker := by
  rw [← @IntermediateField.restrictNormalHom_ker ℚ (AlgebraicClosure ℚ) _ _ _ F ‹Normal ℚ F›, MonoidHom.comap_ker]
  rfl

scoped instance levelSubgroup_normal (q : Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    ((F.fixingSubgroup).comap (primeLocalToGlobal q)).Normal := by
  rw [levelSubgroup_eq_ker]; exact MonoidHom.normal_ker _

scoped instance levelSubgroup_finiteIndex (q : Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F] :
    ((F.fixingSubgroup).comap (primeLocalToGlobal q)).FiniteIndex := by
  rw [levelSubgroup_eq_ker]; exact Subgroup.finiteIndex_ker _

end Plumbing

end P2mS17A9
p2m_reactivate "P2MW.S_ExtCitation_finrank_le_of_levelBound_of_forall_iff_exists_rightInvariantRep.P2mS17A9"

namespace ExtCitation p2m_export "ExtCitation" "primeLocalGaloisGroup primeLocalToGlobal levelSubgroup_eq_ker levelSubgroup_normal levelSubgroup_finiteIndex" end ExtCitation
p2m_open_scoped "ExtCitation" in
open P2mS17A9 in

theorem ExtCitation.finrank_le_of_forall_iff_exists_rightInvariantRep
    (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₀]
    (b : ℕ)
    (hlevel : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F → ∀ _ : Normal ℚ F, F₀ ≤ F →
      Module.finrank (ZMod p) (inflationImage M ((F.fixingSubgroup).comap (primeLocalToGlobal q))) ≤ b)
    (adm₁ : Submodule (ZMod p) (H1 M))
    (hadm₁ : ∀ x, x ∈ adm₁ ↔ ∃ c : cocycles₁ M, H1π M c = x ∧
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ g s : primeLocalGaloisGroup q, primeLocalToGlobal q s ∈ F.fixingSubgroup → c (g * s) = c g) :
    Module.finrank (ZMod p) adm₁ ≤ b := by
  classical
  haveI : Normal ℚ (AlgebraicClosure ℚ) := by
    convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) inferInstance
    rfl

  let ι := {F : IntermediateField ℚ (AlgebraicClosure ℚ) // FiniteDimensional ℚ F ∧ Normal ℚ F ∧ F₀ ≤ F}
  let U : ι → Subgroup (primeLocalGaloisGroup q) := fun F => (F.1.fixingSubgroup).comap (primeLocalToGlobal q)
  haveI hUn : ∀ F : ι, (U F).Normal := fun F => by haveI := F.2.2.1; exact P2mS17A9.levelSubgroup_normal q F.1
  haveI hUf : ∀ F : ι, (U F).FiniteIndex := fun F => by haveI := F.2.1; haveI := F.2.2.1; exact P2mS17A9.levelSubgroup_finiteIndex q F.1
  let T : ι → Submodule (ZMod p) (H1 M) := fun F => inflationImage M (U F)

  have hclose : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F → F₀ ≤ F →
      ∃ F' : ι, F ≤ F'.1 := by
    intro F hF hF₀
    haveI := hF
    refine ⟨⟨IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ), ?_, ?_, ?_⟩, ?_⟩
    · exact normalClosure.is_finiteDimensional ℚ F (AlgebraicClosure ℚ)
    · exact normalClosure.normal ℚ F (AlgebraicClosure ℚ)
    · exact hF₀.trans (IntermediateField.le_normalClosure F)
    · exact IntermediateField.le_normalClosure F
  haveI : Nonempty ι := by
    obtain ⟨F', _⟩ := hclose F₀ inferInstance le_rfl
    exact ⟨F'⟩
  have hdir : Directed (· ≤ ·) T := by
    intro F F'
    haveI := F.2.1; haveI := F'.2.1
    obtain ⟨F'', hF''⟩ := hclose (F.1 ⊔ F'.1) inferInstance (F.2.2.2.trans le_sup_left)
    refine ⟨F'', ?_, ?_⟩
    · exact inflationImage_antitone M (Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hF'')))
    · exact inflationImage_antitone M (Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone (le_sup_right.trans hF'')))
  have hcov : ∀ x ∈ adm₁, ∃ F : ι, x ∈ T F := by
    intro x hx
    obtain ⟨c, rfl, F, hF, hinv⟩ := (hadm₁ x).mp hx
    haveI := hF
    obtain ⟨F', hFF'⟩ := hclose (F ⊔ F₀) inferInstance le_sup_right
    refine ⟨F', H1π_mem_inflationImage_of_forall_apply_eq_zero M (U F') c fun s hs => ?_⟩
    have hs' : primeLocalToGlobal q s ∈ F.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hFF') hs
    exact (cocycles₁_apply_mul_right_eq_iff_apply_eq_zero c s).mp (fun g => hinv g s hs')
  refine finrank_le_of_directed_cover adm₁ T hdir hcov b fun F => ⟨?_, ?_⟩
  · exact finiteDimensional_inflationImage M (U F)
  · exact hlevel F.1 F.2.1 F.2.2.1 F.2.2.2

theorem solution (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₀]
    (b : ℕ)
    (hlevel : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F → ∀ _ : Normal ℚ F, F₀ ≤ F →
      Module.finrank (ZMod p) (inflationImage M ((F.fixingSubgroup).comap (primeLocalToGlobal q))) ≤ b)
    (adm₁ : Submodule (ZMod p) (H1 M))
    (hadm₁ : ∀ x, x ∈ adm₁ ↔ ∃ c : cocycles₁ M, H1π M c = x ∧
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ g s : primeLocalGaloisGroup q, primeLocalToGlobal q s ∈ F.fixingSubgroup → c (g * s) = c g) :
    Module.finrank (ZMod p) adm₁ ≤ b :=
  ExtCitation.finrank_le_of_forall_iff_exists_rightInvariantRep p q M F₀ b hlevel adm₁ hadm₁

end S_ExtCitation_finrank_le_of_levelBound_of_forall_iff_exists_rightInvariantRep
end P2MW
export P2MW.S_ExtCitation_finrank_le_of_levelBound_of_forall_iff_exists_rightInvariantRep (solution)
