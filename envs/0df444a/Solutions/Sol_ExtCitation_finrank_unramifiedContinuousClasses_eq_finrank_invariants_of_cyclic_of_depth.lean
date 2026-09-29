-- Prove2me | solution 1 for ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/bc393a3b-3ffe-5bf7-9504-4bdbe0eab767

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ExtCitation_LocalLevelSubgroupsPD
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Theorems.Thm_groupCohomology_cocycles1_forall_apply_mul_right_eq_iff_apply_eq_zero
import Theorems.Thm_groupCohomology_exists_cocycles1_unramified_iff_mem_inflationImage_sup
import Theorems.Thm_groupCohomology_inflationImage_antitone
import Theorems.Thm_groupCohomology_finiteDimensional_inflationImage
import Theorems.Thm_groupCohomology_finrank_inflationImage_le_finrank_invariants
import Theorems.Thm_groupCohomology_finrank_inflationImage_eq_finrank_invariants_of_norm_eq_zero
import Theorems.Thm_Submodule_exists_mem_forall_of_finset_of_directed
import Theorems.Thm_Representation_norm_eq_zero_of_dvd_card
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth

set_option autoImplicit false

open CategoryTheory Module groupCohomology ExtCitation

theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]

    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m)

    (φ : primeLocalGaloisGroup q)
    (hcyc : ∀ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F],
      ∀ x : primeLocalGaloisGroup q ⧸
          ((((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) ⊔
            ((F.fixingSubgroup).comap (primeLocalToGlobal q))),
        x ∈ Subgroup.zpowers (QuotientGroup.mk φ :  primeLocalGaloisGroup q ⧸
          ((((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) ⊔
            ((F.fixingSubgroup).comap (primeLocalToGlobal q)))))

    (hdepth : ∀ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ → ∀ n : ℕ, 0 < n →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ Normal ℚ F ∧ F₀ ≤ F ∧
        ∀ j : ℕ, φ ^ j ∈ ((((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) ⊔
            ((F.fixingSubgroup).comap (primeLocalToGlobal q))) → n ∣ j)

    (adm_ur : Submodule (ZMod p) (H1 M)) [FiniteDimensional (ZMod p) adm_ur]
    (hadm_ur : ∀ x, x ∈ adm_ur ↔ ∃ c : cocycles₁ M,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : primeLocalGaloisGroup q),
          primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
      ∧ (∃ m : M, ∀ g : primeLocalGaloisGroup q,
          primeLocalToGlobal q g ∈ (primeLocalPlace q).inertiaSubgroupIn ℚ → c.val g = M.ρ g m - m)
      ∧ (H1π M).hom c = x) :
    finrank (ZMod p) adm_ur = finrank (ZMod p) M.ρ.invariants := by
  classical

  set r := primeLocalToGlobal q with hr
  set I : Subgroup (primeLocalGaloisGroup q) := ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap r with hI
  let U : IntermediateField ℚ (AlgebraicClosure ℚ) → Subgroup (primeLocalGaloisGroup q) :=
    fun F => (F.fixingSubgroup).comap r
  haveI hIn : I.Normal := ExtCitation.inertiaPullback_normal q
  haveI : Normal ℚ (AlgebraicClosure ℚ) := by
    convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) inferInstance
    rfl

  haveI : Finite M := Module.finite_of_finite (ZMod p)
  choose Fm hFm using hsm
  let F₀ : IntermediateField ℚ (AlgebraicClosure ℚ) := ⨆ m : M, Fm m
  haveI : ∀ m : M, FiniteDimensional ℚ (Fm m) := fun m => (hFm m).1
  haveI hF₀fin : FiniteDimensional ℚ F₀ := IntermediateField.finiteDimensional_iSup_of_finite
  have hU₀ : ∀ g ∈ U F₀, M.ρ g = 1 := by
    intro g hg
    refine LinearMap.ext fun m => ?_
    exact (hFm m).2 g (IntermediateField.fixingSubgroup_antitone (le_iSup Fm m) hg)

  let ι := {F : IntermediateField ℚ (AlgebraicClosure ℚ) // FiniteDimensional ℚ F ∧ Normal ℚ F ∧ F₀ ≤ F}
  haveI hUn : ∀ F : ι, (U F.1).Normal := fun F => by
    haveI := F.2.2.1; exact ExtCitation.levelSubgroup_normal q F.1
  haveI hUf : ∀ F : ι, (U F.1).FiniteIndex := fun F => by
    haveI := F.2.1; haveI := F.2.2.1; exact ExtCitation.levelSubgroup_finiteIndex q F.1
  let N : ι → Subgroup (primeLocalGaloisGroup q) := fun F => I ⊔ U F.1
  haveI hNn : ∀ F : ι, (N F).Normal := fun F => Subgroup.sup_normal I (U F.1)
  haveI hNf : ∀ F : ι, (N F).FiniteIndex := fun F => Subgroup.finiteIndex_of_le (le_sup_right : U F.1 ≤ N F)
  have hUtriv : ∀ F : ι, ∀ u ∈ U F.1, M.ρ u = 1 := fun F u hu =>
    hU₀ u (Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone F.2.2.2) hu)

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
    obtain ⟨F', _⟩ := hclose F₀ hF₀fin le_rfl
    exact ⟨F'⟩
  let T : ι → Submodule (ZMod p) (H1 M) := fun F => inflationImage M (N F)

  have hcov : ∀ x ∈ adm_ur, ∃ F : ι, x ∈ T F := by
    intro x hx
    obtain ⟨c, ⟨F, hF, hinv⟩, ⟨m, hI'⟩, rfl⟩ := (hadm_ur x).mp hx
    haveI := hF
    obtain ⟨F', hFF'⟩ := hclose (F ⊔ F₀) inferInstance le_sup_right
    refine ⟨F', (groupCohomology.exists_cocycles1_unramified_iff_mem_inflationImage_sup M I (U F'.1)
      (hUtriv F') ((H1π M).hom c)).1 ⟨c, rfl, fun s hs => ?_, m, fun g hg => hI' g (Subgroup.mem_comap.1 hg)⟩⟩
    have hs' : r s ∈ F.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hFF') (Subgroup.mem_comap.1 hs)
    exact (groupCohomology.cocycles1_forall_apply_mul_right_eq_iff_apply_eq_zero c s).1 (fun g => hinv g s hs')
  have hle : ∀ F : ι, T F ≤ adm_ur := by
    intro F x hx
    obtain ⟨c, hcx, hcU, m, hcI⟩ :=
      (groupCohomology.exists_cocycles1_unramified_iff_mem_inflationImage_sup M I (U F.1) (hUtriv F) x).2 hx
    refine (hadm_ur x).2 ⟨c, ⟨F.1, F.2.1, fun g s hs => ?_⟩, ⟨m, fun g hg => hcI g (Subgroup.mem_comap.2 hg)⟩, hcx⟩
    exact (groupCohomology.cocycles1_forall_apply_mul_right_eq_iff_apply_eq_zero c s).2 (hcU s (Subgroup.mem_comap.2 hs)) g

  have hdir : Directed (· ≤ ·) T := by
    intro F F'
    haveI := F.2.1; haveI := F'.2.1
    obtain ⟨F'', hF''⟩ := hclose (F.1 ⊔ F'.1) inferInstance (F.2.2.2.trans le_sup_left)
    refine ⟨F'', ?_, ?_⟩
    · exact groupCohomology.inflationImage_antitone M (sup_le_sup_left
        (Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hF''))) I)
    · exact groupCohomology.inflationImage_antitone M (sup_le_sup_left
        (Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone (le_sup_right.trans hF''))) I)
  have hTb : ∀ F : ι, FiniteDimensional (ZMod p) (T F) ∧
      Module.finrank (ZMod p) (T F) ≤ Module.finrank (ZMod p) M.ρ.invariants := fun F =>
    ⟨groupCohomology.finiteDimensional_inflationImage M (N F),
      by haveI := F.2.1; haveI := F.2.2.1
         exact groupCohomology.finrank_inflationImage_le_finrank_invariants M (N F) (hcyc F.1)⟩

  have hfin : Module.Finite (ZMod p) adm_ur ∧
      Module.finrank (ZMod p) adm_ur ≤ Module.finrank (ZMod p) M.ρ.invariants := by
    set b := Module.finrank (ZMod p) M.ρ.invariants
    have key : ∀ s : Finset adm_ur, LinearIndependent (ZMod p) (fun x : s => (x : adm_ur)) → s.card ≤ b := by
      intro s hs
      obtain ⟨j, hj⟩ := Submodule.exists_mem_forall_of_finset_of_directed T hdir
        (s.image (fun x : adm_ur => (x : H1 M)))
        (fun x hx => by obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx; exact hcov y y.2)
      haveI := (hTb j).1
      have hs' : LinearIndependent (ZMod p)
          (fun x : s => (⟨((x : adm_ur) : H1 M), hj _ (Finset.mem_image_of_mem _ x.2)⟩ : T j)) := by
        apply LinearIndependent.of_comp (T j).subtype
        have : (T j).subtype ∘ (fun x : s => (⟨((x : adm_ur) : H1 M), hj _ (Finset.mem_image_of_mem _ x.2)⟩ : T j))
            = adm_ur.subtype ∘ (fun x : s => (x : adm_ur)) := rfl
        rw [this]; exact hs.map' adm_ur.subtype (Submodule.ker_subtype adm_ur)
      have := hs'.fintype_card_le_finrank
      simp only [Fintype.card_coe] at this
      exact this.trans (hTb j).2
    have hrank : Module.rank (ZMod p) adm_ur ≤ b := _root_.rank_le key
    haveI : Module.Finite (ZMod p) adm_ur :=
      Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0 (n := b)))
    exact ⟨inferInstance, Module.finrank_le_of_rank_le hrank⟩
  haveI := hfin.1
  refine le_antisymm hfin.2 ?_

  haveI : Finite (M →ₗ[ZMod p] M) := Finite.of_injective _ DFunLike.coe_injective
  set d : ℕ := Nat.card (M →ₗ[ZMod p] M)ˣ with hd
  have hdpos : 0 < d := Nat.card_pos
  have hρd : (M.ρ φ) ^ d = 1 := by
    have h1 : (M.ρ.asGroupHom φ) ^ d = 1 := pow_card_eq_one'
    have h2 := congrArg Units.val h1
    rwa [Units.val_pow_eq_pow_val, Units.val_one, Representation.asGroupHom_apply] at h2
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨F, hFfin, hFnorm, hF₀F, hdiv⟩ := hdepth F₀ hF₀fin (p * d) (Nat.mul_pos hp hdpos)
  let Fι : ι := ⟨F, hFfin, hFnorm, hF₀F⟩
  haveI : Fintype (primeLocalGaloisGroup q ⧸ N Fι) := Subgroup.fintypeQuotientOfFiniteIndex
  have hgen : ∀ x : primeLocalGaloisGroup q ⧸ N Fι, x ∈ Subgroup.zpowers (QuotientGroup.mk φ : _ ⧸ N Fι) := by
    haveI := hFfin; haveI := hFnorm; exact hcyc F

  have hρQd : (M.quotientToInvariants (N Fι)).ρ (QuotientGroup.mk φ) ^ d = 1 := by
    have hk : ∀ (k : ℕ) (z : M.quotientToInvariants (N Fι)),
        (((M.quotientToInvariants (N Fι)).ρ (QuotientGroup.mk φ) ^ k) z).1 = ((M.ρ φ) ^ k) z.1 := by
      intro k
      induction k with
      | zero => intro z; rfl
      | succ k ih =>
        intro z
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
        rfl
    refine LinearMap.ext fun y => Subtype.ext ?_
    rw [hk, hρd]; rfl

  have hcard : p * d ∣ Fintype.card (primeLocalGaloisGroup q ⧸ N Fι) := by
    rw [← Nat.card_eq_fintype_card, ← orderOf_eq_card_of_forall_mem_zpowers hgen]
    refine hdiv _ ?_
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_orderOf_eq_one _
  have hN0 : (M.quotientToInvariants (N Fι)).ρ.norm = 0 :=
    Representation.norm_eq_zero_of_dvd_card _ p hgen hρQd hcard
  have heq := groupCohomology.finrank_inflationImage_eq_finrank_invariants_of_norm_eq_zero M (N Fι) hgen hN0
  rw [← heq]
  exact Submodule.finrank_mono (hle Fι)

end S_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth
end P2MW
export P2MW.S_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth (solution)
