-- Prove2me | solution 1 for ExtCitation.LocalLevel.exists_common_overlayer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/241d5043-a79f-5b02-8264-22d4bf0c3860

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_exists_common_overlayer

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

set_option maxHeartbeats 800000

namespace OVbProof

noncomputable section

open Polynomial

variable (q : ℕ) [Fact q.Prime]

section Layer

variable (K : IntermediateField ℚ_[q] (PadicAlgCl q))
  (L : IntermediateField ℚ_[q] (PadicAlgCl q))
  (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
  (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
  (hKL : K ≤ L) (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x)

omit [FaithfulSMul G L] in
include hK in

theorem stable (σ : GG q) (hσ : ∀ k ∈ K, σ k = k) (x : L) : σ (x : PadicAlgCl q) ∈ L := by
  classical
  letI := Fintype.ofFinite G
  let p : L[X] := prodXSubSMul G L x
  have hpcoeff : ∀ i, ((p.coeff i : L) : PadicAlgCl q) ∈ K := fun i =>
    (hK _).2 (fun g => prodXSubSMul.coeff G L x g i)
  let P : (PadicAlgCl q)[X] := p.map (algebraMap L (PadicAlgCl q))
  have hPσ : P.map (σ : PadicAlgCl q →+* PadicAlgCl q) = P := by
    ext i
    simp only [P, Polynomial.coeff_map]
    exact hσ _ (hpcoeff i)
  have hroot : P.eval (x : PadicAlgCl q) = 0 := by
    show (p.map (algebraMap L (PadicAlgCl q))).eval (algebraMap L (PadicAlgCl q) x) = 0
    rw [Polynomial.eval_map, Polynomial.eval₂_hom, prodXSubSMul.eval, map_zero]
  have hroot' : P.eval (σ (x : PadicAlgCl q)) = 0 := by
    rw [← hPσ, Polynomial.eval_map, show σ (x : PadicAlgCl q) = (σ : PadicAlgCl q →+* PadicAlgCl q) x from rfl,
      Polynomial.eval₂_hom, hroot, map_zero]
  simp only [P, p, prodXSubSMul, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Finset.prod_eq_zero_iff] at hroot'
  obtain ⟨g, -, hg⟩ := hroot'
  rw [sub_eq_zero] at hg
  rw [hg]
  exact Subtype.mem _

include hK in

theorem exists_restrict (σ : GG q) (hσ : ∀ k ∈ K, σ k = k) :
    ∃ g : G, ∀ x : L, ((g • x : L) : PadicAlgCl q) = σ (x : PadicAlgCl q) := by
  have hst := stable q K L G hK σ hσ
  let ψ₀ : L →+* L :=
    { toFun := fun x => ⟨σ (x : PadicAlgCl q), hst x⟩
      map_one' := Subtype.ext (map_one σ)
      map_mul' := fun x y => Subtype.ext (map_mul σ _ _)
      map_zero' := Subtype.ext (map_zero σ)
      map_add' := fun x y => Subtype.ext (map_add σ _ _) }
  let ψ : L →ₐ[FixedPoints.subfield G L] L :=
    { toRingHom := ψ₀
      commutes' := fun c => by
        apply Subtype.ext
        show σ ((c : L) : PadicAlgCl q) = ((c : L) : PadicAlgCl q)
        exact hσ _ ((hK (c : L)).2 (fun g => c.2 g)) }
  obtain ⟨g, hg⟩ := (FixedPoints.toAlgHom_bijective G L).2 ψ
  refine ⟨g, fun x => ?_⟩
  exact congrArg Subtype.val (show g • x = ψ x from congrArg (fun f : L →ₐ[FixedPoints.subfield G L] L => f x) hg)

omit [Finite G] [FaithfulSMul G L] in
include hG hKL hK in

theorem exists_extend (g : G) :
    ∃ σ : GG q, (∀ k ∈ K, σ k = k) ∧ ∀ x : L, σ (x : PadicAlgCl q) = ((g • x : L) : PadicAlgCl q) := by
  haveI : IsGalois ℚ_[q] (PadicAlgCl q) := IsAlgClosure.isGalois ℚ_[q] (PadicAlgCl q)
  let gA : L ≃ₐ[ℚ_[q]] L :=
    { MulSemiringAction.toRingEquiv G L g with commutes' := hG g }
  refine ⟨gA.liftNormal (PadicAlgCl q), fun k hk => ?_, fun x => ?_⟩
  · have h := AlgEquiv.liftNormal_commutes gA (PadicAlgCl q) ⟨k, hKL hk⟩
    have hfix : g • (⟨k, hKL hk⟩ : L) = ⟨k, hKL hk⟩ := (hK ⟨k, hKL hk⟩).1 hk g
    have h' : (gA ⟨k, hKL hk⟩ : L) = ⟨k, hKL hk⟩ := hfix
    rw [h'] at h
    exact h
  · exact AlgEquiv.liftNormal_commutes gA (PadicAlgCl q) x

theorem normal_of_stable (hst : ∀ σ : GG q, (∀ k ∈ K, σ k = k) → ∀ y ∈ L, σ y ∈ L) :
    ((Gw q L).subgroupOf (Gw q K)).Normal := by
  refine ⟨fun a ha σ => ?_⟩
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  rw [IntermediateField.mem_fixingSubgroup_iff] at ha ⊢
  intro y hy
  have hσ' : ∀ k ∈ K, ((σ⁻¹ : Gw q K) : GG q) k = k := (IntermediateField.mem_fixingSubgroup_iff K _).1 (σ⁻¹).2
  have hy' : ((σ⁻¹ : Gw q K) : GG q) y ∈ L := hst _ hσ' y hy
  show (σ : GG q) ((a : GG q) (((σ⁻¹ : Gw q K) : GG q) y)) = y
  rw [ha _ hy']
  show ((σ * σ⁻¹ : Gw q K) : GG q) y = y
  rw [mul_inv_cancel]
  rfl

omit [FaithfulSMul G L] in
include hK in
theorem normal_subgroupOf :
    ((Gw q L).subgroupOf (Gw q K)).Normal :=
  normal_of_stable q K L (fun σ hσ y hy => stable q K L G hK σ hσ ⟨y, hy⟩)

noncomputable def rHom : Gw q K →* G where
  toFun σ := Classical.choose (exists_restrict q K L G hK σ ((IntermediateField.mem_fixingSubgroup_iff K _).1 σ.2))
  map_one' := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro x
    apply Subtype.ext
    rw [Classical.choose_spec (exists_restrict q K L G hK (1 : Gw q K) ((IntermediateField.mem_fixingSubgroup_iff K _).1 (1 : Gw q K).2)) x, one_smul]
    rfl
  map_mul' σ τ := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro x
    apply Subtype.ext
    rw [Classical.choose_spec (exists_restrict q K L G hK (σ * τ) ((IntermediateField.mem_fixingSubgroup_iff K _).1 (σ * τ).2)) x, mul_smul,
      Classical.choose_spec (exists_restrict q K L G hK σ ((IntermediateField.mem_fixingSubgroup_iff K _).1 σ.2)),
      Classical.choose_spec (exists_restrict q K L G hK τ ((IntermediateField.mem_fixingSubgroup_iff K _).1 τ.2))]
    rfl

theorem rHom_spec (σ : Gw q K) (x : L) :
    ((rHom q K L G hK σ • x : L) : PadicAlgCl q) = (σ : GG q) (x : PadicAlgCl q) :=
  Classical.choose_spec (exists_restrict q K L G hK σ ((IntermediateField.mem_fixingSubgroup_iff K _).1 σ.2)) x

theorem rHom_eq_one_iff (σ : Gw q K) : rHom q K L G hK σ = 1 ↔ (σ : GG q) ∈ Gw q L := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h y hy
    have := rHom_spec q K L G hK σ ⟨y, hy⟩
    rw [h, one_smul] at this
    exact this.symm
  · intro h
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro x
    apply Subtype.ext
    rw [rHom_spec, one_smul]
    exact h _ x.2

include hG hKL in
theorem rHom_surjective : Function.Surjective (rHom q K L G hK) := by
  intro g
  obtain ⟨σ, hσK, hσ⟩ := exists_extend q K L G hG hKL hK g
  refine ⟨⟨σ, (IntermediateField.mem_fixingSubgroup_iff K σ).2 hσK⟩, ?_⟩
  apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
  intro x
  apply Subtype.ext
  rw [rHom_spec]
  exact hσ x

variable (D : Subgroup (Gw q K)) [D.Normal] (hD : D ≤ (Gw q L).subgroupOf (Gw q K))

def NSub : Subgroup (Gw q K ⧸ D) := ((Gw q L).subgroupOf (Gw q K)).map (QuotientGroup.mk' D)

omit [FaithfulSMul G L] in
include hK in
theorem NSub_normal : (NSub q K L D).Normal :=
  Subgroup.Normal.map (normal_subgroupOf q K L G hK) _ (QuotientGroup.mk'_surjective D)

include hD in
theorem mem_NSub_iff (σ : Gw q K) : (QuotientGroup.mk σ : Gw q K ⧸ D) ∈ NSub q K L D ↔ (σ : GG q) ∈ Gw q L := by
  constructor
  · intro h
    obtain ⟨τ, hτ, hτσ⟩ := Subgroup.mem_map.1 h
    rw [Subgroup.mem_subgroupOf] at hτ
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hτσ
    have hmem : τ⁻¹ * σ ∈ (Gw q L).subgroupOf (Gw q K) := hD hτσ
    rw [Subgroup.mem_subgroupOf] at hmem
    have := (Gw q L).mul_mem hτ hmem
    simpa using this
  · intro h
    exact ⟨σ, Subgroup.mem_subgroupOf.2 h, rfl⟩

omit [D.Normal] in
include hD in
theorem le_ker : D ≤ (rHom q K L G hK).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker, rHom_eq_one_iff]
  exact Subgroup.mem_subgroupOf.1 (hD hσ)

noncomputable def Φ : Gw q K ⧸ D →* G := QuotientGroup.lift D (rHom q K L G hK) (le_ker q K L G hK D hD)

theorem Φ_mk (σ : Gw q K) : Φ q K L G hK D hD (QuotientGroup.mk σ) = rHom q K L G hK σ :=
  QuotientGroup.lift_mk _ (le_ker q K L G hK D hD) σ

include hG hKL in
theorem Φ_surjective : Function.Surjective (Φ q K L G hK D hD) := by
  intro g
  obtain ⟨σ, rfl⟩ := rHom_surjective q K L G hG hKL hK g
  exact ⟨QuotientGroup.mk σ, Φ_mk q K L G hK D hD σ⟩

theorem ker_Φ : (Φ q K L G hK D hD).ker = NSub q K L D := by
  ext h
  induction h using QuotientGroup.induction_on with | H σ =>
  rw [MonoidHom.mem_ker, Φ_mk, rHom_eq_one_iff, mem_NSub_iff q K L D hD]

noncomputable def eIso [(NSub q K L D).Normal] : G ≃* (Gw q K ⧸ D) ⧸ NSub q K L D :=
  (QuotientGroup.quotientKerEquivOfSurjective (Φ q K L G hK D hD)
      (Φ_surjective q K L G hG hKL hK D hD)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (ker_Φ q K L G hK D hD))

theorem eIso_spec [(NSub q K L D).Normal] (g : G) (σ : Gw q K)
    (h : (QuotientGroup.mk (QuotientGroup.mk σ : Gw q K ⧸ D) : (Gw q K ⧸ D) ⧸ NSub q K L D) =
        eIso q K L G hG hKL hK D hD g)
    (x : L) : ((g • x : L) : PadicAlgCl q) = (σ : GG q) (x : PadicAlgCl q) := by
  have h1 : (eIso q K L G hG hKL hK D hD).symm
      (QuotientGroup.mk (QuotientGroup.mk σ : Gw q K ⧸ D)) = g := by
    rw [h, MulEquiv.symm_apply_apply]
  have h2 : (eIso q K L G hG hKL hK D hD).symm
      (QuotientGroup.mk (QuotientGroup.mk σ : Gw q K ⧸ D)) = rHom q K L G hK σ := by
    simp only [eIso, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
    rw [show (QuotientGroup.quotientMulEquivOfEq (ker_Φ q K L G hK D hD)).symm
        (QuotientGroup.mk (QuotientGroup.mk σ : Gw q K ⧸ D)) =
        (QuotientGroup.mk (QuotientGroup.mk σ : Gw q K ⧸ D)) from rfl]
    show QuotientGroup.kerLift (Φ q K L G hK D hD) (QuotientGroup.mk (QuotientGroup.mk σ : Gw q K ⧸ D)) = _
    rw [QuotientGroup.kerLift_mk, Φ_mk]
  rw [← h1, h2, rHom_spec]

include hKL hD in

theorem mem_L_iff (y : PadicAlgCl q) :
    y ∈ L ↔ ∀ σ : Gw q K, (QuotientGroup.mk σ : Gw q K ⧸ D) ∈ NSub q K L D → (σ : GG q) y = y := by
  haveI : IsGalois ℚ_[q] (PadicAlgCl q) := IsAlgClosure.isGalois ℚ_[q] (PadicAlgCl q)
  constructor
  · intro hy σ hσ
    rw [mem_NSub_iff q K L D hD] at hσ
    exact (IntermediateField.mem_fixingSubgroup_iff L _).1 hσ y hy
  · intro h
    rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
    intro τ hτ
    have hτK : τ ∈ Gw q K := by
      rw [IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
      exact fun k hk => hτ k (hKL hk)
    exact h ⟨τ, hτK⟩ ((mem_NSub_iff q K L D hD ⟨τ, hτK⟩).2 hτ)

end Layer

section Ambient

variable (K : IntermediateField ℚ_[q] (PadicAlgCl q))
  (M : IntermediateField ℚ_[q] (PadicAlgCl q))
  (hst : ∀ σ : GG q, (∀ k ∈ K, σ k = k) → ∀ y ∈ M, σ y ∈ M)

@[reducible] noncomputable def actM : MulSemiringAction (Gw q K) M where
  smul σ m := ⟨(σ : GG q) (m : PadicAlgCl q), hst σ ((IntermediateField.mem_fixingSubgroup_iff K _).1 σ.2) m m.2⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl
  smul_zero σ := Subtype.ext (map_zero (σ : GG q))
  smul_add σ _ _ := Subtype.ext (map_add (σ : GG q) _ _)
  smul_one σ := Subtype.ext (map_one (σ : GG q))
  smul_mul σ _ _ := Subtype.ext (map_mul (σ : GG q) _ _)

abbrev DM : Subgroup (Gw q K) := (Gw q M).subgroupOf (Gw q K)

theorem DM_le_ker :
    DM q K M ≤ (@MulSemiringAction.toRingAut (Gw q K) M _ _ (actM q K M hst)).ker := by
  intro σ hσ
  rw [Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff] at hσ
  rw [MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro m
  apply Subtype.ext
  exact hσ _ m.2

@[reducible] noncomputable def actH [(DM q K M).Normal] : MulSemiringAction (Gw q K ⧸ DM q K M) M :=
  MulSemiringAction.compHom M
    (QuotientGroup.lift (DM q K M) (@MulSemiringAction.toRingAut (Gw q K) M _ _ (actM q K M hst)) (DM_le_ker q K M hst))

theorem actH_mk [(DM q K M).Normal] (σ : Gw q K) (m : M) :
    ((@HSMul.hSMul _ _ _ (@instHSMul _ _ (actH q K M hst).toSMul) (QuotientGroup.mk σ : Gw q K ⧸ DM q K M) m : M) : PadicAlgCl q) =
      (σ : GG q) (m : PadicAlgCl q) := by
  rfl

end Ambient

end

end OVbProof

open OVbProof in
theorem solution (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q))
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (hKL : K ≤ L) (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x)
    (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    (G' : Type) [Group G'] [Finite G'] [MulSemiringAction G' L'] [FaithfulSMul G' L']
    (hG' : ∀ (g : G') (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
    [MulDistribMulAction G' (↥L')ˣ]
    (hcompat' : ∀ (g : G') (u : (↥L')ˣ), ((g • u : (↥L')ˣ) : L') = g • (u : L'))
    (hKL' : K ≤ L') (hK' : ∀ x : L', (x : PadicAlgCl q) ∈ K ↔ ∀ g : G', g • x = x) :
    ∃ (M : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] M) (hLM : L ≤ M) (hL'M : L' ≤ M)
      (H : Type) (_ : Group H) (_ : Finite H) (_ : MulSemiringAction H M) (_ : FaithfulSMul H M)
      (_ : MulDistribMulAction H (↥M)ˣ) (N N' : Subgroup H) (_ : N.Normal) (_ : N'.Normal)
      (e : G ≃* H ⧸ N) (e' : G' ≃* H ⧸ N'),
      (∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x) ∧
      (∀ (h : H) (u : (↥M)ˣ), ((h • u : (↥M)ˣ) : M) = h • (u : M)) ∧
      (∀ x : M, (x : PadicAlgCl q) ∈ K ↔ ∀ h : H, h • x = x) ∧
      (∀ x : M, (x : PadicAlgCl q) ∈ L ↔ ∀ h ∈ N, h • x = x) ∧
      (∀ x : M, (x : PadicAlgCl q) ∈ L' ↔ ∀ h ∈ N', h • x = x) ∧
      (∀ (g : G) (h : H), (QuotientGroup.mk h : H ⧸ N) = e g →
        ∀ x : L, ((g • x : L) : PadicAlgCl q) = ((h • (⟨(x : PadicAlgCl q), hLM x.2⟩ : M) : M) : PadicAlgCl q)) ∧
      (∀ (g : G') (h : H), (QuotientGroup.mk h : H ⧸ N') = e' g →
        ∀ x : L', ((g • x : L') : PadicAlgCl q) = ((h • (⟨(x : PadicAlgCl q), hL'M x.2⟩ : M) : M) : PadicAlgCl q)) := by
  classical
  haveI : IsGalois ℚ_[q] (PadicAlgCl q) := IsAlgClosure.isGalois ℚ_[q] (PadicAlgCl q)

  let M : IntermediateField ℚ_[q] (PadicAlgCl q) := L ⊔ L'
  haveI : FiniteDimensional ℚ_[q] M := IntermediateField.finiteDimensional_sup L L'
  have hLM : L ≤ M := le_sup_left
  have hL'M : L' ≤ M := le_sup_right

  have hstL := stable q K L G hK
  have hstL' := stable q K L' G' hK'
  have hstM : ∀ σ : GG q, (∀ k ∈ K, σ k = k) → ∀ y ∈ M, σ y ∈ M := by
    intro σ hσ y hy
    have h1 : (L ⊔ L').map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q) ≤ L ⊔ L' := by
      rw [IntermediateField.map_sup]
      apply sup_le_sup
      · rintro _ ⟨z, hz, rfl⟩; exact hstL σ hσ ⟨z, hz⟩
      · rintro _ ⟨z, hz, rfl⟩; exact hstL' σ hσ ⟨z, hz⟩
    exact h1 ⟨y, hy, rfl⟩

  haveI hDn : (DM q K M).Normal := normal_of_stable q K M hstM
  have hDL : DM q K M ≤ (Gw q L).subgroupOf (Gw q K) := by
    intro σ hσ
    rw [Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    exact fun y hy => hσ y (hLM hy)
  have hDL' : DM q K M ≤ (Gw q L').subgroupOf (Gw q K) := by
    intro σ hσ
    rw [Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    exact fun y hy => hσ y (hL'M hy)
  haveI hN : (NSub q K L (DM q K M)).Normal := NSub_normal q K L G hK _
  haveI hN' : (NSub q K L' (DM q K M)).Normal := NSub_normal q K L' G' hK' _
  letI act : MulSemiringAction (Gw q K ⧸ DM q K M) M := actH q K M hstM
  letI actU : MulDistribMulAction (Gw q K ⧸ DM q K M) (↥M)ˣ := Units.mulDistribMulActionRight
  have hfaith : FaithfulSMul (Gw q K ⧸ DM q K M) M := by
    refine ⟨fun {h₁ h₂} hh => ?_⟩
    induction h₁ using QuotientGroup.induction_on with | H σ =>
    induction h₂ using QuotientGroup.induction_on with | H τ =>
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hy' : (σ : GG q) y = (τ : GG q) y := congrArg Subtype.val (hh ⟨y, hy⟩)
    show (σ : GG q)⁻¹ ((τ : GG q) y) = y
    rw [← hy', AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  refine ⟨M, inferInstance, hLM, hL'M, Gw q K ⧸ DM q K M, inferInstance, inferInstance, act, hfaith, actU,
    NSub q K L (DM q K M), NSub q K L' (DM q K M), hN, hN',
    eIso q K L G hG hKL hK (DM q K M) hDL, eIso q K L' G' hG' hKL' hK' (DM q K M) hDL',
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro h x
    induction h using QuotientGroup.induction_on with | H σ =>
    apply Subtype.ext
    exact (σ : GG q).commutes x
  ·
    intro h u
    rfl
  ·
    intro x
    constructor
    · intro hx h
      induction h using QuotientGroup.induction_on with | H σ =>
      apply Subtype.ext
      exact (IntermediateField.mem_fixingSubgroup_iff K _).1 σ.2 _ hx
    · intro h
      rw [← InfiniteGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      exact congrArg Subtype.val (h (QuotientGroup.mk ⟨τ, hτ⟩))
  ·
    intro x
    rw [mem_L_iff q K L hKL (DM q K M) hDL (x : PadicAlgCl q)]
    constructor
    · intro h hh hmem
      induction hh using QuotientGroup.induction_on with | H σ =>
      exact Subtype.ext (h σ hmem)
    · intro h σ hσ
      exact congrArg Subtype.val (h _ hσ)
  ·
    intro x
    rw [mem_L_iff q K L' hKL' (DM q K M) hDL' (x : PadicAlgCl q)]
    constructor
    · intro h hh hmem
      induction hh using QuotientGroup.induction_on with | H σ =>
      exact Subtype.ext (h σ hmem)
    · intro h σ hσ
      exact congrArg Subtype.val (h _ hσ)
  ·
    intro g h hgh x
    induction h using QuotientGroup.induction_on with | H σ =>
    exact eIso_spec q K L G hG hKL hK (DM q K M) hDL g σ hgh x
  ·
    intro g h hgh x
    induction h using QuotientGroup.induction_on with | H σ =>
    exact eIso_spec q K L' G' hG' hKL' hK' (DM q K M) hDL' g σ hgh x

end S_ExtCitation_LocalLevel_exists_common_overlayer
end P2MW
export P2MW.S_ExtCitation_LocalLevel_exists_common_overlayer (solution)
