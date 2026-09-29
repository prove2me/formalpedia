-- Prove2me | solution 1 for ExtCitation.tame_or_descent_of_isSimple
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/718ed93d-01d8-5ca9-b795-e8521660ace8

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Theorems.Thm_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image
import Theorems.Thm_localGaloisToGlobal_mem_fixingSubgroup_iff
import Theorems.Thm_Subgroup_exists_wild_tame_unramified_chain_of_le
import Theorems.Thm_Representation_forall_apply_eq_one_of_normal_isPGroup_of_isSimple
import Theorems.Thm_groupCohomology_exists_level_ofChar_cycloChar_comp
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ExtCitation_exists_tame_generator_at_level
import Theorems.Thm_ExtCitation_exists_frobenius_pow_inv_mul_mem_inertia_sup_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_tame_or_descent_of_isSimple
p2m_attr_erase "instance" "instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"

set_option autoImplicit false
open ExtCitation
open scoped IntermediateField Pointwise

open groupCohomology in

set_option maxHeartbeats 2400000 in
theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (hq : (q : ℕ) = p) {k : Type} [Field k] [Finite k] [CharP k p]
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (N : Rep k S)
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n)
    [FiniteDimensional k N] (hN : Module.finrank k N ≠ 0)
    (hsimple : ∀ W : Submodule k N, (∀ (s : S) (v : N), v ∈ W → N.ρ s v ∈ W) → W = ⊥ ∨ W = ⊤) :
    (∃ S₀ : Subgroup (primeLocalGaloisGroup q), S₀ ≤ S ∧
        (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
          F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S₀) ∧
        (S₀.subgroupOf S).Normal ∧
        (∀ s : S, (s : primeLocalGaloisGroup q) ∈ S₀ → N.ρ s = 1 ∧ cycloChar p (primeLocalToGlobal q s) = 1) ∧
        ¬ p ∣ (S₀.subgroupOf S).index) ∨
    (∃ (S' : Subgroup (primeLocalGaloisGroup q)) (hle : S' ≤ S),
        (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
          F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S') ∧
        (S'.subgroupOf S).Normal ∧ (S'.subgroupOf S).index = p ∧
        Nat.card (MonoidHom.mrange (N.ρ.comp (Subgroup.inclusion hle)))
          < Nat.card (MonoidHom.mrange N.ρ)) := by
  classical
  subst hq
  haveI hqF : Fact (q : ℕ).Prime := ⟨q.2⟩
  have hq2 : 2 ≤ (q : ℕ) := q.2.two_le

  obtain ⟨φ, hφ⟩ := exists_isFrobeniusAt_apply_primeLocalToGlobal q
  obtain ⟨F₀, hF₀fd, hF₀S⟩ := hS
  haveI := hF₀fd
  have hlevel : ∃ F₁ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₁ ∧
      ∀ s : S, primeLocalToGlobal q s ∈ F₁.fixingSubgroup → N.ρ s = 1 := by
    let b := Module.Basis.ofVectorSpace k N
    haveI : Finite (Module.Basis.ofVectorSpaceIndex k N) := Module.Finite.finite_basis b
    choose Fv hFv hFv' using hsm
    haveI : ∀ i, FiniteDimensional ℚ (Fv (b i)) := fun i => hFv _
    refine ⟨⨆ i, Fv (b i), IntermediateField.finiteDimensional_iSup_of_finite, fun s hs => ?_⟩
    apply b.ext
    intro i
    rw [Module.End.one_apply]
    exact hFv' (b i) s (IntermediateField.fixingSubgroup_antitone (le_iSup (fun i => Fv (b i)) i) hs)
  obtain ⟨F₁, hF₁fd, hF₁⟩ := hlevel
  haveI := hF₁fd
  obtain ⟨F₂, hF₂fd, hF₂⟩ := groupCohomology.exists_level_ofChar_cycloChar_comp (p := (q : ℕ))
    (primeLocalToGlobal q) (1 : ZMod q)
  haveI := hF₂fd
  have hF₂' : ∀ s : primeLocalGaloisGroup q, primeLocalToGlobal q s ∈ F₂.fixingSubgroup →
      cycloChar (q : ℕ) (primeLocalToGlobal q s) = 1 := by
    intro s hs
    have h := hF₂ s hs
    have h' : (ofChar (k := ZMod q) ((cycloChar (q : ℕ)).comp (primeLocalToGlobal q))).ρ s (1 : ZMod q)
        = (((cycloChar (q : ℕ)).comp (primeLocalToGlobal q) s : (ZMod q)ˣ) : ZMod q) • (1 : ZMod q) := by
      show (((Representation.trivial (ZMod q) _ (ZMod q)).twist _) s) 1 = _
      rw [Representation.twist_apply_apply]; rfl
    rw [h', smul_eq_mul, mul_one] at h
    exact Units.ext h

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) := F₀ ⊔ F₁ ⊔ F₂
  haveI : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_sup _ _
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)
  haveI hFfd : FiniteDimensional ℚ F := normalClosure.is_finiteDimensional ℚ E _
  haveI hFgal : IsGalois ℚ F := by
    haveI : Normal ℚ F := normalClosure.normal ℚ E _
    exact ⟨⟩
  have hEF : E ≤ F := IntermediateField.le_normalClosure E
  have hF₀F : F₀ ≤ F := le_trans (le_trans le_sup_left le_sup_left) hEF
  have hF₁F : F₁ ≤ F := le_trans (le_trans le_sup_right le_sup_left) hEF
  have hF₂F : F₂ ≤ F := le_trans le_sup_right hEF

  let U : Subgroup (primeLocalGaloisGroup q) := (F.fixingSubgroup).comap (primeLocalToGlobal q)
  have hUmem : ∀ g, g ∈ U ↔ primeLocalToGlobal q g ∈ F.fixingSubgroup := fun _ => Iff.rfl
  have hUS : U ≤ S := fun g hg => hF₀S (IntermediateField.fixingSubgroup_antitone hF₀F hg)
  have hUN : ∀ s : S, (s : primeLocalGaloisGroup q) ∈ U → N.ρ s = 1 :=
    fun s hs => hF₁ s (IntermediateField.fixingSubgroup_antitone hF₁F hs)
  have hUχ : ∀ g ∈ U, cycloChar (q : ℕ) (primeLocalToGlobal q g) = 1 :=
    fun g hg => hF₂' g (IntermediateField.fixingSubgroup_antitone hF₂F hg)

  haveI hUn : U.Normal := by
    haveI : F.fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois F).mpr hFgal
    exact Subgroup.Normal.comap inferInstance _
  haveI : IsGalois ℚ_[q] (PadicAlgCl q) := IsAlgClosure.isGalois ℚ_[q] (PadicAlgCl q)
  haveI hUfi : U.FiniteIndex := by
    let Kw : IntermediateField ℚ_[q] (PadicAlgCl q) :=
      IntermediateField.adjoin ℚ_[q] (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ)))
    haveI : FiniteDimensional ℚ_[q] Kw := IntermediateField.finiteDimensional_adjoin_padicEmbedding_image q F
    have hUK : U = (Kw.fixingSubgroup : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) := by
      ext s; exact localGaloisToGlobal_mem_fixingSubgroup_iff q F s
    refine ⟨?_⟩
    rw [hUK]
    show (Kw.fixingSubgroup : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)).index ≠ 0
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'

  obtain ⟨t, W, htI, hUW, -, hWn, hWq, hIt, hφt⟩ := exists_tame_generator_at_level q φ hφ F
  haveI := hWn
  have hgen : ∀ g : primeLocalGaloisGroup q, ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ Subgroup.closure {t} ⊔ W := by
    intro g
    obtain ⟨n, hn⟩ := exists_frobenius_pow_inv_mul_mem_inertia_sup_level q φ hφ F g
    refine ⟨n, ?_⟩
    refine (sup_le (fun i hi => ?_) (hUW.trans le_sup_right)) hn
    obtain ⟨a, ha⟩ := hIt i hi
    have hmem : t ^ a * ((t ^ a)⁻¹ * i) ∈ Subgroup.closure {t} ⊔ W :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_singleton t)) a))
        (Subgroup.mem_sup_right ha)
    rwa [mul_inv_cancel_left] at hmem
  let H : Subgroup (primeLocalGaloisGroup q) := (N.ρ.ker).map S.subtype
  have hHmem : ∀ s : S, (s : primeLocalGaloisGroup q) ∈ H ↔ N.ρ s = 1 := by
    intro s
    constructor
    · rintro ⟨y, hy, hys⟩
      have : y = s := Subtype.ext hys
      rw [this] at hy
      exact hy
    · intro h; exact ⟨s, h, rfl⟩
  have hHS : H ≤ S := Subgroup.map_subtype_le _
  have hUH : U ≤ H := fun g hg => (hHmem ⟨g, hUS hg⟩).mpr (hUN ⟨g, hUS hg⟩ hg)
  have hHsub : H.subgroupOf S = N.ρ.ker := by
    ext s; rw [Subgroup.mem_subgroupOf, hHmem]; rfl
  have hHn : (H.subgroupOf S).Normal := by rw [hHsub]; infer_instance
  obtain ⟨P, I, hHP, hPI, hIS, hPn, hIn, ⟨n, hPH⟩, hIP, ⟨g₀, hg₀S, hcyc⟩⟩ :=
    Subgroup.exists_wild_tame_unramified_chain_of_le U W hUW hWq t φ hφt hgen S H hUH hHS hHn

  have hPH' : P ≤ H := by

    haveI : (N.ρ.ker).FiniteIndex := by
      rw [← hHsub]
      haveI : (U.subgroupOf S).FiniteIndex := inferInstance
      have hle : U.subgroupOf S ≤ H.subgroupOf S := fun s hs => hUH hs
      exact Subgroup.finiteIndex_of_le hle
    haveI : Finite (S ⧸ N.ρ.ker) := Subgroup.finite_quotient_of_finiteIndex
    let ρb : Representation k (S ⧸ N.ρ.ker) N := QuotientGroup.lift (N.ρ.ker) N.ρ (fun x hx => hx)
    have hρb : ∀ s : S, ρb (QuotientGroup.mk s) = N.ρ s := fun _ => rfl
    have hsimple' : ∀ W' : Submodule k N, (∀ (d : S ⧸ N.ρ.ker) (v : N), v ∈ W' → ρb d v ∈ W') → W' = ⊥ ∨ W' = ⊤ :=
      fun W' hW' => hsimple W' (fun s v hv => by rw [← hρb]; exact hW' _ v hv)

    haveI := hPn
    let Pb : Subgroup (S ⧸ N.ρ.ker) := (P.subgroupOf S).map (QuotientGroup.mk' (N.ρ.ker))
    haveI : Pb.Normal := Subgroup.Normal.map hPn _ (QuotientGroup.mk'_surjective _)
    have hPb : IsPGroup (q : ℕ) Pb := by
      rintro ⟨x, hx⟩
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx

      haveI : (H.subgroupOf P).Normal := by
        have : (H.subgroupOf P) = ((H.subgroupOf S).comap (Subgroup.inclusion (hPI.trans hIS))) := by
          ext y; simp [Subgroup.mem_subgroupOf]
        rw [this]; exact Subgroup.Normal.comap hHn _
      have hpow : (⟨(s : primeLocalGaloisGroup q), hs⟩ : P) ^ ((q : ℕ) ^ n) ∈ H.subgroupOf P := by
        rw [← hPH]; exact Subgroup.pow_index_mem _ _
      rw [Subgroup.mem_subgroupOf] at hpow
      change ((s : primeLocalGaloisGroup q)) ^ ((q : ℕ) ^ n) ∈ H at hpow
      have hpow' : N.ρ (s ^ ((q : ℕ) ^ n)) = 1 := (hHmem (s ^ ((q : ℕ) ^ n))).mp hpow
      refine ⟨n, Subtype.ext ?_⟩
      show (QuotientGroup.mk' (N.ρ.ker) s) ^ ((q : ℕ) ^ n) = 1
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hpow'
    have htrivP := Representation.forall_apply_eq_one_of_normal_isPGroup_of_isSimple ρb hN hsimple' Pb hPb
    intro g hg
    have hgS : g ∈ S := hIS (hPI hg)
    rw [show g = ((⟨g, hgS⟩ : S) : primeLocalGaloisGroup q) from rfl, hHmem, ← hρb]
    exact htrivP _ (Subgroup.mem_map.mpr ⟨⟨g, hgS⟩, hg, rfl⟩)
  have hPeq : P = H := le_antisymm hPH' hHP

  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_le hUH
  have hIH : ¬ (q : ℕ) ∣ H.relIndex I := by rw [← hPeq]; exact hIP
  have hSH : H.relIndex S = H.relIndex I * I.relIndex S := (Subgroup.relIndex_mul_relIndex H I S (hHP.trans hPI) hIS).symm
  by_cases hdiv : (q : ℕ) ∣ I.relIndex S
  ·

    right
    haveI := hIn
    haveI : (I.subgroupOf S).FiniteIndex := by
      haveI : I.FiniteIndex := Subgroup.finiteIndex_of_le (hUH.trans (hHP.trans hPI))
      infer_instance
    haveI : Finite (S ⧸ I.subgroupOf S) := Subgroup.finite_quotient_of_finiteIndex
    let mk : S →* S ⧸ I.subgroupOf S := QuotientGroup.mk' _
    have hmk : ∀ s : S, mk s = 1 ↔ (s : primeLocalGaloisGroup q) ∈ I := fun s => QuotientGroup.eq_one_iff s
    let gb : S ⧸ I.subgroupOf S := mk ⟨g₀, hg₀S⟩
    have hgenQ : ∀ x : S ⧸ I.subgroupOf S, x ∈ Subgroup.zpowers gb := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H s =>
        obtain ⟨n, hn⟩ := hcyc s s.2
        refine ⟨n, ?_⟩
        show gb ^ (n : ℤ) = mk s
        rw [zpow_natCast, ← map_pow]
        have : mk ((⟨g₀, hg₀S⟩ ^ n)⁻¹ * s) = 1 := (hmk _).mpr (by simpa using hn)
        rw [map_mul, map_inv, inv_mul_eq_one] at this
        exact this
    have hordg : orderOf gb = Nat.card (S ⧸ I.subgroupOf S) := orderOf_eq_card_of_forall_mem_zpowers hgenQ
    have hcardQ : Nat.card (S ⧸ I.subgroupOf S) = I.relIndex S := rfl
    have ha0 : I.relIndex S ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    let S'' : Subgroup S := (Subgroup.zpowers (gb ^ (q : ℕ))).comap mk
    let S' : Subgroup (primeLocalGaloisGroup q) := S''.map S.subtype
    have hS'S : S' ≤ S := Subgroup.map_subtype_le _
    have hS'sub : S'.subgroupOf S = S'' := Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective S) S''
    have hS'mem : ∀ s : S, (s : primeLocalGaloisGroup q) ∈ S' ↔ mk s ∈ Subgroup.zpowers (gb ^ (q : ℕ)) := by
      intro s
      rw [← Subgroup.mem_subgroupOf, hS'sub]
      rfl
    have hIS' : I ≤ S' := by
      intro g hg
      rw [show g = ((⟨g, hIS hg⟩ : S) : primeLocalGaloisGroup q) from rfl, hS'mem, (hmk _).mpr hg]
      exact one_mem _
    refine ⟨S', hS'S, ⟨F, hFfd, (hUH.trans (hHP.trans hPI)).trans hIS'⟩, ?_, ?_, ?_⟩
    ·
      rw [hS'sub]
      haveI : (Subgroup.zpowers (gb ^ (q : ℕ))).Normal := by
        refine ⟨fun a ha b => ?_⟩
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgenQ b)
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        have : gb ^ i * (gb ^ (q : ℕ)) ^ j * (gb ^ i)⁻¹ = (gb ^ (q : ℕ)) ^ j := by group
        rw [this]; exact ha
      exact Subgroup.Normal.comap inferInstance _
    ·
      rw [hS'sub, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
      have hc : Nat.card (Subgroup.zpowers (gb ^ (q : ℕ))) = I.relIndex S / q := by
        rw [Nat.card_zpowers, orderOf_pow' _ hqF.out.ne_zero, hordg, hcardQ, Nat.gcd_eq_right hdiv]
      have hm := Subgroup.card_mul_index (Subgroup.zpowers (gb ^ (q : ℕ)))
      rw [hc, hcardQ] at hm
      have hne : I.relIndex S / q ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hdiv) hqF.out.pos).ne'
      apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
      rw [hm, Nat.div_mul_cancel hdiv]
    ·
      have cardRange : ∀ {Γ : Type} [Group Γ] (f : Γ →* (N →ₗ[k] N)),
          Nat.card (MonoidHom.mrange f) = f.ker.index := by
        intro Γ _ f
        rw [Subgroup.index]
        refine (Nat.card_congr (Equiv.ofBijective
          (fun x : Γ ⧸ f.ker => Quotient.liftOn' x (fun g => (⟨f g, ⟨g, rfl⟩⟩ : MonoidHom.mrange f))
            (fun a b hab => ?_)) ⟨?_, ?_⟩)).symm
        · apply Subtype.ext
          rw [QuotientGroup.leftRel_apply, MonoidHom.mem_ker, map_mul] at hab
          show f a = f b
          calc f a = f a * (f a⁻¹ * f b) := by rw [hab, mul_one]
            _ = f b := by rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
        · intro x y hxy
          induction x using QuotientGroup.induction_on with
          | H a =>
            induction y using QuotientGroup.induction_on with
            | H b =>
              have h : f a = f b := congrArg Subtype.val hxy
              apply QuotientGroup.eq.mpr
              rw [MonoidHom.mem_ker, map_mul, ← h, ← map_mul, inv_mul_cancel, map_one]
        · rintro ⟨_, g, rfl⟩
          exact ⟨QuotientGroup.mk g, rfl⟩
      rw [cardRange, cardRange, ← MonoidHom.comap_ker]
      have hk1 : (N.ρ.ker).index = H.relIndex S := by rw [← hHsub]; rfl
      have hk2 : ((N.ρ.ker).comap (Subgroup.inclusion hS'S)).index = H.relIndex S' := by
        have : (N.ρ.ker).comap (Subgroup.inclusion hS'S) = H.subgroupOf S' := by
          ext x
          rw [Subgroup.mem_comap, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hHmem]
          rfl
        rw [this]; rfl
      rw [hk1, hk2]
      have hHS' : H ≤ S' := (hHP.trans hPI).trans hIS'
      have hmul : H.relIndex S' * S'.relIndex S = H.relIndex S := Subgroup.relIndex_mul_relIndex H S' S hHS' hS'S
      have hq' : S'.relIndex S = q := by
        show (S'.subgroupOf S).index = q
        rw [hS'sub, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
        have hc : Nat.card (Subgroup.zpowers (gb ^ (q : ℕ))) = I.relIndex S / q := by
          rw [Nat.card_zpowers, orderOf_pow' _ hqF.out.ne_zero, hordg, hcardQ, Nat.gcd_eq_right hdiv]
        have hm := Subgroup.card_mul_index (Subgroup.zpowers (gb ^ (q : ℕ)))
        rw [hc, hcardQ] at hm
        have hne : I.relIndex S / q ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hdiv) hqF.out.pos).ne'
        apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
        rw [hm, Nat.div_mul_cancel hdiv]
      haveI : (H.subgroupOf S').FiniteIndex := inferInstance
      have hpos : 0 < H.relIndex S' := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
      rw [← hmul, hq']
      nlinarith
  ·

    left
    let Kχ : Subgroup (primeLocalGaloisGroup q) := ((cycloChar (q : ℕ)).comp (primeLocalToGlobal q)).ker
    have hKχ : ∀ g, g ∈ Kχ ↔ cycloChar (q : ℕ) (primeLocalToGlobal q g) = 1 := fun g => MonoidHom.mem_ker
    refine ⟨H ⊓ Kχ, inf_le_left.trans hHS, ⟨F, hFfd, fun g hg => ⟨hUH hg, (hKχ g).mpr (hUχ g hg)⟩⟩, ?_, ?_, ?_⟩
    ·
      have : (H ⊓ Kχ).subgroupOf S = H.subgroupOf S ⊓ Kχ.subgroupOf S := by
        ext x; simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      rw [this]
      haveI := hHn
      haveI : (Kχ.subgroupOf S).Normal := inferInstance
      infer_instance
    · intro s hs
      exact ⟨(hHmem s).mp hs.1, (hKχ _).mp hs.2⟩
    ·
      have h1 : (H ⊓ Kχ).relIndex S = (H ⊓ Kχ).relIndex H * H.relIndex S :=
        (Subgroup.relIndex_mul_relIndex (H ⊓ Kχ) H S inf_le_left hHS).symm
      have h2 : (H ⊓ Kχ).relIndex H = Kχ.relIndex H := Subgroup.inf_relIndex_left _ _

      have h3 : ¬ (q : ℕ) ∣ Kχ.relIndex H := by
        let χH : H →* (ZMod q)ˣ := ((cycloChar (q : ℕ)).comp (primeLocalToGlobal q)).comp H.subtype
        have hker : Kχ.subgroupOf H = χH.ker := by
          ext x; rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]; rfl
        have hcard : Kχ.relIndex H = Nat.card χH.range := by
          rw [Subgroup.relIndex, hker]
          exact Nat.card_congr (QuotientGroup.quotientKerEquivRange χH).toEquiv
        have hdvd : Nat.card χH.range ∣ (q : ℕ) - 1 := by
          have := Subgroup.card_subgroup_dvd_card χH.range
          rwa [Nat.card_eq_fintype_card (α := (ZMod (q : ℕ))ˣ), ZMod.card_units_eq_totient, Nat.totient_prime hqF.out] at this
        rw [hcard]
        intro h
        have := Nat.le_of_dvd (by omega) (h.trans hdvd)
        omega
      show ¬ (q : ℕ) ∣ ((H ⊓ Kχ).subgroupOf S).index
      rw [← Subgroup.relIndex, h1, h2, hSH]
      intro h
      rcases (Nat.Prime.dvd_mul hqF.out).mp h with h | h
      · exact h3 h
      · rcases (Nat.Prime.dvd_mul hqF.out).mp h with h | h
        · exact hIH h
        · exact hdiv h

end S_ExtCitation_tame_or_descent_of_isSimple
end P2MW
export P2MW.S_ExtCitation_tame_or_descent_of_isSimple (solution)
