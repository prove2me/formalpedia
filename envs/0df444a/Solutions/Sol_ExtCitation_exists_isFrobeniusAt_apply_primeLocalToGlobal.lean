-- Prove2me | solution 1 for ExtCitation.exists_isFrobeniusAt_apply_primeLocalToGlobal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/3495a13d-501e-5476-80e7-4a85f7ae918b

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_Deformations_Frobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal

set_option autoImplicit false

open ExtCitation
open scoped NNReal

namespace P2mS17K1

theorem index_op_s17 {G : Type*} [Group G] (H : Subgroup G) :
    H.op.index = H.index := by
  trans (H.comap (MulEquiv.inv' G).symm.toMonoidHom).index
  · congr 1
    ext; simp
  · exact Subgroup.index_comap_of_surjective _ (MulEquiv.inv' G).symm.surjective

scoped instance finiteIndex_op_s17 {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] :
    H.op.FiniteIndex := ⟨by rw [index_op_s17]; exact Subgroup.FiniteIndex.index_ne_zero⟩

lemma totallyBounded_s17 {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : ∀ s ∈ nhds (1 : G), ∃ H : Subgroup G, H.FiniteIndex ∧ ↑H ⊆ s) :
    letI := IsTopologicalGroup.rightUniformSpace G
    TotallyBounded (Set.univ : Set G) := by
  letI := IsTopologicalGroup.rightUniformSpace G
  rintro s ⟨t, ht1, hts⟩
  obtain ⟨H, hH, hHs⟩ := H _ ht1
  have : Finite (Gᵐᵒᵖ ⧸ H.op) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨Set.range (MulOpposite.unop ∘ Quotient.out : Gᵐᵒᵖ ⧸ H.op → G),
    Set.finite_range _, fun x _ ↦
      Set.mem_iUnion₂_of_mem ⟨QuotientGroup.mk (.op x), rfl⟩ (hts (hHs ?_))⟩
  dsimp only
  rw [Function.comp_apply, SetLike.mem_coe, ← MulOpposite.unop_op (x⁻¹),
    ← MulOpposite.unop_mul, ← Subgroup.mem_op, MulOpposite.op_inv, ← QuotientGroup.eq]
  simp

scoped instance finiteIndex_fixingSubgroup_s17 {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] : E.fixingSubgroup.FiniteIndex := by
  let f : (L ≃ₐ[K] L) ⧸ E.fixingSubgroup → E →ₐ[K] L := Quotient.lift
    (fun f ↦ f.toAlgHom.comp E.val)
    (by rintro _ τ ⟨σ, rfl⟩; ext x; exact DFunLike.congr_arg τ (σ.2 x))
  have : Function.Injective f := by
    rintro ⟨σ⟩ ⟨τ⟩ (H : σ.toAlgHom.comp E.val = τ.toAlgHom.comp E.val)
    refine Quotient.sound ⟨⟨.op (τ⁻¹ * σ), fun x ↦ ?_⟩, by simp⟩
    simpa [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] using DFunLike.congr_fun H x
  have := Finite.of_injective _ this
  exact Subgroup.finiteIndex_of_finite_quotient

open IntermediateField in
scoped instance compactSpace_gal {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    CompactSpace (L ≃ₐ[K] L) := by
  classical
  letI := IsTopologicalGroup.rightUniformSpace (L ≃ₐ[K] L)
  rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete]
  refine ⟨totallyBounded_s17 fun s hs ↦ ?_, ?_⟩
  · obtain ⟨E, hE, H⟩ := (krullTopology_mem_nhds_one_iff _ _ _).mp hs
    refine ⟨_, inferInstance, H⟩
  · rintro f hf -
    have := hf.1
    have (x : L) :
        ∃ σ₀ : L ≃ₐ[K] L, ∃ t ∈ f, ∀ σ ∈ t, ∀ τ : L ≃ₐ[K] L, σ (τ x) = σ₀ (τ x) := by
      have : FiniteDimensional K K⟮x⟯ :=
        adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
      obtain ⟨t, htf, H⟩ := ((Filter.HasBasis.cauchy_iff
        (by exact (galGroupBasis K L).nhds_one_hasBasis.comap _)).mp hf).2 _ (by
            exact ⟨_, ⟨normalClosure K K⟮x⟯ L, inferInstanceAs (FiniteDimensional K _), rfl⟩, rfl⟩)
      obtain ⟨σ, hσ⟩ := f.nonempty_of_mem htf
      refine ⟨σ, t, htf, fun τ hτ τ₀ ↦ ?_⟩
      have : σ (τ.symm (τ (τ₀ x))) = τ (τ₀ x) := H τ hτ σ hσ ⟨τ (τ₀ x), by
        refine SetLike.le_def.mp (le_iSup _ (τ.toAlgHom.comp <| τ₀.toAlgHom.comp (val _))) ?_
        exact ⟨⟨_, subset_adjoin _ _ (by simp)⟩, rfl⟩⟩
      simpa using this.symm
    choose σ₀ t htf H using this
    have H' (s σ hσ) := H s σ hσ .refl
    dsimp at H'
    let F : L ≃ₐ[K] L :=
    { toFun x := σ₀ x x
      invFun x := (σ₀ x).symm x
      left_inv x := by
        obtain ⟨σ, hσ₁, hσ₂⟩ := f.nonempty_of_mem (f.inter_mem (htf x) (htf (σ₀ x x)))
        dsimp
        have H' := H' _ _ hσ₁
        have : σ x = (σ₀ (σ₀ x x) x) := by simpa using H _ _ hσ₂ (σ₀ x).symm
        rw [← H', AlgEquiv.symm_apply_eq, H', ← this, H']
      right_inv x := by
        obtain ⟨σ, hσ₁, hσ₂⟩ := f.nonempty_of_mem (f.inter_mem (htf x) (htf ((σ₀ x).symm x)))
        dsimp
        replace H := H _ _ hσ₁ σ.symm
        simp only [AlgEquiv.apply_symm_apply, ← AlgEquiv.symm_apply_eq, AlgEquiv.symm_symm] at H
        rw [← H' _ _ hσ₂, H]
      map_mul' x y := by
        obtain ⟨σ, hσx, hσy, hσxy⟩ :=
          f.nonempty_of_mem (f.inter_mem (htf x) (f.inter_mem (htf y) (htf (x * y))))
        rw [← H' _ _ hσxy, ← H' _ _ hσx, ← H' _ _ hσy, map_mul]
      map_add' x y := by
        obtain ⟨σ, hσx, hσy, hσxy⟩ :=
          f.nonempty_of_mem (f.inter_mem (htf x) (f.inter_mem (htf y) (htf (x + y))))
        rw [← H' _ _ hσxy, ← H' _ _ hσx, ← H' _ _ hσy, map_add]
      commutes' := by simp }
    refine ⟨F, Set.mem_univ _, ?_⟩
    rw [((galGroupBasis K L).nhds_hasBasis F).ge_iff]
    rintro _ ⟨_, ⟨E, hE, rfl⟩, rfl⟩
    simp only [Set.image_mul_left]
    have ⟨s, hs⟩ := E.toSubmodule.fg_iff_finiteDimensional.mpr hE
    refine f.mem_of_superset ((Filter.biInter_finset_mem s).mpr fun i _ ↦ htf i) ?_
    rintro σ hσ ⟨x, hx⟩
    change F.symm (σ x) = x
    induction hs.ge hx using Submodule.span_induction with
    | zero | add | smul => simp_all
    | mem x h =>
      rw [AlgEquiv.symm_apply_eq]
      simp [F, ← H' _ _ (Set.mem_iInter₂.mp hσ _ h)]

open scoped IntermediateField in
scoped instance continuousSMulDiscrete_gal {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    ContinuousSMulDiscrete (L ≃ₐ[K] L) L := by
  constructor
  intro x y
  rw [isOpen_iff_forall_mem_open]
  rintro σ (hσ : _ = _)
  have : FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional
      (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral
  refine ⟨_, ?_, K⟮x⟯.fixingSubgroup_isOpen.smul σ, 1, one_mem _, by simp⟩
  rintro _ ⟨τ, hτ, rfl⟩
  have := (mem_fixingSubgroup_iff _).mp hτ x (IntermediateField.mem_adjoin_simple_self K x)
  simp only [smul_eq_mul, Set.mem_setOf_eq, mul_smul, this, hσ]

scoped instance isInvariant_gal {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Algebra.IsInvariant K L (L ≃ₐ[K] L) :=
  ⟨fun _ H ↦ (InfiniteGalois.fixedField_fixingSubgroup
    (⊥ : IntermediateField K L)).le fun _ ↦ H _⟩

section Local

variable (q : ℕ) [Fact q.Prime]

abbrev OO : Type := ↥(padicIntegers q)

abbrev GG : Type := PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q

noncomputable scoped instance smulOO : SMul (GG q) (OO q) :=
  ⟨fun g x => ⟨g (x : PadicAlgCl q), by
    rw [mem_padicIntegers_iff, nnnorm_padicAlgCl_algEquiv]; exact (mem_padicIntegers_iff q).mp x.2⟩⟩

@[scoped simp] theorem coe_smul_OO (g : GG q) (x : OO q) : ((g • x : OO q) : PadicAlgCl q) = g (x : PadicAlgCl q) := rfl

noncomputable scoped instance actOO : MulSemiringAction (GG q) (OO q) where
  one_smul x := Subtype.ext rfl
  mul_smul g h x := Subtype.ext rfl
  smul_zero g := Subtype.ext (map_zero g)
  smul_add g x y := Subtype.ext (map_add g _ _)
  smul_one g := Subtype.ext (map_one g)
  smul_mul g x y := Subtype.ext (map_mul g _ _)

noncomputable def intToOO : ℤ_[q] →+* OO q :=
  ((algebraMap ℚ_[q] (PadicAlgCl q)).comp PadicInt.Coe.ringHom).codRestrict (padicIntegers q) (fun x => by
    show algebraMap ℚ_[q] (PadicAlgCl q) (x : ℚ_[q]) ∈ padicIntegers q
    rw [mem_padicIntegers_iff, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
    change ‖((x : ℚ_[q]) : PadicAlgCl q)‖ ≤ 1
    rw [PadicAlgCl.norm_extends]
    exact x.2)

noncomputable scoped instance algOO : Algebra ℤ_[q] (OO q) := (intToOO q).toAlgebra

theorem algebraMap_OO_coe (x : ℤ_[q]) :
    ((algebraMap ℤ_[q] (OO q) x : OO q) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) (x : ℚ_[q]) := rfl

scoped instance smulCommOO : SMulCommClass (GG q) ℤ_[q] (OO q) where
  smul_comm g r x := by
    apply Subtype.ext
    rw [Algebra.smul_def, Algebra.smul_def]
    change g ((algebraMap ℤ_[q] (OO q) r : PadicAlgCl q) * (x : PadicAlgCl q))
      = (algebraMap ℤ_[q] (OO q) r : PadicAlgCl q) * g (x : PadicAlgCl q)
    rw [map_mul, algebraMap_OO_coe, AlgEquiv.commutes]

scoped instance isInvariantOO : Algebra.IsInvariant ℤ_[q] (OO q) (GG q) where
  isInvariant b hb := by
    haveI : IsGalois ℚ_[q] (PadicAlgCl q) := IsAlgClosure.isGalois ℚ_[q] (PadicAlgCl q)
    have hb' : ∀ g : GG q, g • (b : PadicAlgCl q) = b := fun g => congrArg Subtype.val (hb g)
    obtain ⟨x, hx⟩ := Algebra.IsInvariant.isInvariant (A := ℚ_[q]) (G := GG q) (b : PadicAlgCl q) hb'
    have hx1 : ‖x‖ ≤ 1 := by
      rw [← PadicAlgCl.norm_extends]
      change ‖algebraMap ℚ_[q] (PadicAlgCl q) x‖ ≤ 1
      rw [hx]
      have := (mem_padicIntegers_iff q).mp b.2
      exact_mod_cast this
    exact ⟨⟨x, hx1⟩, Subtype.ext hx⟩

scoped instance csdOO : ContinuousSMulDiscrete (GG q) (OO q) := by
  rw [continuousSMulDiscrete_iff_isOpen_stabilizer]
  intro x
  have : (MulAction.stabilizer (GG q) x : Set (GG q)) = MulAction.stabilizer (GG q) (x : PadicAlgCl q) := by
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [this]
  exact ContinuousSMulDiscrete.isOpen_stabilizer (GG q) (x : PadicAlgCl q)

theorem natCast_mem_nonunits : ((q : ℕ) : PadicAlgCl q) ∈ (padicIntegers q).nonunits := by
  have hq : Valued.v ((q : ℕ) : PadicAlgCl q) = 1 / (q : ℝ≥0) := PadicAlgCl.valuation_p q
  have hq2 : (2 : ℕ) ≤ q := (Fact.out : q.Prime).two_le
  rw [ValuationSubring.mem_nonunits_iff, ← (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one]
  change Valued.v ((q : ℕ) : PadicAlgCl q) < 1
  rw [hq, div_lt_one (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hq2)]
  exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hq2

theorem under_maximalIdeal_eq :
    (IsLocalRing.maximalIdeal (OO q)).under ℤ_[q] = IsLocalRing.maximalIdeal ℤ_[q] := by
  set P := (IsLocalRing.maximalIdeal (OO q)).under ℤ_[q] with hPdef
  have hqP : ((q : ℕ) : ℤ_[q]) ∈ P := by
    change ((q : ℕ) : ℤ_[q]) ∈ Ideal.comap (algebraMap ℤ_[q] (OO q)) (IsLocalRing.maximalIdeal (OO q))
    rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff, map_natCast]
    have : (((q : ℕ) : OO q) : PadicAlgCl q) = ((q : ℕ) : PadicAlgCl q) := by simp
    rw [this]
    exact natCast_mem_nonunits q
  have hP0 : P ≠ ⊥ := fun h => by
    have h0 : ((q : ℕ) : ℤ_[q]) = 0 := by simpa [h] using hqP
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) h0
  haveI : P.IsPrime := Ideal.IsPrime.under ℤ_[q] (IsLocalRing.maximalIdeal (OO q))
  exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal ‹P.IsPrime› hP0)

theorem exists_frob_local : ∃ σ : GG q, ∀ x : OO q,
    ((σ • x - x ^ q : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits := by
  haveI : Algebra.IsIntegral ℚ_[q] (PadicAlgCl q) := ⟨fun x => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral⟩
  let Q := IsLocalRing.maximalIdeal (OO q)
  have hP : Q.under ℤ_[q] = IsLocalRing.maximalIdeal ℤ_[q] := under_maximalIdeal_eq q
  haveI : Finite (ℤ_[q] ⧸ Q.under ℤ_[q]) := by
    rw [hP]
    exact Finite.of_equiv _ (PadicInt.residueField (p := q)).toEquiv.symm
  have hcard : Nat.card (ℤ_[q] ⧸ Q.under ℤ_[q]) = q := by
    rw [Nat.card_congr ((Ideal.quotEquivOfEq hP).toEquiv.trans (PadicInt.residueField (p := q)).toEquiv), Nat.card_zmod]
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant_of_profinite ℤ_[q] (GG q) Q
  refine ⟨σ, fun x => ?_⟩
  have hx := hσ x
  rw [hcard] at hx
  exact ValuationSubring.coe_mem_nonunits_iff.mpr hx

end Local

theorem mem_nonunits_comap {K L : Type*} [Field K] [Field L] {B : ValuationSubring L} {f : K →+* L} {x : K} :
    x ∈ (B.comap f).nonunits ↔ f x ∈ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap, map_inv₀]
  constructor
  · rintro (rfl | h)
    · exact Or.inl (map_zero f)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ((map_eq_zero f).mp h)
    · exact Or.inr h

theorem mem_nonunits_padicPlace_iff (q : ℕ) [Fact q.Prime] {x : AlgebraicClosure ℚ} :
    x ∈ (padicPlace q).nonunits ↔ padicEmbedding q x ∈ (padicIntegers q).nonunits := by
  rw [padicPlace, mem_nonunits_comap]
  rfl

theorem coe_decomp_smul {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    (d : A.decompositionSubgroup K) (a : A) : ((d • a : A) : L) = (d : L ≃ₐ[K] L) a := rfl

end P2mS17K1
p2m_reactivate "P2MW.S_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal.P2mS17K1"

open P2mS17K1 in
theorem solution (q : Nat.Primes) :
    ∃ φ : primeLocalGaloisGroup q, (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  show ∃ φ : PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ),
    (padicPlace (q : ℕ)).IsFrobeniusAt (localGaloisToGlobal (q : ℕ) φ) q
  obtain ⟨σ, hσ⟩ := exists_frob_local (q : ℕ)
  let D : ↥((padicPlace (q : ℕ)).decompositionSubgroup ℚ) :=
    ⟨localGaloisToGlobal (q : ℕ) σ, localGaloisToGlobal_mem_decompositionSubgroup (q : ℕ) σ⟩
  refine ⟨σ, D.2, fun y => ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  change D • IsLocalRing.residue _ a = IsLocalRing.residue _ a ^ (q : ℕ)
  rw [← map_pow, ← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff, mem_nonunits_padicPlace_iff]
  let x : OO (q : ℕ) := ⟨padicEmbedding (q : ℕ) (a : AlgebraicClosure ℚ), a.2⟩
  have key := hσ x
  have hcoe : padicEmbedding (q : ℕ) (((D • a - a ^ (q : ℕ) : ↥(padicPlace (q : ℕ))) : AlgebraicClosure ℚ))
      = ((σ • x - x ^ (q : ℕ) : OO (q : ℕ)) : PadicAlgCl (q : ℕ)) := by
    simp only [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, map_sub, map_pow, coe_decomp_smul, coe_smul_OO,
      padicEmbedding_localGaloisToGlobal, x, D]
  rw [hcoe]
  exact key

end S_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
end P2MW
export P2MW.S_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal (solution)
