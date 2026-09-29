-- Prove2me | solution 1 for ExtCitation.exists_frobenius_pow_inv_mul_mem_inertia_sup_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e4947a7c-2b26-5b9a-b29f-9f6e47d477fa

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_Deformations_Frobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_exists_frobenius_pow_inv_mul_mem_inertia_sup_level

set_option autoImplicit false

open ExtCitation
open scoped NNReal

namespace P2mS17K2

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

section LevelW

variable (q : ℕ) [Fact q.Prime]
variable (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

noncomputable abbrev Rw : ValuationSubring Kw := (padicIntegers q).comap (algebraMap Kw (PadicAlgCl q))

noncomputable abbrev Gw : Subgroup (GG q) := Kw.fixingSubgroup

noncomputable def RwToOO : Rw q Kw →+* OO q :=
  ((algebraMap Kw (PadicAlgCl q)).comp (Rw q Kw).subtype).codRestrict (padicIntegers q) (fun x => x.2)

noncomputable scoped instance algRwOO : Algebra (Rw q Kw) (OO q) := (RwToOO q Kw).toAlgebra

theorem algebraMap_Rw_coe (x : Rw q Kw) :
    ((algebraMap (Rw q Kw) (OO q) x : OO q) : PadicAlgCl q) = ((x : Kw) : PadicAlgCl q) := rfl

scoped instance smulCommRw : SMulCommClass (Gw q Kw) (Rw q Kw) (OO q) where
  smul_comm g r x := by
    apply Subtype.ext
    rw [Algebra.smul_def, Algebra.smul_def]
    change (g : GG q) ((algebraMap (Rw q Kw) (OO q) r : PadicAlgCl q) * (x : PadicAlgCl q))
      = (algebraMap (Rw q Kw) (OO q) r : PadicAlgCl q) * (g : GG q) (x : PadicAlgCl q)
    rw [map_mul, algebraMap_Rw_coe]
    congr 1
    exact (IntermediateField.mem_fixingSubgroup_iff Kw (g : GG q)).mp g.2 _ (r : Kw).2

scoped instance isInvariantRw : Algebra.IsInvariant (Rw q Kw) (OO q) (Gw q Kw) where
  isInvariant b hb := by
    haveI : IsGalois ℚ_[q] (PadicAlgCl q) := IsAlgClosure.isGalois ℚ_[q] (PadicAlgCl q)
    have hb' : (b : PadicAlgCl q) ∈ IntermediateField.fixedField (Gw q Kw) := by
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      exact congrArg Subtype.val (hb ⟨g, hg⟩)
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hb'
    refine ⟨⟨⟨(b : PadicAlgCl q), hb'⟩, ?_⟩, Subtype.ext rfl⟩
    show algebraMap Kw (PadicAlgCl q) ⟨(b : PadicAlgCl q), hb'⟩ ∈ padicIntegers q
    exact b.2

scoped instance csdRw : ContinuousSMulDiscrete (Gw q Kw) (OO q) := by
  rw [continuousSMulDiscrete_iff_isOpen_stabilizer]
  intro x
  have : (MulAction.stabilizer (Gw q Kw) x : Set (Gw q Kw))
      = Subtype.val ⁻¹' (MulAction.stabilizer (GG q) x : Set (GG q)) := by
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_preimage]
    rfl
  rw [this]
  exact (ContinuousSMulDiscrete.isOpen_stabilizer (GG q) x).preimage continuous_subtype_val

scoped instance compactGw : CompactSpace (Gw q Kw) :=
  isCompact_iff_compactSpace.mp (Kw.fixingSubgroup_isClosed.isCompact)

theorem stabilizerHom_surjective_Gw :
    Function.Surjective (Ideal.Quotient.stabilizerHom (IsLocalRing.maximalIdeal (OO q))
      ((IsLocalRing.maximalIdeal (OO q)).under (Rw q Kw)) (Gw q Kw)) := by
  haveI : Algebra.IsIntegral ℚ_[q] (PadicAlgCl q) := ⟨fun x => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral⟩
  letI : TopologicalSpace (OO q) := ⊥
  haveI : DiscreteTopology (OO q) := ⟨rfl⟩
  exact Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Gw q Kw)
    ((IsLocalRing.maximalIdeal (OO q)).under (Rw q Kw)) (IsLocalRing.maximalIdeal (OO q))

end LevelW

section Residues

variable (q : ℕ) [Fact q.Prime]

abbrev kbar : Type := IsLocalRing.ResidueField (OO q)

theorem natCast_residue_eq_zero : ((q : ℕ) : kbar q) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (OO q)), IsLocalRing.residue_eq_zero_iff]
  rw [← ValuationSubring.coe_mem_nonunits_iff]
  have : (((q : ℕ) : OO q) : PadicAlgCl q) = ((q : ℕ) : PadicAlgCl q) := by simp
  rw [this]
  exact natCast_mem_nonunits q

scoped instance charP_kbar : CharP (kbar q) q :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr (natCast_residue_eq_zero q)

noncomputable scoped instance algZModKbar : Algebra (ZMod q) (kbar q) := ZMod.algebra (kbar q) q

theorem algebraMap_toZMod (z : ℤ_[q]) :
    algebraMap (ZMod q) (kbar q) (PadicInt.toZMod z) = IsLocalRing.residue (OO q) (algebraMap ℤ_[q] (OO q) z) := by
  have hspec := PadicInt.toZMod_spec z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hspec
  obtain ⟨w, hw⟩ := hspec
  have hz : z = (ZMod.cast (PadicInt.toZMod z) : ℤ_[q]) + (q : ℤ_[q]) * w := by rw [← hw]; ring
  conv_rhs => rw [hz]
  rw [map_add, map_add, map_mul, map_mul, map_natCast, map_natCast, natCast_residue_eq_zero, zero_mul, add_zero,
    ZMod.cast_eq_val, map_natCast, map_natCast]
  change ZMod.cast (PadicInt.toZMod z) = ((PadicInt.toZMod z).val : kbar q)
  rw [ZMod.cast_eq_val]

noncomputable def kM (M : ℕ) : IntermediateField (ZMod q) (kbar q) where
  carrier := {y | y ^ (q ^ M) = y}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_pow, ha, hb]
  one_mem' := by simp only [Set.mem_setOf_eq, one_pow]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [add_pow_char_pow, ha, hb]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    exact zero_pow (pow_ne_zero _ (Fact.out : q.Prime).ne_zero)
  algebraMap_mem' a := by
    simp only [Set.mem_setOf_eq]
    rw [← map_pow, ZMod.pow_card_pow]
  inv_mem' a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [inv_pow, ha]

theorem mem_kM_iff {M : ℕ} {y : kbar q} : y ∈ kM q M ↔ y ^ (q ^ M) = y := Iff.rfl

theorem finite_kM (M : ℕ) (hM : 0 < M) : Finite (kM q M) := by
  classical
  have h1 : 1 < q ^ M := Nat.one_lt_pow hM.ne' (Fact.out : q.Prime).one_lt
  · have hne : (Polynomial.X ^ (q ^ M) - Polynomial.X : Polynomial (kbar q)) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero (kbar q) h1
    have hsub : ((kM q M) : Set (kbar q)) ⊆ ((Polynomial.X ^ (q ^ M) - Polynomial.X : Polynomial (kbar q)).roots.toFinset : Set (kbar q)) := by
      intro y hy
      rw [SetLike.mem_coe, mem_kM_iff] at hy
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hy, sub_self]
    exact Set.Finite.to_subtype (Set.Finite.subset (Finset.finite_toSet _) hsub)

noncomputable def resAut (M : ℕ) (g : GG q) : (kM q M) ≃ₐ[ZMod q] (kM q M) where
  toFun y := ⟨g • (y : kbar q), by
    have hy := y.2; rw [mem_kM_iff] at hy ⊢; rw [← smul_pow', hy]⟩
  invFun y := ⟨g⁻¹ • (y : kbar q), by
    have hy := y.2; rw [mem_kM_iff] at hy ⊢; rw [← smul_pow', hy]⟩
  left_inv y := Subtype.ext (inv_smul_smul g (y : kbar q))
  right_inv y := Subtype.ext (smul_inv_smul g (y : kbar q))
  map_mul' a b := Subtype.ext (smul_mul' g (a : kbar q) (b : kbar q))
  map_add' a b := Subtype.ext (smul_add g (a : kbar q) (b : kbar q))
  commutes' a := Subtype.ext (by
    change g • (algebraMap (ZMod q) (kbar q) a) = algebraMap (ZMod q) (kbar q) a
    have : algebraMap (ZMod q) (kbar q) a = ((a.val : ℕ) : kbar q) := by
      change ZMod.cast a = _; rw [ZMod.cast_eq_val]
    rw [this]
    exact map_natCast (MulSemiringAction.toRingHom (GG q) (kbar q) g) a.val)

theorem coe_resAut (M : ℕ) (g : GG q) (y : kM q M) : ((resAut q M g y : kM q M) : kbar q) = g • (y : kbar q) := rfl

theorem exists_smul_eq_pow (M : ℕ) (hM : 0 < M) (g : GG q) :
    ∃ n : ℕ, ∀ y : kbar q, y ∈ kM q M → g • y = y ^ (q ^ n) := by
  haveI : Finite (kM q M) := finite_kM q M hM
  haveI : Algebra.IsAlgebraic (ZMod q) (kM q M) := Algebra.IsAlgebraic.of_finite (ZMod q) (kM q M)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod q) (kM q M)).2 (resAut q M g)
  refine ⟨n, fun y hy => ?_⟩
  have := congrArg (fun e : (kM q M) ≃ₐ[ZMod q] (kM q M) => ((e ⟨y, hy⟩ : kM q M) : kbar q)) hn
  simp only [coe_resAut] at this
  rw [← this, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]
  rfl

theorem pow_pow_mul_eq {R : Type*} [Monoid R] {x : R} {a : ℕ} (h : x ^ (q ^ a) = x) (b : ℕ) : x ^ (q ^ (a * b)) = x := by
  induction b with
  | zero => simp
  | succ b ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

end Residues

section DegreeBound

variable (q : ℕ) [Fact q.Prime]
variable (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

theorem exists_monic_lift (x : Kw) (hx : x ∈ Rw q Kw) :
    ∃ P : Polynomial ℤ_[q], P.Monic ∧ P.map PadicInt.Coe.ringHom = minpoly ℚ_[q] x := by
  have hint : IsIntegral ℚ_[q] x := IsIntegral.of_finite ℚ_[q] x
  have hx1 : spectralNorm ℚ_[q] (PadicAlgCl q) (x : PadicAlgCl q) ≤ 1 := by
    have : ‖(x : PadicAlgCl q)‖₊ ≤ 1 := (mem_padicIntegers_iff q).mp hx
    have h' : ‖(x : PadicAlgCl q)‖ ≤ 1 := by exact_mod_cast this
    exact h'
  have hmin : minpoly ℚ_[q] (x : PadicAlgCl q) = minpoly ℚ_[q] x :=
    minpoly.algebraMap_eq (algebraMap Kw (PadicAlgCl q)).injective x
  have hlifts : minpoly ℚ_[q] x ∈ Polynomial.lifts (PadicInt.Coe.ringHom (p := q)) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun i => ?_
    have hci : ‖(minpoly ℚ_[q] x).coeff i‖ ≤ 1 := by
      rw [← hmin]
      have := (ciSup_le_iff (spectralValueTerms_bddAbove (minpoly ℚ_[q] (x : PadicAlgCl q)))).mp hx1 i
      simp only [spectralValueTerms] at this
      split_ifs at this with h
      · conv_rhs at this => rw [← Real.one_rpow (1 / (↑(minpoly ℚ_[q] (x : PadicAlgCl q)).natDegree - ↑i) : ℝ)]
        rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by
          rw [one_div_pos, sub_pos]; exact_mod_cast h)] at this
        exact this
      · obtain h | h := (le_of_not_gt h).eq_or_lt
        · have hmon' : (minpoly ℚ_[q] (x : PadicAlgCl q)).Monic := by rw [hmin]; exact minpoly.monic hint
          rw [← h, hmon'.coeff_natDegree, norm_one]
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h, norm_zero]; exact zero_le_one
    exact ⟨⟨_, hci⟩, rfl⟩
  obtain ⟨P, hP, -, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts (minpoly.monic hint)
  exact ⟨P, hmon, hP⟩

theorem residue_mem_kM (x : Rw q Kw) :
    IsLocalRing.residue (OO q) (algebraMap (Rw q Kw) (OO q) x) ∈ kM q (Module.finrank ℚ_[q] Kw).factorial := by
  classical
  obtain ⟨P, hmon, hP⟩ := exists_monic_lift q Kw (x : Kw) x.2
  set X : OO q := algebraMap (Rw q Kw) (OO q) x with hXdef
  set xb : kbar q := IsLocalRing.residue (OO q) X with hxbdef

  have h1 : Polynomial.eval₂ (algebraMap ℤ_[q] (OO q)) X P = 0 := by
    apply Subtype.val_injective
    rw [show ((Polynomial.eval₂ (algebraMap ℤ_[q] (OO q)) X P : OO q) : PadicAlgCl q)
        = Polynomial.eval₂ ((padicIntegers q).subtype.comp (algebraMap ℤ_[q] (OO q))) (X : PadicAlgCl q) P from
        Polynomial.hom_eval₂ P (algebraMap ℤ_[q] (OO q)) (padicIntegers q).subtype X]
    have hcomp : (padicIntegers q).subtype.comp (algebraMap ℤ_[q] (OO q))
        = (algebraMap ℚ_[q] (PadicAlgCl q)).comp PadicInt.Coe.ringHom := by
      ext z; rfl
    rw [hcomp, ← Polynomial.eval₂_map, hP, ZeroMemClass.coe_zero]
    change Polynomial.eval₂ (algebraMap ℚ_[q] (PadicAlgCl q)) (algebraMap Kw (PadicAlgCl q) (x : Kw)) (minpoly ℚ_[q] (x : Kw)) = 0
    rw [← Polynomial.aeval_def, Polynomial.aeval_algebraMap_apply, minpoly.aeval, map_zero]

  set Pb : Polynomial (ZMod q) := P.map (PadicInt.toZMod (p := q)) with hPbdef
  have h2 : Polynomial.aeval xb Pb = 0 := by
    rw [Polynomial.aeval_def, hPbdef, Polynomial.eval₂_map]
    have hcomp : (algebraMap (ZMod q) (kbar q)).comp (PadicInt.toZMod (p := q))
        = (IsLocalRing.residue (OO q)).comp (algebraMap ℤ_[q] (OO q)) := by
      ext z; exact algebraMap_toZMod q z
    rw [hcomp, hxbdef, ← Polynomial.hom_eval₂, h1, map_zero]
  have hPbmon : Pb.Monic := hmon.map _
  have hPbdeg : Pb.natDegree ≤ Module.finrank ℚ_[q] Kw := by
    rw [hPbdef, hmon.natDegree_map]
    have : P.natDegree = (minpoly ℚ_[q] (x : Kw)).natDegree := by rw [← hP, hmon.natDegree_map]
    rw [this]
    exact minpoly.natDegree_le (x : Kw)

  have hxbint : IsIntegral (ZMod q) xb := ⟨Pb, hPbmon, h2⟩
  let E := IntermediateField.adjoin (ZMod q) ({xb} : Set (kbar q))
  haveI : FiniteDimensional (ZMod q) E := IntermediateField.adjoin.finiteDimensional hxbint
  have hd : Module.finrank (ZMod q) E ≤ Module.finrank ℚ_[q] Kw := by
    rw [IntermediateField.adjoin.finrank hxbint]
    exact (Polynomial.natDegree_le_natDegree (minpoly.min (ZMod q) xb hPbmon h2)).trans hPbdeg
  have hdpos : 0 < Module.finrank (ZMod q) E := Module.finrank_pos
  haveI : Finite E := Module.finite_of_finite (ZMod q)
  letI : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = q ^ Module.finrank (ZMod q) E := by
    rw [Module.card_eq_pow_finrank (K := ZMod q) (V := E), ZMod.card]
  have hfermat : xb ^ (q ^ Module.finrank (ZMod q) E) = xb := by
    have := FiniteField.pow_card (⟨xb, IntermediateField.mem_adjoin_simple_self (ZMod q) xb⟩ : E)
    rw [hcard] at this
    exact congrArg Subtype.val this

  rw [mem_kM_iff]
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hdpos hd
  rw [hc]
  exact pow_pow_mul_eq q hfermat c

end DegreeBound

section Transport

variable (q : ℕ) [Fact q.Prime]

noncomputable abbrev rD : GG q →* ↥((padicPlace q).decompositionSubgroup ℚ) :=
  (localGaloisToGlobal q).codRestrict _ (localGaloisToGlobal_mem_decompositionSubgroup q)

theorem rD_smul_residue_eq_pow (w : GG q) (e : ℕ)
    (hw : ∀ x : OO q, ((w • x - x ^ e : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits)
    (a : ↥(padicPlace q)) :
    rD q w • IsLocalRing.residue _ a = (IsLocalRing.residue _ a) ^ e := by
  rw [← map_pow, ← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff, mem_nonunits_padicPlace_iff]
  let x : OO q := ⟨padicEmbedding q (a : AlgebraicClosure ℚ), a.2⟩
  have key := hw x
  have hcoe : padicEmbedding q (((rD q w • a - a ^ e : ↥(padicPlace q))) : AlgebraicClosure ℚ)
      = ((w • x - x ^ e : OO q) : PadicAlgCl q) := by
    simp only [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, map_sub, map_pow, coe_decomp_smul, coe_smul_OO,
      MonoidHom.codRestrict_apply, padicEmbedding_localGaloisToGlobal, x]
  rw [hcoe]
  exact key

theorem isFrobeniusAt_of_local (σ : GG q)
    (hσ : ∀ x : OO q, ((σ • x - x ^ q : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits) :
    (padicPlace q).IsFrobeniusAt (localGaloisToGlobal q σ) q :=
  ⟨localGaloisToGlobal_mem_decompositionSubgroup q σ, fun y => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact rD_smul_residue_eq_pow q σ q hσ a⟩

theorem rD_pow_smul (ψ : GG q) (hψ : (padicPlace q).IsFrobeniusAt (localGaloisToGlobal q ψ) q)
    (k : ℕ) (y : IsLocalRing.ResidueField ↥(padicPlace q)) : rD q (ψ ^ k) • y = y ^ (q ^ k) := by
  induction k generalizing y with
  | zero => rw [pow_zero, map_one, one_smul, pow_zero, pow_one]
  | succ k ih =>
    rw [pow_succ, map_mul, mul_smul, (show rD q ψ • y = y ^ q from hψ.smul_residue_eq y), smul_pow', ih, ← pow_mul, ← pow_succ]

theorem mem_inertiaPullback_iff_nat (g : GG q) :
    g ∈ ((padicPlace q).inertiaSubgroupIn ℚ).comap (localGaloisToGlobal q) ↔
      ∀ x : IsLocalRing.ResidueField ↥(padicPlace q), rD q g • x = x := by
  rw [Subgroup.mem_comap, ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map]
  constructor
  · rintro ⟨τ, hτ, hτg⟩
    intro x
    have hmem : rD q g = τ := by
      apply Subtype.ext; exact hτg.symm
    rw [hmem]
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hτ
    have := congrArg (fun φ => (φ : IsLocalRing.ResidueField ↥(padicPlace q) ≃+* _) x) hτ
    simpa using this
  · intro h
    refine ⟨rD q g, ?_, rfl⟩
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro x
    simpa using h x

theorem pow_smul_kbar (φ₀ : GG q) (hφ₀res : ∀ z : kbar q, φ₀ • z = z ^ q) (k : ℕ) (z : kbar q) :
    (φ₀ ^ k) • z = z ^ (q ^ k) := by
  induction k generalizing z with
  | zero => rw [pow_zero, one_smul, pow_zero, pow_one]
  | succ k ih => rw [pow_succ, mul_smul, hφ₀res, smul_pow', ih, ← pow_mul, ← pow_succ]

theorem main (φ : GG q) (hφ : (padicPlace q).IsFrobeniusAt (localGaloisToGlobal q φ) q)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] (g : GG q) :
    ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ ((padicPlace q).inertiaSubgroupIn ℚ).comap (localGaloisToGlobal q)
                        ⊔ (F.fixingSubgroup).comap (localGaloisToGlobal q) := by
  classical
  set I' : Subgroup (GG q) := ((padicPlace q).inertiaSubgroupIn ℚ).comap (localGaloisToGlobal q) with hI'def
  set U : Subgroup (GG q) := (F.fixingSubgroup).comap (localGaloisToGlobal q) with hUdef
  have memI' : ∀ w : GG q, (∀ y : IsLocalRing.ResidueField ↥(padicPlace q), rD q w • y = y) → w ∈ I' :=
    fun w hw => (mem_inertiaPullback_iff_nat q w).mpr hw

  obtain ⟨φ₀, hφ₀⟩ := exists_frob_local q
  have hφ₀' : (padicPlace q).IsFrobeniusAt (localGaloisToGlobal q φ₀) q := isFrobeniusAt_of_local q φ₀ hφ₀

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let b := Module.finBasis ℚ F
  let S : Set (PadicAlgCl q) := Set.range (fun i => padicEmbedding q ((b i : F) : AlgebraicClosure ℚ))
  haveI : Finite S := (Set.finite_range _).to_subtype
  let Kw : IntermediateField ℚ_[q] (PadicAlgCl q) := IntermediateField.adjoin ℚ_[q] S
  haveI : FiniteDimensional ℚ_[q] Kw := IntermediateField.finiteDimensional_adjoin (fun y hy => by
    obtain ⟨i, rfl⟩ := hy
    have h1 : IsIntegral ℚ (padicEmbedding q ((b i : F) : AlgebraicClosure ℚ)) :=
      (Algebra.IsAlgebraic.isAlgebraic ((b i : F) : AlgebraicClosure ℚ)).isIntegral.map (padicEmbedding q)
    exact h1.tower_top)

  have hGwU : ∀ u : GG q, u ∈ Gw q Kw → u ∈ U := by
    intro u hu
    rw [hUdef, Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    apply (padicEmbedding q).toRingHom.injective
    change padicEmbedding q (localGaloisToGlobal q u y) = padicEmbedding q y
    rw [padicEmbedding_localGaloisToGlobal]
    have hιy : padicEmbedding q y ∈ Kw := by
      have hrepr := b.sum_repr ⟨y, hy⟩
      have hy' : y = ∑ i, ((b.repr ⟨y, hy⟩ i : ℚ) : AlgebraicClosure ℚ) * ((b i : F) : AlgebraicClosure ℚ) := by
        have h0 := congrArg Subtype.val hrepr
        rw [AddSubmonoidClass.coe_finset_sum] at h0
        change ((⟨y, hy⟩ : F) : AlgebraicClosure ℚ) = _
        rw [← h0]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Rat.smul_def]
        rfl
      rw [hy', map_sum]
      refine Subalgebra.sum_mem _ fun i _ => ?_
      rw [map_mul, map_ratCast]
      have hbi : padicEmbedding q ((b i : F) : AlgebraicClosure ℚ) ∈ Kw :=
        IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
      exact Subalgebra.mul_mem _ (SubfieldClass.ratCast_mem Kw _) hbi
    exact (IntermediateField.mem_fixingSubgroup_iff Kw u).mp hu _ hιy

  set N : ℕ := Module.finrank ℚ_[q] Kw with hNdef
  obtain ⟨n, hn⟩ := exists_smul_eq_pow q N.factorial (Nat.factorial_pos N) g
  set h : GG q := (φ₀ ^ n)⁻¹ * g with hhdef
  have hφ₀res : ∀ z : kbar q, φ₀ • z = z ^ q := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    rw [← IsLocalRing.ResidueField.residue_smul, ← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ← ValuationSubring.coe_mem_nonunits_iff]
    exact hφ₀ x
  have hφ₀n : ∀ z : kbar q, (φ₀ ^ n) • z = z ^ (q ^ n) := pow_smul_kbar q φ₀ hφ₀res n
  have hh : ∀ x : Rw q Kw,
      h • IsLocalRing.residue (OO q) (algebraMap (Rw q Kw) (OO q) x)
        = IsLocalRing.residue (OO q) (algebraMap (Rw q Kw) (OO q) x) := by
    intro x
    have hy := hn _ (residue_mem_kM q Kw x)
    rw [hhdef, mul_smul, hy, ← hφ₀n, inv_smul_smul]

  let Q := IsLocalRing.maximalIdeal (OO q)
  let σbar : (OO q ⧸ Q) ≃ₐ[Rw q Kw ⧸ Q.under (Rw q Kw)] (OO q ⧸ Q) :=
    { MulSemiringAction.toRingEquiv (GG q) (kbar q) h with
      commutes' := fun r => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        exact hh r }
  obtain ⟨u, hu⟩ := stabilizerHom_surjective_Gw q Kw σbar
  set uG : GG q := ((u : Gw q Kw) : GG q) with huGdef
  have hu' : ∀ bb : OO q, IsLocalRing.residue (OO q) (uG • bb) = h • IsLocalRing.residue (OO q) bb := by
    intro bb
    have := congrArg (fun e => e (Ideal.Quotient.mk Q bb)) hu
    exact this

  have hw : ∀ x : OO q, (((h⁻¹ * uG) • x - x ^ 1 : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits := by
    intro x
    rw [ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, pow_one,
      IsLocalRing.ResidueField.residue_smul, mul_smul, ← IsLocalRing.ResidueField.residue_smul, hu', inv_smul_smul]
  have hwI : h⁻¹ * uG ∈ I' := by
    refine memI' _ fun y => ?_
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    rw [rD_smul_residue_eq_pow q _ 1 hw a, pow_one]

  have hφφ₀ : (φ ^ n)⁻¹ * φ₀ ^ n ∈ I' := by
    refine memI' _ fun y => ?_
    rw [map_mul, map_inv, mul_smul, rD_pow_smul q φ₀ hφ₀' n y, ← rD_pow_smul q φ hφ n y, inv_smul_smul]

  refine ⟨n, ?_⟩
  have heq : (φ ^ n)⁻¹ * g = ((φ ^ n)⁻¹ * φ₀ ^ n) * uG * (h⁻¹ * uG)⁻¹ := by
    rw [hhdef]; group
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hφφ₀) (Subgroup.mem_sup_right (hGwU uG u.1.2)))
    (Subgroup.mem_sup_left (Subgroup.inv_mem _ hwI))

end Transport

end P2mS17K2
p2m_reactivate "P2MW.S_ExtCitation_exists_frobenius_pow_inv_mul_mem_inertia_sup_level.P2mS17K2"

open P2mS17K2 in
theorem solution (q : Nat.Primes)
    (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] (g : primeLocalGaloisGroup q) :
    ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)
                        ⊔ (F.fixingSubgroup).comap (primeLocalToGlobal q) := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  exact main (q : ℕ) φ hφ F g

end S_ExtCitation_exists_frobenius_pow_inv_mul_mem_inertia_sup_level
end P2MW
export P2MW.S_ExtCitation_exists_frobenius_pow_inv_mul_mem_inertia_sup_level (solution)
