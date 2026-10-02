-- Prove2me | solution 1 for ChebotarevDensity.cyclePattern_eq_decompositionType
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T13:53:32.015868+00:00
-- url     : https://prove2.me/submissions/1c4fa00f-cbf2-48be-948f-e89acb25a02f

import Definitions.Def_ChebotarevDensity_Defs
import Theorems.Thm_ChebotarevDensity_frobeniusCyclePattern_eq_factorDegrees

open Polynomial NumberField
open ChebotarevDensity

private lemma parts_eq_of_equiv {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) (a : Equiv.Perm α) (b : Equiv.Perm β)
    (h : ∀ x, e (a x) = b (e x)) : a.partition.parts = b.partition.parts := by
  have hcard : Fintype.card α = Fintype.card β := Fintype.card_congr e
  let e' : α ≃ {y : β // True} := e.trans (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm
  have hb : b = a.extendDomain e' := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    have := Equiv.Perm.extendDomain_apply_image a e' x
    rw [← h x]
    simpa [e'] using this.symm
  have hct : a.cycleType = b.cycleType := by
    rw [hb]; exact (Equiv.Perm.cycleType_extendDomain e').symm
  rw [Equiv.Perm.parts_partition, Equiv.Perm.parts_partition, hct, hcard]
  congr 2
  have h1 := Equiv.Perm.sum_cycleType a
  have h2 := Equiv.Perm.sum_cycleType b
  rw [hct] at h1
  have : a.support.card = b.support.card := by omega
  rw [this]

private lemma parts_eq_of_rel {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (R : α → β → Prop) (hfun : ∀ x y y', R x y → R x y' → y = y')
    (htot : ∀ x, ∃ y, R x y) (hsurj : ∀ y, ∃ x, R x y)
    (hcard : Fintype.card α = Fintype.card β) (a : Equiv.Perm α) (b : Equiv.Perm β)
    (hab : ∀ x y, R x y → R (a x) (b y)) : a.partition.parts = b.partition.parts := by
  choose e he using htot
  have hsurj' : Function.Surjective e := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, hfun x _ _ (he x) hx⟩
  have hbij : Function.Bijective e := (Fintype.bijective_iff_surjective_and_card e).mpr ⟨hsurj', hcard⟩
  refine parts_eq_of_equiv (Equiv.ofBijective e hbij) a b ?_
  intro x
  exact hfun _ _ _ (he _) (hab _ _ (he x))

private lemma separable_map_of_discr {F : Type*} [Field F] (φ : ℤ →+* F) (f : ℤ[X])
    (hf : f.Monic) (h : φ f.discr ≠ 0) : (f.map φ).Separable := by
  by_cases h0 : f.natDegree = 0
  · rw [eq_one_of_monic_natDegree_zero hf h0]; simp
  have hpos : 0 < f.degree := by
    rw [← natDegree_pos_iff_degree_pos]; omega
  have hres := resultant_deriv hpos
  have hm : (f.map φ).Monic := hf.map φ
  have hdeg : (f.map φ).natDegree = f.natDegree := hf.natDegree_map φ
  have h1 := congrArg φ hres
  rw [← resultant_map_map, hf.leadingCoeff] at h1
  simp only [map_mul, map_pow, map_neg, map_one] at h1
  have hne : (f.map φ).resultant (derivative (f.map φ)) f.natDegree (f.natDegree - 1) ≠ 0 := by
    rw [derivative_map, h1]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp)) one_ne_zero) h
  obtain ⟨a, b, -, -, hab⟩ := exists_mul_add_mul_eq_C_resultant (f.map φ)
    (derivative (f.map φ)) (m := f.natDegree) (n := f.natDegree - 1) hdeg.le
    (natDegree_derivative_le _ |>.trans (by omega)) (Or.inl h0)
  refine ⟨C ((f.map φ).resultant (derivative (f.map φ)) f.natDegree (f.natDegree - 1))⁻¹ * a,
    C ((f.map φ).resultant (derivative (f.map φ)) f.natDegree (f.natDegree - 1))⁻¹ * b, ?_⟩
  have : (C ((f.map φ).resultant (derivative (f.map φ)) f.natDegree (f.natDegree - 1))⁻¹ : F[X]) *
      C ((f.map φ).resultant (derivative (f.map φ)) f.natDegree (f.natDegree - 1)) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hne, C_1]
  rw [← this, ← hab]
  ring

open scoped Classical in
private lemma galActionHom_parts {F E : Type*} [Field F] [Field E] [Algebra F E] (p : F[X])
    [Fact ((p.map (algebraMap F E)).Splits)] (σ : p.Gal) :
    (Gal.galActionHom p E σ).partition.parts =
      (MulAction.toPermHom p.Gal (p.rootSet p.SplittingField) σ).partition.parts := by
  refine parts_eq_of_equiv (Gal.rootsEquivRoots p E).symm _ _ ?_
  intro x
  show (Gal.rootsEquivRoots p E).symm (σ • x) = σ • (Gal.rootsEquivRoots p E).symm x
  rw [Gal.smul_def, Equiv.symm_apply_apply]

open scoped Classical in
private lemma cyclePattern_eq (f : ℤ[X]) (σ : GalGroup f) :
    cyclePattern f σ = (MulAction.toPermHom (ratPoly f).Gal
      ((ratPoly f).rootSet (SplitField f)) σ).partition.parts := by
  unfold cyclePattern
  have : Fact ((ratPoly f).map (algebraMap ℚ ℂ)).Splits := ⟨IsAlgClosed.splits _⟩
  exact galActionHom_parts _ σ

open scoped Classical in
private lemma frobeniusCyclePattern_eq (p : ℕ) [Fact p.Prime] (g : (ZMod p)[X]) :
    frobeniusCyclePattern p g = (MulAction.toPermHom g.Gal (g.rootSet g.SplittingField)
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) g.SplittingField)).partition.parts := by
  unfold frobeniusCyclePattern
  have : Fact (g.map (algebraMap (ZMod p) g.SplittingField)).Splits :=
    ⟨SplittingField.splits g⟩
  exact galActionHom_parts _ _

private lemma under_eq_span {K : Type*} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] (hpQ : (p : 𝓞 K) ∈ Q) :
    Q.under ℤ = Ideal.span {(p : ℤ)} := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := by
    have : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    exact PrincipalIdealRing.isMaximal_of_irreducible this.irreducible
  have hle : Ideal.span {(p : ℤ)} ≤ Q.under ℤ := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simpa [Ideal.under] using hpQ
  exact (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm

private lemma aeval_ratPoly {A : Type*} [CommRing A] [Algebra ℚ A] (f : ℤ[X]) (x : A) :
    aeval x (ratPoly f) = aeval (R := ℤ) x f := by
  have : ratPoly f = f.map (algebraMap ℤ ℚ) := by simp [ratPoly]
  rw [this, aeval_map_algebraMap]

private lemma aeval_modp {A : Type*} [CommRing A] (p : ℕ) [Algebra (ZMod p) A] (f : ℤ[X]) (x : A) :
    aeval x (f.map (Int.castRingHom (ZMod p))) = aeval (R := ℤ) x f := by
  have : f.map (Int.castRingHom (ZMod p)) = f.map (algebraMap ℤ (ZMod p)) := by simp
  rw [this, aeval_map_algebraMap]

private lemma map_modp_eq {A : Type*} [CommRing A] (p : ℕ) [Algebra (ZMod p) A] (f : ℤ[X]) :
    (f.map (Int.castRingHom (ZMod p))).map (algebraMap (ZMod p) A) = f.map (algebraMap ℤ A) := by
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext_int _ _

private lemma isIntegral_of_aeval {A : Type*} [CommRing A] (f : ℤ[X]) (hf : f.Monic) (x : A)
    (h : aeval (R := ℤ) x f = 0) : IsIntegral ℤ x :=
  ⟨f, hf, by simpa [aeval_def] using h⟩

private lemma map_int_eq {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (f : ℤ[X]) :
    (f.map (algebraMap ℤ A)).map (algebraMap A B) = f.map (algebraMap ℤ B) := by
  rw [Polynomial.map_map]
  congr 1
  exact Subsingleton.elim _ _

private lemma splits_ringOfIntegers (f : ℤ[X]) (hf : f.Monic) :
    (f.map (algebraMap ℤ (𝓞 (SplitField f)))).Splits := by
  have hK : (f.map (algebraMap ℤ (SplitField f))).Splits := by
    have h : ((ratPoly f).map (algebraMap ℚ (SplitField f))).Splits := SplittingField.splits _
    have e : (ratPoly f).map (algebraMap ℚ (SplitField f)) = f.map (algebraMap ℤ (SplitField f)) := by
      show (f.map (Int.castRingHom ℚ)).map _ = _
      rw [Polynomial.map_map]
      congr 1
    rwa [e] at h
  refine Splits.of_splits_map_of_injective (i := algebraMap (𝓞 (SplitField f)) (SplitField f))
    (FaithfulSMul.algebraMap_injective _ _) ?_ ?_
  · rw [map_int_eq]; exact hK
  · intro a ha
    have hne : (f.map (algebraMap ℤ (𝓞 (SplitField f)))).map
        (algebraMap (𝓞 (SplitField f)) (SplitField f)) ≠ 0 := by
      rw [map_int_eq]
      exact (hf.map _).ne_zero
    rw [mem_roots hne, IsRoot, map_int_eq] at ha
    have : aeval (R := ℤ) a f = 0 := by
      rw [aeval_def, ← eval_map]; exact ha
    exact ⟨⟨a, isIntegral_of_aeval f hf a this⟩, rfl⟩

private lemma coe_aeval {K : Type*} [Field K] [NumberField K] (f : ℤ[X]) (z : 𝓞 K) :
    ((aeval (R := ℤ) z f : 𝓞 K) : K) = aeval (R := ℤ) (z : K) f :=
  (aeval_algHom_apply (IsScalarTower.toAlgHom ℤ (𝓞 K) K) z f).symm

private lemma aeval_ringHom {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (x : A)
    (f : ℤ[X]) : aeval (R := ℤ) (φ x) f = φ (aeval (R := ℤ) x f) :=
  aeval_algHom_apply φ.toIntAlgHom x f

open scoped Classical in
private lemma core (f : ℤ[X]) (hf : f.Monic) (p : ℕ) [Fact p.Prime]
    (hsepK : (ratPoly f).Separable) (hsepg : (f.map (Int.castRingHom (ZMod p))).Separable)
    (σ : GalGroup f) (hσ : IsFrobeniusAt f p σ) :
    cyclePattern f σ = frobeniusCyclePattern p (f.map (Int.castRingHom (ZMod p))) := by
  rw [cyclePattern_eq, frobeniusCyclePattern_eq]
  obtain ⟨Q, hQ, hpQ, hF⟩ := hσ
  have hunder := under_eq_span p (Fact.out) Q hpQ
  have hcard : Nat.card (ℤ ⧸ Q.under ℤ) = p := by
    rw [hunder]
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv]
    exact Nat.card_zmod p
  have hQmax : Q.IsMaximal := by
    refine Ideal.IsPrime.isMaximal hQ ?_
    rintro rfl
    have : (p : 𝓞 (SplitField f)) = 0 := by simpa using hpQ
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) this
  let : Field (𝓞 (SplitField f) ⧸ Q) := Ideal.Quotient.field Q
  have hpk : ((p : ℕ) : 𝓞 (SplitField f) ⧸ Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpQ
  have : CharP (𝓞 (SplitField f) ⧸ Q) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hpk
  let : Algebra (ZMod p) (𝓞 (SplitField f) ⧸ Q) := ZMod.algebra _ p
  have hsplO := splits_ringOfIntegers f hf
  have hsplk : ((f.map (Int.castRingHom (ZMod p))).map
      (algebraMap (ZMod p) (𝓞 (SplitField f) ⧸ Q))).Splits := by
    rw [map_modp_eq, ← map_int_eq (A := 𝓞 (SplitField f)) (B := 𝓞 (SplitField f) ⧸ Q)]
    exact hsplO.map _
  let g : (ZMod p)[X] := f.map (Int.castRingHom (ZMod p))
  let ι : g.SplittingField →ₐ[ZMod p] (𝓞 (SplitField f) ⧸ Q) := SplittingField.lift g hsplk
  have hιinj : Function.Injective ι := ι.toRingHom.injective
  have himg : ι '' g.rootSet g.SplittingField = g.rootSet (𝓞 (SplitField f) ⧸ Q) :=
    Splits.image_rootSet (SplittingField.splits g) ι
  have hlift : ∀ b : 𝓞 (SplitField f) ⧸ Q, aeval b g = 0 →
      ∃ z : 𝓞 (SplitField f), aeval (R := ℤ) z f = 0 ∧ Ideal.Quotient.mk Q z = b := by
    intro b hb
    have h0 : eval b ((f.map (algebraMap ℤ (𝓞 (SplitField f)))).map (Ideal.Quotient.mk Q)) = 0 := by
      have := map_int_eq (A := 𝓞 (SplitField f)) (B := 𝓞 (SplitField f) ⧸ Q) f
      rw [show Ideal.Quotient.mk Q = algebraMap (𝓞 (SplitField f)) (𝓞 (SplitField f) ⧸ Q) from rfl,
        this, eval_map_algebraMap, ← aeval_modp p f b]
      exact hb
    have hprod := hsplO.eq_prod_roots_of_monic (hf.map (algebraMap ℤ (𝓞 (SplitField f))))
    rw [hprod, Polynomial.map_multiset_prod, eval_multiset_prod, Multiset.map_map,
      Multiset.prod_eq_zero_iff, Multiset.mem_map] at h0
    obtain ⟨c, hc, hc0⟩ := h0
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hc
    refine ⟨z, ?_, ?_⟩
    · have hne := (hf.map (algebraMap ℤ (𝓞 (SplitField f)))).ne_zero
      rw [mem_roots hne, IsRoot, eval_map, ← aeval_def] at hz
      exact hz
    · simp only [Function.comp, Polynomial.map_sub, map_X, map_C, eval_sub, eval_X, eval_C] at hc0
      exact (sub_eq_zero.mp hc0).symm
  let R : (ratPoly f).rootSet (SplitField f) → g.rootSet g.SplittingField → Prop :=
    fun a y => ∃ z : 𝓞 (SplitField f), (z : SplitField f) = a.1 ∧
      Ideal.Quotient.mk Q z = ι y.1
  have hg0 : g ≠ 0 := (hf.map _).ne_zero
  have hp0 : ratPoly f ≠ 0 := (hf.map _).ne_zero
  refine parts_eq_of_rel R ?_ ?_ ?_ ?_ _ _ ?_
  · rintro a y y' ⟨z, hz, hzy⟩ ⟨z', hz', hzy'⟩
    have : z = z' := Subtype.ext (hz.trans hz'.symm)
    subst this
    exact Subtype.ext (hιinj (hzy.symm.trans hzy'))
  · intro a
    have ha := (mem_rootSet.mp a.2).2
    rw [aeval_ratPoly] at ha
    have hint := isIntegral_of_aeval f hf a.1 ha
    let z : 𝓞 (SplitField f) := ⟨a.1, hint⟩
    have hz : aeval (R := ℤ) z f = 0 := by
      refine FaithfulSMul.algebraMap_injective (𝓞 (SplitField f)) (SplitField f) ?_
      rw [map_zero]
      exact (coe_aeval f z).trans ha
    have hmem : Ideal.Quotient.mk Q z ∈ g.rootSet (𝓞 (SplitField f) ⧸ Q) := by
      rw [mem_rootSet]
      refine ⟨hg0, ?_⟩
      rw [aeval_modp, aeval_ringHom, hz, map_zero]
    rw [← himg] at hmem
    obtain ⟨y, hy, hyz⟩ := hmem
    exact ⟨⟨y, hy⟩, z, rfl, hyz.symm⟩
  · intro y
    have hmem : ι y.1 ∈ g.rootSet (𝓞 (SplitField f) ⧸ Q) := by
      rw [← himg]; exact ⟨y.1, y.2, rfl⟩
    have hy0 := (mem_rootSet.mp hmem).2
    obtain ⟨z, hz, hzy⟩ := hlift _ hy0
    refine ⟨⟨(z : SplitField f), ?_⟩, z, rfl, hzy⟩
    rw [mem_rootSet]
    refine ⟨hp0, ?_⟩
    rw [aeval_ratPoly, ← coe_aeval, hz]
    rfl
  · have h1 := card_rootSet_eq_natDegree hsepK (SplittingField.splits (ratPoly f))
    have h2 := card_rootSet_eq_natDegree hsepg (SplittingField.splits g)
    have h3 : g.natDegree = (ratPoly f).natDegree := by
      rw [hf.natDegree_map]
      exact (hf.natDegree_map (Int.castRingHom ℚ)).symm
    exact h1.trans (h3.symm.trans h2.symm)
  · rintro a y ⟨z, hz, hzy⟩
    refine ⟨MulSemiringAction.toAlgHom ℤ (𝓞 (SplitField f)) σ z, ?_, ?_⟩
    · show σ (z : SplitField f) = σ a.1
      rw [hz]
    · have h1 := AlgHom.IsArithFrobAt.mk_apply hF z
      rw [hcard] at h1
      have h2 : ((MulAction.toPermHom g.Gal (g.rootSet g.SplittingField)
          (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) g.SplittingField) y :
          g.rootSet g.SplittingField) : g.SplittingField) = y.1 ^ p := by
        show FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) g.SplittingField y.1 = y.1 ^ p
        rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card]
      rw [h2, map_pow, ← hzy, h1]

theorem solution (f : ℤ[X]) (hf : f.Monic) (hdisc : f.discr ≠ 0)
    (p : ℕ) [Fact p.Prime] (hpd : ¬ (p : ℤ) ∣ f.discr) (σ : GalGroup f)
    (hσ : IsFrobeniusAt f p σ) :
    cyclePattern f σ = decompositionType f p := by
  have hsepK : (ratPoly f).Separable :=
    separable_map_of_discr (Int.castRingHom ℚ) f hf (by simpa using hdisc)
  have hsepg : (f.map (Int.castRingHom (ZMod p))).Separable :=
    separable_map_of_discr (Int.castRingHom (ZMod p)) f hf (by
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hpd)
  rw [core f hf p hsepK hsepg σ hσ,
    frobeniusCyclePattern_eq_factorDegrees p _ hsepg.squarefree]
  rfl
