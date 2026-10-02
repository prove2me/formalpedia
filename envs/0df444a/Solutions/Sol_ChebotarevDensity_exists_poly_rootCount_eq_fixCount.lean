-- Prove2me | solution 1 for ChebotarevDensity.exists_poly_rootCount_eq_fixCount
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T14:28:09.894587+00:00
-- url     : https://prove2.me/submissions/b361eeef-2a16-41ea-951e-4adc6bae89aa

import Definitions.Def_ChebotarevDensity_Defs
import Definitions.Def_ChebotarevDensity_Aux

open Polynomial NumberField
open ChebotarevDensity

/-- if `α ≠ β` are roots of monic `f` in `𝓞 K` with `α - β ∈ Q`, then `f'(α) ∈ Q`. -/
private lemma deriv_mem {A : Type*} [CommRing A] [IsDomain A] (g : A[X])
    (Q : Ideal A) (α β : A) (hα : g.eval α = 0) (hβ : g.eval β = 0) (hne : α ≠ β)
    (hQ : α - β ∈ Q) : (derivative g).eval α ∈ Q := by
  have h1 : (X - C α) * (g /ₘ (X - C α)) = g := mul_divByMonic_eq_iff_isRoot.mpr hα
  set g1 := g /ₘ (X - C α) with hg1
  have hβ1 : g1.eval β = 0 := by
    have := congrArg (eval β) h1
    rw [hβ, eval_mul] at this
    simp only [eval_sub, eval_X, eval_C] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) (Ne.symm hne)
    · exact h
  have h2 : (X - C β) * (g1 /ₘ (X - C β)) = g1 := mul_divByMonic_eq_iff_isRoot.mpr hβ1
  have hd : derivative g = g1 + (X - C α) * derivative g1 := by
    conv_lhs => rw [← h1]
    rw [derivative_mul]
    simp
  rw [hd]
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
  rw [← h2]
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  exact Ideal.mul_mem_right _ _ hQ

private lemma eval_coe {K : Type*} [Field K] [NumberField K] (g : ℤ[X]) (x : 𝓞 K) :
    (g.map (algebraMap ℤ K)).eval (x : K) = ((g.map (algebraMap ℤ (𝓞 K))).eval x : 𝓞 K) := by
  rw [eval_map, eval_map, eval₂_eq_sum_range, eval₂_eq_sum_range]
  simp [map_sum]

private lemma disc_mem {K : Type*} [Field K] [NumberField K] (f : ℤ[X]) (hf : f.Monic)
    (hsplit : (f.map (algebraMap ℤ K)).Splits)
    (Q : Ideal (𝓞 K)) (α β : 𝓞 K) (hα : (f.map (algebraMap ℤ (𝓞 K))).eval α = 0)
    (hβ : (f.map (algebraMap ℤ (𝓞 K))).eval β = 0)
    (hne : α ≠ β) (hQ : α - β ∈ Q) : (f.discr : 𝓞 K) ∈ Q := by
  have hdeg : f.natDegree ≠ 0 := by
    intro h
    have := eq_one_of_monic_natDegree_zero hf h
    subst this
    simp at hα
  have hdeg' : 0 < f.degree := by
    rw [← natDegree_pos_iff_degree_pos]; omega
  have hder := deriv_mem (f.map (algebraMap ℤ (𝓞 K))) Q α β hα hβ hne hQ
  -- resultant relation in K
  have hres := resultant_deriv hdeg'
  have hfK : (f.map (algebraMap ℤ K)).Monic := hf.map _
  have hnat : (f.map (algebraMap ℤ K)).natDegree = f.natDegree := hf.natDegree_map _
  have key := resultant_eq_prod_eval (f.map (algebraMap ℤ K)) (derivative (f.map (algebraMap ℤ K)))
    (f.natDegree - 1) ((natDegree_derivative_le _).trans (by rw [hnat])) hsplit
  rw [hnat, hfK.leadingCoeff, one_pow, one_mul] at key
  have e1 : resultant (f.map (algebraMap ℤ K)) (derivative (f.map (algebraMap ℤ K)))
      f.natDegree (f.natDegree - 1) =
      algebraMap ℤ K ((-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff * f.discr) := by
    rw [← hres, derivative_map, resultant_map_map]
  rw [e1, hf.leadingCoeff] at key
  simp only [mul_one, map_mul, map_pow, map_neg, map_one] at key
  -- split the product
  have hαK : (f.map (algebraMap ℤ K)).eval (α : K) = 0 := by
    rw [eval_coe, hα]; rfl
  have hmem : (α : K) ∈ (f.map (algebraMap ℤ K)).roots := by
    rw [mem_roots hfK.ne_zero]; exact hαK
  obtain ⟨R₀, hR₀⟩ := Multiset.exists_cons_of_mem hmem
  rw [hR₀, Multiset.map_cons, Multiset.prod_cons] at key
  have hrest : (R₀.map fun x => eval x (derivative (f.map (algebraMap ℤ K)))).prod ∈
      integralClosure ℤ K := by
    apply multiset_prod_mem
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
    have hxr : x ∈ (f.map (algebraMap ℤ K)).roots := by rw [hR₀]; exact Multiset.mem_cons_of_mem hx
    rw [mem_roots hfK.ne_zero] at hxr
    have hxint : IsIntegral ℤ x := by
      refine ⟨f, hf, ?_⟩
      have h := hxr
      rw [IsRoot, eval_map] at h
      exact h
    have : eval x (derivative (f.map (algebraMap ℤ K))) =
        (((derivative f).map (algebraMap ℤ (𝓞 K))).eval ⟨x, hxint⟩ : 𝓞 K) := by
      simp only [derivative_map]
      exact eval_coe (derivative f) ⟨x, hxint⟩
    rw [this]
    exact (((derivative f).map (algebraMap ℤ (𝓞 K))).eval ⟨x, hxint⟩ : 𝓞 K).2
  have hd2 : eval (α : K) (derivative (f.map (algebraMap ℤ K))) =
      ((((derivative f).map (algebraMap ℤ (𝓞 K))).eval α : 𝓞 K) : K) := by
    simp only [derivative_map]
    exact eval_coe (derivative f) α
  have hE : ((-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * (f.discr : 𝓞 K) : 𝓞 K) =
      (((derivative f).map (algebraMap ℤ (𝓞 K))).eval α) * ⟨_, hrest⟩ := by
    apply Subtype.ext
    rw [hd2] at key
    refine Eq.trans ?_ (Eq.trans key ?_)
    · rfl
    · rfl
  have hQ' : ((-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * (f.discr : 𝓞 K) : 𝓞 K) ∈ Q := by
    rw [hE]; rw [derivative_map] at hder; exact Ideal.mul_mem_right _ _ hder
  rcases neg_one_pow_eq_or (𝓞 K) (f.natDegree * (f.natDegree - 1) / 2) with h | h
  · rw [h, one_mul] at hQ'; exact hQ'
  · rw [h, neg_one_mul] at hQ'; simpa using hQ'

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


private lemma aeval_modp {A : Type*} [CommRing A] (p : ℕ) [Algebra (ZMod p) A] (f : ℤ[X]) (x : A) :
    aeval x (f.map (Int.castRingHom (ZMod p))) = aeval (R := ℤ) x f := by
  have : f.map (Int.castRingHom (ZMod p)) = f.map (algebraMap ℤ (ZMod p)) := by simp
  rw [this, aeval_map_algebraMap]


private lemma isIntegral_of_aeval {A : Type*} [CommRing A] (f : ℤ[X]) (hf : f.Monic) (x : A)
    (h : aeval (R := ℤ) x f = 0) : IsIntegral ℤ x :=
  ⟨f, hf, by simpa [aeval_def] using h⟩

private lemma map_int_eq {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (f : ℤ[X]) :
    (f.map (algebraMap ℤ A)).map (algebraMap A B) = f.map (algebraMap ℤ B) := by
  rw [Polynomial.map_map]
  congr 1
  exact Subsingleton.elim _ _

private lemma coe_aeval {K : Type*} [Field K] [NumberField K] (f : ℤ[X]) (z : 𝓞 K) :
    ((aeval (R := ℤ) z f : 𝓞 K) : K) = aeval (R := ℤ) (z : K) f :=
  (aeval_algHom_apply (IsScalarTower.toAlgHom ℤ (𝓞 K) K) z f).symm

private lemma aeval_ringHom {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (x : A)
    (f : ℤ[X]) : aeval (R := ℤ) (φ x) f = φ (aeval (R := ℤ) x f) :=
  aeval_algHom_apply φ.toIntAlgHom x f


private lemma splits_ringOfIntegers' {K : Type*} [Field K] [NumberField K] (g : ℤ[X]) (hg : g.Monic)
    (hK : (g.map (algebraMap ℤ K)).Splits) :
    (g.map (algebraMap ℤ (𝓞 K))).Splits := by
  refine Splits.of_splits_map_of_injective (i := algebraMap (𝓞 K) K)
    (FaithfulSMul.algebraMap_injective _ _) ?_ ?_
  · rw [map_int_eq]; exact hK
  · intro a ha
    have hne : (g.map (algebraMap ℤ (𝓞 K))).map (algebraMap (𝓞 K) K) ≠ 0 := by
      rw [map_int_eq]
      exact (hg.map _).ne_zero
    rw [mem_roots hne, IsRoot, map_int_eq] at ha
    have : aeval (R := ℤ) a g = 0 := by
      rw [aeval_def, ← eval_map]; exact ha
    exact ⟨⟨a, isIntegral_of_aeval g hg a this⟩, rfl⟩

private lemma eval_map_aeval {K : Type*} [Field K] [NumberField K] (g : ℤ[X]) (z : 𝓞 K) :
    (g.map (algebraMap ℤ (𝓞 K))).eval z = aeval (R := ℤ) z g := by
  rw [eval_map, aeval_def]

private lemma mem_range_of_pow_eq {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) k]
    (b : k) (hb : b ^ p = b) : ∃ x : ZMod p, algebraMap (ZMod p) k x = b := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq k hp1
  have hne := FiniteField.X_pow_card_sub_X_ne_zero k hp1
  have hinj : Function.Injective (algebraMap (ZMod p) k) := (algebraMap (ZMod p) k).injective
  classical
  let S : Finset k := (Finset.univ : Finset (ZMod p)).image (algebraMap (ZMod p) k)
  have hS : S.card = p := by
    rw [Finset.card_image_of_injective _ hinj]; simp
  have hsub : S ⊆ (X ^ p - X : k[X]).roots.toFinset := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    rw [Multiset.mem_toFinset, mem_roots hne]
    simp [IsRoot, ← map_pow, ZMod.pow_card]
  have hle : (X ^ p - X : k[X]).roots.toFinset.card ≤ S.card := by
    rw [hS]
    calc _ ≤ Multiset.card (X ^ p - X : k[X]).roots := Multiset.toFinset_card_le _
      _ ≤ _ := (card_roots' _).trans hdeg.le
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hb' : b ∈ (X ^ p - X : k[X]).roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hne]
    simp [IsRoot, hb]
  rw [← heq] at hb'
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hb'
  exact ⟨x, hx⟩

private lemma discr_ne_zero_of_irred (g : ℤ[X]) (hg : g.Monic)
    (hirr : Irreducible (g.map (Int.castRingHom ℚ))) : g.discr ≠ 0 := by
  have hsep : (g.map (Int.castRingHom ℚ)).Separable := hirr.separable
  have h0 : g.natDegree ≠ 0 := by
    intro h; rw [eq_one_of_monic_natDegree_zero hg h] at hirr; simp at hirr
  have hpos : 0 < g.degree := by rw [← natDegree_pos_iff_degree_pos]; omega
  intro hd
  have hres := resultant_deriv hpos
  rw [hd, mul_zero] at hres
  have h1 := congrArg (Int.castRingHom ℚ) hres
  rw [← resultant_map_map, map_zero, ← derivative_map] at h1
  have e1 : (g.map (Int.castRingHom ℚ)).natDegree = g.natDegree := hg.natDegree_map _
  have e2 : (derivative (g.map (Int.castRingHom ℚ))).natDegree = g.natDegree - 1 := by
    rw [natDegree_derivative, e1]
  have : (g.map (Int.castRingHom ℚ)).resultant (derivative (g.map (Int.castRingHom ℚ))) = 0 := by
    unfold resultant; rw [e1, e2]; exact h1
  rw [resultant_eq_zero_iff] at this
  exact this.2 hsep

private lemma fix_of_primitive {K : Type*} [Field K] [Algebra ℚ K] (E : IntermediateField ℚ K) (α : E)
    (hα : IntermediateField.adjoin ℚ {α} = ⊤) (x : K ≃ₐ[ℚ] K) (hx : x (α : K) = α) :
    ∀ e ∈ E, x e = e := by
  intro e he
  have h : (⟨e, he⟩ : E) ∈ IntermediateField.adjoin ℚ {α} := by rw [hα]; trivial
  have key : ∀ (e' : E), e' ∈ IntermediateField.adjoin ℚ {α} → x (e' : K) = e' := by
    intro e' he'
    induction he' using IntermediateField.adjoin_induction with
    | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact hx
    | algebraMap q => simp
    | add a b _ _ ha hb => simp [map_add, ha, hb]
    | inv a _ ha => simp [ha]
    | mul a b _ _ ha hb => simp [map_mul, ha, hb]
  exact key ⟨e, he⟩ h

private lemma exists_beta (f : ℤ[X]) (H : Subgroup (GalGroup f)) :
    ∃ β : SplitField f, IsIntegral ℤ β ∧ ∀ x : GalGroup f, x β = β ↔ x ∈ H := by
  have hs : Polynomial.IsSplittingField ℚ (SplitField f) (ratPoly f) :=
    Polynomial.IsSplittingField.splittingField _
  have : Normal ℚ (SplitField f) := Normal.of_isSplittingField (ratPoly f)
  have : IsGalois ℚ (SplitField f) := {}
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ (IntermediateField.fixedField H)
  have halg : IsAlgebraic ℤ (α : SplitField f) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ _).mpr (.of_finite ℚ _)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  refine ⟨y • (α : SplitField f), hyint, fun x => ?_⟩
  have h1 : x (y • (α : SplitField f)) = y • (α : SplitField f) ↔ x (α : SplitField f) = α := by
    rw [map_zsmul]
    exact (smul_right_injective (SplitField f) hy0).eq_iff
  rw [h1]
  constructor
  · intro hx
    rw [← IntermediateField.fixingSubgroup_fixedField H]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr (fix_of_primitive _ α hα x hx)
  · intro hx
    exact (IntermediateField.mem_fixedField_iff H _).mp α.2 x hx

private lemma splits_g (f : ℤ[X]) (g : ℤ[X]) (β : SplitField f)
    (hg : g.Monic) (hgβ : aeval (R := ℤ) β g = 0)
    (hirr : Irreducible (g.map (Int.castRingHom ℚ))) :
    (g.map (algebraMap ℤ (SplitField f))).Splits := by
  have hs : Polynomial.IsSplittingField ℚ (SplitField f) (ratPoly f) :=
    Polynomial.IsSplittingField.splittingField _
  have : Normal ℚ (SplitField f) := Normal.of_isSplittingField (ratPoly f)
  have hroot : aeval β (g.map (Int.castRingHom ℚ)) = 0 := by
    rw [show g.map (Int.castRingHom ℚ) = g.map (algebraMap ℤ ℚ) from rfl, aeval_map_algebraMap]
    exact hgβ
  have h1 := minpoly.eq_of_irreducible_of_monic hirr hroot (hg.map _)
  have h2 := Normal.splits (F := ℚ) (inferInstance : Normal ℚ (SplitField f)) β
  rw [← h1] at h2
  rwa [Polynomial.map_map, show (algebraMap ℚ (SplitField f)).comp (Int.castRingHom ℚ) =
    algebraMap ℤ (SplitField f) from RingHom.ext_int _ _] at h2

private lemma orbit_roots (f : ℤ[X]) (g : ℤ[X]) (β : SplitField f)
    (hg : g.Monic) (hgβ : aeval (R := ℤ) β g = 0)
    (hirr : Irreducible (g.map (Int.castRingHom ℚ))) (z : SplitField f)
    (hz : aeval (R := ℤ) z g = 0) : ∃ x : GalGroup f, x β = z := by
  have hs : Polynomial.IsSplittingField ℚ (SplitField f) (ratPoly f) :=
    Polynomial.IsSplittingField.splittingField _
  have : Normal ℚ (SplitField f) := Normal.of_isSplittingField (ratPoly f)
  have hroot : ∀ y : SplitField f, aeval (R := ℤ) y g = 0 → aeval y (g.map (Int.castRingHom ℚ)) = 0 := by
    intro y hy
    rw [show g.map (Int.castRingHom ℚ) = g.map (algebraMap ℤ ℚ) from rfl, aeval_map_algebraMap]
    exact hy
  have h1 := minpoly.eq_of_irreducible_of_monic hirr (hroot β hgβ) (hg.map _)
  have h2 := minpoly.eq_of_irreducible_of_monic hirr (hroot z hz) (hg.map _)
  have h3 : minpoly ℚ z = minpoly ℚ β := h2.symm.trans h1
  obtain ⟨x, hx⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := SplitField f)).mp h3
  exact ⟨x, hx⟩

private lemma smul_root (f : ℤ[X]) (g : ℤ[X]) (x : GalGroup f) (z : 𝓞 (SplitField f))
    (hz : aeval (R := ℤ) z g = 0) : aeval (R := ℤ) (x • z) g = 0 := by
  have := aeval_algHom_apply (MulSemiringAction.toAlgHom ℤ (𝓞 (SplitField f)) x) z g
  rw [hz, map_zero] at this
  exact this

open scoped Classical in
private lemma fixCount_eq (f : ℤ[X]) (g : ℤ[X])
    (H : Subgroup (GalGroup f)) (β : 𝓞 (SplitField f))
    (hgβ : aeval (R := ℤ) β g = 0)
    (hβ : ∀ x : GalGroup f, x • β = β ↔ x ∈ H)
    (horb : ∀ z : 𝓞 (SplitField f), aeval (R := ℤ) z g = 0 → ∃ x : GalGroup f, x • β = z)
    (σ : GalGroup f) :
    fixCount H σ = Nat.card {u : {z : 𝓞 (SplitField f) // aeval (R := ℤ) z g = 0} //
      σ • u.1 = u.1} := by
  have hact := smul_root f g
  let e0 : GalGroup f → {z : 𝓞 (SplitField f) // aeval (R := ℤ) z g = 0} :=
    fun x => ⟨x • β, hact x β hgβ⟩
  have he0 : ∀ x y : GalGroup f, x⁻¹ * y ∈ H → e0 x = e0 y := by
    intro x y hxy
    apply Subtype.ext
    show x • β = y • β
    have : (x⁻¹ * y) • β = β := (hβ _).mpr hxy
    rw [mul_smul, inv_smul_eq_iff] at this
    exact this.symm
  let e : GalGroup f ⧸ H → {z : 𝓞 (SplitField f) // aeval (R := ℤ) z g = 0} :=
    Quotient.lift e0 (fun x y hxy => he0 x y (QuotientGroup.leftRel_apply.mp hxy))
  have he : Function.Bijective e := by
    constructor
    · intro q q'
      induction q using QuotientGroup.induction_on with | _ x => ?_
      induction q' using QuotientGroup.induction_on with | _ y => ?_
      intro h
      have h' : x • β = y • β := congrArg Subtype.val h
      rw [QuotientGroup.eq]
      apply (hβ _).mp
      rw [mul_smul, inv_smul_eq_iff]
      exact h'.symm
    · rintro ⟨z, hz⟩
      obtain ⟨x, hx⟩ := horb z hz
      exact ⟨(x : GalGroup f ⧸ H), Subtype.ext hx⟩
  have hcompat : ∀ q : GalGroup f ⧸ H, (e (σ • q)).1 = σ • (e q).1 := by
    intro q
    induction q using QuotientGroup.induction_on with | _ x => ?_
    show (σ * x) • β = σ • (x • β)
    rw [mul_smul]
  unfold fixCount
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective e he) ?_)
  intro q
  show σ • q = q ↔ σ • (e q).1 = (e q).1
  rw [← hcompat]
  constructor
  · intro h; rw [h]
  · intro h; exact he.1 (Subtype.ext h)

private lemma count_core {O k : Type*} [CommRing O] [Field k] (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) k] (g : ℤ[X]) (mk : O →+* k) (σ : O → O)
    (hact : ∀ z : O, aeval (R := ℤ) z g = 0 → aeval (R := ℤ) (σ z) g = 0)
    (hA : ∀ z z' : O, aeval (R := ℤ) z g = 0 → aeval (R := ℤ) z' g = 0 → mk z = mk z' → z = z')
    (hB : ∀ b : k, aeval (R := ℤ) b g = 0 → ∃ z : O, aeval (R := ℤ) z g = 0 ∧ mk z = b)
    (hFrob : ∀ z : O, mk (σ z) = mk z ^ p) :
    Nat.card {x : ZMod p // (g.map (Int.castRingHom (ZMod p))).IsRoot x} =
      Nat.card {u : {z : O // aeval (R := ℤ) z g = 0} // σ u.1 = u.1} := by
  let T := {x : ZMod p // (g.map (Int.castRingHom (ZMod p))).IsRoot x}
  let U := {u : {z : O // aeval (R := ℤ) z g = 0} // σ u.1 = u.1}
  let φT : T → k := fun x => algebraMap (ZMod p) _ x.1
  let φU : U → k := fun u => mk u.1.1
  have hφT : Function.Injective φT := by
    intro x y h
    exact Subtype.ext ((algebraMap (ZMod p) k).injective h)
  have hφU : Function.Injective φU := by
    intro u v h
    exact Subtype.ext (Subtype.ext (hA _ _ u.1.2 v.1.2 h))
  have hroot_iff : ∀ x : ZMod p, (g.map (Int.castRingHom (ZMod p))).IsRoot x ↔
      aeval (R := ℤ) (algebraMap (ZMod p) k x) g = 0 := by
    intro x
    rw [← aeval_modp p g, aeval_algebraMap_apply, IsRoot.def,
      map_eq_zero_iff _ (algebraMap (ZMod p) k).injective]
    simp
  have hrange : Set.range φT = Set.range φU := by
    ext b
    constructor
    · rintro ⟨x, rfl⟩
      have hx := (hroot_iff x.1).mp x.2
      obtain ⟨z, hz, hzb⟩ := hB _ hx
      have hσz : σ z = z := by
        refine hA _ _ (hact z hz) hz ?_
        rw [hFrob, hzb, ← map_pow, ZMod.pow_card]
      exact ⟨⟨⟨z, hz⟩, hσz⟩, hzb⟩
    · rintro ⟨u, rfl⟩
      have hb : aeval (R := ℤ) (mk u.1.1) g = 0 := by
        rw [aeval_ringHom mk, u.1.2, map_zero]
      have hpow : mk u.1.1 ^ p = mk u.1.1 := by
        rw [← hFrob, u.2]
      obtain ⟨x, hx⟩ := mem_range_of_pow_eq p _ hpow
      refine ⟨⟨x, (hroot_iff x).mpr (hx ▸ hb)⟩, hx⟩
  show Nat.card T = Nat.card U
  rw [← Nat.card_range_of_injective hφT, ← Nat.card_range_of_injective hφU, hrange]

private lemma rootCount_eq (f : ℤ[X]) (g : ℤ[X]) (hg : g.Monic)
    (hgK : (g.map (algebraMap ℤ (SplitField f))).Splits)
    (p : ℕ) (hp : p.Prime) (hpd : ¬ (p : ℤ) ∣ g.discr) (σ : GalGroup f)
    (hσ : IsFrobeniusAt f p σ) :
    rootCount g p = Nat.card {u : {z : 𝓞 (SplitField f) // aeval (R := ℤ) z g = 0} //
      σ • u.1 = u.1} := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ, hpQ, hF⟩ := hσ
  have hunder := under_eq_span p hp Q hpQ
  have hcard : Nat.card (ℤ ⧸ Q.under ℤ) = p := by
    rw [hunder]
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv]
    exact Nat.card_zmod p
  have hQmax : Q.IsMaximal := by
    refine Ideal.IsPrime.isMaximal hQ ?_
    rintro rfl
    have : (p : 𝓞 (SplitField f)) = 0 := by simpa using hpQ
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) this
  let : Field (𝓞 (SplitField f) ⧸ Q) := Ideal.Quotient.field Q
  have hpk : ((p : ℕ) : 𝓞 (SplitField f) ⧸ Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpQ
  have : CharP (𝓞 (SplitField f) ⧸ Q) p := (CharP.charP_iff_prime_eq_zero hp).mpr hpk
  let : Algebra (ZMod p) (𝓞 (SplitField f) ⧸ Q) := ZMod.algebra _ p
  have hsplO := splits_ringOfIntegers' g hg hgK
  -- injectivity of reduction on roots
  have hA : ∀ z z' : 𝓞 (SplitField f), aeval (R := ℤ) z g = 0 → aeval (R := ℤ) z' g = 0 →
      Ideal.Quotient.mk Q z = Ideal.Quotient.mk Q z' → z = z' := by
    intro z z' hz hz' hzz
    by_contra hne
    have hmem : z - z' ∈ Q := Ideal.Quotient.eq.mp hzz
    have := disc_mem g hg hgK Q z z' (by rw [eval_map_aeval]; exact hz)
      (by rw [eval_map_aeval]; exact hz') hne hmem
    have : (g.discr : ℤ) ∈ Q.under ℤ := by simpa [Ideal.under] using this
    rw [hunder, Ideal.mem_span_singleton] at this
    exact hpd this
  -- lifting roots
  have hB : ∀ b : 𝓞 (SplitField f) ⧸ Q, aeval (R := ℤ) b g = 0 →
      ∃ z : 𝓞 (SplitField f), aeval (R := ℤ) z g = 0 ∧ Ideal.Quotient.mk Q z = b := by
    intro b hb
    have h0 : eval b ((g.map (algebraMap ℤ (𝓞 (SplitField f)))).map (Ideal.Quotient.mk Q)) = 0 := by
      have := map_int_eq (A := 𝓞 (SplitField f)) (B := 𝓞 (SplitField f) ⧸ Q) g
      rw [show Ideal.Quotient.mk Q = algebraMap (𝓞 (SplitField f)) (𝓞 (SplitField f) ⧸ Q) from rfl,
        this, eval_map_algebraMap]
      exact hb
    have hprod := hsplO.eq_prod_roots_of_monic (hg.map (algebraMap ℤ (𝓞 (SplitField f))))
    rw [hprod, Polynomial.map_multiset_prod, eval_multiset_prod, Multiset.map_map,
      Multiset.prod_eq_zero_iff, Multiset.mem_map] at h0
    obtain ⟨c, hc, hc0⟩ := h0
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hc
    refine ⟨z, ?_, ?_⟩
    · have hne := (hg.map (algebraMap ℤ (𝓞 (SplitField f)))).ne_zero
      rw [mem_roots hne, IsRoot, eval_map, ← aeval_def] at hz
      exact hz
    · simp only [Function.comp, Polynomial.map_sub, map_X, map_C, eval_sub, eval_X, eval_C] at hc0
      exact (sub_eq_zero.mp hc0).symm
  have hFrob : ∀ z : 𝓞 (SplitField f), Ideal.Quotient.mk Q (σ • z) = Ideal.Quotient.mk Q z ^ p := by
    intro z
    have h1 := AlgHom.IsArithFrobAt.mk_apply hF z
    rw [hcard] at h1
    exact h1
  exact count_core p g (Ideal.Quotient.mk Q) (fun z => σ • z) (smul_root f g σ) hA hB hFrob

theorem solution (f : ℤ[X]) (hf : f.Monic) (hdisc : f.discr ≠ 0)
    (H : Subgroup (GalGroup f)) :
    ∃ (g : ℤ[X]) (N : Finset ℕ), g.Monic ∧ Irreducible (g.map (Int.castRingHom ℚ)) ∧
      ∀ p : ℕ, p.Prime → p ∉ N → ∀ σ : GalGroup f, IsFrobeniusAt f p σ →
        rootCount g p = fixCount H σ := by
  obtain ⟨β, hβint, hβ⟩ := exists_beta f H
  have hg : (minpoly ℤ β).Monic := minpoly.monic hβint
  have hgβ : aeval (R := ℤ) β (minpoly ℤ β) = 0 := minpoly.aeval ℤ β
  have hirr : Irreducible ((minpoly ℤ β).map (Int.castRingHom ℚ)) := by
    have h1 := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hβint
    have h2 : Irreducible (minpoly ℚ β) := minpoly.irreducible (hβint.tower_top)
    rw [h1] at h2
    exact h2
  have hD := discr_ne_zero_of_irred _ hg hirr
  refine ⟨minpoly ℤ β, (minpoly ℤ β).discr.natAbs.primeFactors, hg, hirr, ?_⟩
  intro p hp hpN σ hσ
  have hpd : ¬ (p : ℤ) ∣ (minpoly ℤ β).discr := by
    intro h
    apply hpN
    rw [Nat.mem_primeFactors]
    exact ⟨hp, Int.natCast_dvd.mp h, Int.natAbs_ne_zero.mpr hD⟩
  let β' : 𝓞 (SplitField f) := ⟨β, hβint⟩
  have hgβ' : aeval (R := ℤ) β' (minpoly ℤ β) = 0 := by
    refine FaithfulSMul.algebraMap_injective (𝓞 (SplitField f)) (SplitField f) ?_
    rw [map_zero]
    exact (coe_aeval _ β').trans hgβ
  have hβ' : ∀ x : GalGroup f, x • β' = β' ↔ x ∈ H := by
    intro x
    rw [← hβ x]
    constructor
    · intro h
      have := congrArg (fun y : 𝓞 (SplitField f) => (y : SplitField f)) h
      exact this
    · intro h
      exact Subtype.ext h
  have horb : ∀ z : 𝓞 (SplitField f), aeval (R := ℤ) z (minpoly ℤ β) = 0 →
      ∃ x : GalGroup f, x • β' = z := by
    intro z hz
    have hz' : aeval (R := ℤ) (z : SplitField f) (minpoly ℤ β) = 0 := by
      exact (coe_aeval _ z).symm.trans (by rw [hz]; rfl)
    obtain ⟨x, hx⟩ := orbit_roots f (minpoly ℤ β) β hg hgβ hirr z hz'
    exact ⟨x, Subtype.ext hx⟩
  exact (rootCount_eq f _ hg (splits_g f _ β hg hgβ hirr) p hp hpd σ hσ).trans
    (fixCount_eq f _ H β' hgβ' hβ' horb σ).symm
