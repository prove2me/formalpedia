-- Prove2me | solution 1 for ChebotarevDensity.chebotarev_density
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-17T21:06:20.607477+00:00
-- url     : https://prove2.me/submissions/e064bf50-8c09-4973-a12a-1dcc24cd587f

import Definitions.Def_ChebotarevDensity_Defs
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_FrobeniusPrimeSet
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_RamifiedPrimes
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NaturalDensity
import Theorems.Thm_NumberField_Chebotarev_hasNaturalDensity_frobeniusPrimeSet
import Theorems.Thm_ChebotarevDensity_hasDirichletDensity_of_hasNaturalDensity

set_option warn.classDefReducibility false
open Polynomial NumberField IsDedekindDomain
open scoped symmDiff

namespace ChebotarevBridge

/-! ### Instance plumbing (verified to compile) -/

noncomputable abbrev algGen {F : Type*} [Field F] (p : F[X]) : Algebra F p.SplittingField :=
  inferInstance

noncomputable abbrev algQ (f : ℤ[X]) : Algebra ℚ (ChebotarevDensity.SplitField f) :=
  algGen (ChebotarevDensity.ratPoly f)

theorem isGalois_gen {F : Type*} [Field F] [PerfectField F] (p : F[X]) :
    @IsGalois F _ p.SplittingField _ (algGen p) := by
  have : Normal F p.SplittingField := Normal.of_isSplittingField p
  have : Algebra.IsAlgebraic F p.SplittingField := Algebra.IsAlgebraic.of_finite F _
  have : Algebra.IsSeparable F p.SplittingField := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact ⟨⟩

theorem isGalois_splitField (f : ℤ[X]) :
    @IsGalois ℚ _ (ChebotarevDensity.SplitField f) _ (algQ f) :=
  isGalois_gen (ChebotarevDensity.ratPoly f)

/-! ### T0: rational primes as height-one primes of `𝓞 ℚ` -/

theorem A_prime_natCast (p : ℕ) (hp : p.Prime) : Prime (p : 𝓞 ℚ) := by
  have h := Nat.prime_iff_prime_int.mp hp
  rw [← MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ)]
  simpa using h

theorem A_natCast_ne_zero (p : ℕ) (hp : p.Prime) : (p : 𝓞 ℚ) ≠ 0 :=
  (A_prime_natCast p hp).ne_zero

/-- The height-one prime `(p)` of `𝓞 ℚ` for a rational prime `p`. -/
noncomputable def primeOfNat (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {(p : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (A_natCast_ne_zero p hp)).mpr (A_prime_natCast p hp)
  ne_bot := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact A_natCast_ne_zero p hp

theorem primeOfNat_asIdeal (p : ℕ) (hp : p.Prime) :
    (primeOfNat p hp).asIdeal = Ideal.span {(p : 𝓞 ℚ)} := rfl

theorem absNorm_primeOfNat (p : ℕ) (hp : p.Prime) :
    Ideal.absNorm (primeOfNat p hp).asIdeal = p := by
  rw [primeOfNat_asIdeal, Ideal.absNorm_span_singleton]
  have h : Module.finrank ℤ (𝓞 ℚ) = 1 := by
    rw [NumberField.RingOfIntegers.rank]; exact Module.finrank_self ℚ
  have : (p : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap, h]
  simp

theorem exists_primeOfNat (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ (p : ℕ) (hp : p.Prime), primeOfNat p hp = v := by
  refine ⟨(Rat.HeightOneSpectrum.primesEquiv v).1, (Rat.HeightOneSpectrum.primesEquiv v).2, ?_⟩
  have h := congrArg HeightOneSpectrum.asIdeal
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v)
  apply HeightOneSpectrum.ext
  refine Eq.trans ?_ h
  show Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ)} =
    Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm
      (Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ)})
  rw [Ideal.map_span]
  simp

theorem liesOver_primeOfNat_iff {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
    (Q : Ideal (𝓞 L)) [Q.IsPrime] (p : ℕ) (hp : p.Prime) :
    Q.LiesOver (primeOfNat p hp).asIdeal ↔ (p : 𝓞 L) ∈ Q := by
  rw [Ideal.liesOver_iff, primeOfNat_asIdeal]
  constructor
  · intro h
    have : (p : 𝓞 ℚ) ∈ Q.under (𝓞 ℚ) := h ▸ Ideal.subset_span rfl
    simpa [Ideal.mem_under] using this
  · intro h
    have hmax : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal := (primeOfNat p hp).isMaximal
    refine hmax.eq_of_le (Ideal.IsPrime.ne_top (inferInstance : (Q.under (𝓞 ℚ)).IsPrime)) ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_under]
    simpa using h

/-- The set of rational primes whose associated height-one prime lies in `S`. -/
def natSet (S : Set (HeightOneSpectrum (𝓞 ℚ))) : Set ℕ :=
  {p | ∃ hp : p.Prime, primeOfNat p hp ∈ S}

/-! ### T1: natural density transport -/

theorem A_primeOfNat_injective {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : primeOfNat p hp = primeOfNat q hq) : p = q := by
  have := congrArg (fun v : HeightOneSpectrum (𝓞 ℚ) => Ideal.absNorm v.asIdeal) h
  simpa [absNorm_primeOfNat] using this

open scoped Classical in
theorem A_primeCount_eq (T : Set (HeightOneSpectrum (𝓞 ℚ))) (x : ℕ) :
    TauCeti.primeCount ℚ T (x : ℝ) =
      (((Finset.Iic x).filter (fun p => p.Prime ∧ p ∈ natSet T)).card : ℝ) := by
  unfold TauCeti.primeCount TauCeti.primeSummatory TauCeti.summatory
  simp only [Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_boole]
  congr 1
  refine (Finset.card_bij (fun p hp => primeOfNat p (Finset.mem_filter.mp hp).2.1) ?_ ?_ ?_).symm
  · intro p hp
    have hp2 := Finset.mem_filter.mp hp
    have hpx := Finset.mem_Iic.mp hp2.1
    obtain ⟨-, hp', hT⟩ := hp2.2
    simp only [Finset.mem_filter, TauCeti.normLE, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    refine ⟨?_, hT⟩
    rw [absNorm_primeOfNat]
    exact_mod_cast hpx
  · intro p hp q hq h
    exact A_primeOfNat_injective _ _ h
  · intro v hv
    simp only [Finset.mem_filter, TauCeti.normLE, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq] at hv
    obtain ⟨p, hp, rfl⟩ := exists_primeOfNat v
    refine ⟨p, ?_, rfl⟩
    rw [absNorm_primeOfNat] at hv
    simp only [Finset.mem_filter, Finset.mem_Iic]
    exact ⟨by exact_mod_cast hv.1, hp, hp, hv.2⟩

open scoped Classical in
theorem hasNaturalDensity_natSet {S : Set (HeightOneSpectrum (𝓞 ℚ))} {δ : ℝ}
    (h : NumberField.Set.HasNaturalDensity S δ) :
    ChebotarevDensity.HasNaturalDensity (natSet S) δ := by
  unfold ChebotarevDensity.HasNaturalDensity
  have h' := h.comp tendsto_natCast_atTop_atTop
  refine h'.congr (fun x => ?_)
  simp only [Function.comp]
  rw [A_primeCount_eq S x, A_primeCount_eq Set.univ x]
  have hd : (Finset.Iic x).filter (fun p => p.Prime ∧ p ∈ natSet (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ)))) =
      (Finset.Iic x).filter Nat.Prime := by
    refine Finset.filter_congr fun p _ => ⟨fun hp => hp.1, fun hp => ⟨hp, hp, Set.mem_univ _⟩⟩
  rw [hd]


/-! ### T2: the two Frobenius prime sets agree up to finitely many primes -/

/-! #### Helpers for T2 -/

theorem B_card_int {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
    (Q : Ideal (𝓞 L)) [Q.IsPrime] (p : ℕ) (hp : p.Prime) (hQ : (p : 𝓞 L) ∈ Q) :
    Nat.card (ℤ ⧸ Q.under ℤ) = p := by
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).mpr hpr).isMaximal
      (by simpa using hpr.ne_zero)
  have hle : Ideal.span {(p : ℤ)} ≤ Q.under ℤ := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa using hQ
  have heq := hmax.eq_of_le Ideal.IsPrime.ne_top' hle
  rw [← heq, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv]
  have : NeZero p := ⟨hp.ne_zero⟩
  exact Nat.card_zmod p

theorem B_card_O {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
    (Q : Ideal (𝓞 L)) [Q.IsPrime] (p : ℕ) (hp : p.Prime) (hQ : (p : 𝓞 L) ∈ Q) :
    Nat.card (𝓞 ℚ ⧸ Q.under (𝓞 ℚ)) = p := by
  have : Q.LiesOver (primeOfNat p hp).asIdeal := (liesOver_primeOfNat_iff Q p hp).mpr hQ
  rw [← Ideal.LiesOver.over (p := (primeOfNat p hp).asIdeal) (P := Q)]
  have h := absNorm_primeOfNat p hp
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  exact h

theorem B_isArithFrobAt_iff {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
    {G : Type*} [Group G] [MulSemiringAction G (𝓞 L)] [SMulCommClass G ℤ (𝓞 L)]
    [SMulCommClass G (𝓞 ℚ) (𝓞 L)]
    (σ : G) (Q : Ideal (𝓞 L)) [Q.IsPrime] (p : ℕ) (hp : p.Prime) (hQ : (p : 𝓞 L) ∈ Q) :
    IsArithFrobAt ℤ σ Q ↔ IsArithFrobAt (𝓞 ℚ) σ Q := by
  unfold IsArithFrobAt AlgHom.IsArithFrobAt
  rw [B_card_int Q p hp hQ, B_card_O Q p hp hQ]
  rfl

theorem B_iff {L : Type*} [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    (C : ConjClasses (L ≃ₐ[ℚ] L)) (p : ℕ) (hp : p.Prime)
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (primeOfNat p hp).asIdeal],
      Algebra.IsUnramifiedAt (𝓞 ℚ) Q) :
    (∃ σ ∈ C.carrier, ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ (p : 𝓞 L) ∈ Q ∧ IsArithFrobAt ℤ σ Q) ↔
      primeOfNat p hp ∈ NumberField.Chebotarev.frobeniusPrimeSet ℚ L C := by
  constructor
  · rintro ⟨σ, hσ, Q, hQ, hpQ, hF⟩
    have : Q.IsPrime := hQ
    have : Q.LiesOver (primeOfNat p hp).asIdeal := (liesOver_primeOfNat_iff Q p hp).mpr hpQ
    have h2 := (B_isArithFrobAt_iff σ Q p hp hpQ).mp hF
    refine ⟨hur, ?_⟩
    rw [artinSymbol_eq_mk_of_isArithFrobAt _ hur Q σ h2]
    exact ConjClasses.mem_carrier_iff_mk_eq.mp hσ
  · rintro ⟨hur', h⟩
    obtain ⟨Q⟩ : Nonempty ((primeOfNat p hp).asIdeal.primesOver (𝓞 L)) := inferInstance
    have : Q.1.IsPrime := Q.2.1
    have : Q.1.LiesOver (primeOfNat p hp).asIdeal := Q.2.2
    have hne : Q.1 ≠ ⊥ :=
      Ideal.ne_bot_of_liesOver_of_ne_bot (primeOfNat p hp).ne_bot Q.1
    have : Q.1.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hne inferInstance
    have hσ := IsArithFrobAt.arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) Q.1
    have h1 := artinSymbol_eq_mk_of_isArithFrobAt _ hur' Q.1 _ hσ
    rw [h] at h1
    have hpQ : (p : 𝓞 L) ∈ Q.1 := (liesOver_primeOfNat_iff Q.1 p hp).mp ‹_›
    exact ⟨_, ConjClasses.mem_carrier_iff_mk_eq.mpr h1.symm, Q.1, inferInstance, hpQ,
      (B_isArithFrobAt_iff _ Q.1 p hp hpQ).mpr hσ⟩

theorem B_finite_dvd (d : ℤ) (hd : d ≠ 0) : {p : ℕ | (p : ℤ) ∣ d}.Finite :=
  (Set.finite_Iic d.natAbs).subset fun p hp =>
    Nat.le_of_dvd (Int.natAbs_pos.mpr hd) (Int.natCast_dvd.mp hp)

theorem B_finite_ram {L : Type*} [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L] :
    {p : ℕ | ∃ hp : p.Prime,
      primeOfNat p hp ∈ NumberField.Chebotarev.ramifiedPrimes ℚ L}.Finite := by
  refine ((NumberField.Chebotarev.ramifiedPrimes ℚ L).finite_toSet.image
    (fun v => Ideal.absNorm v.asIdeal)).subset ?_
  rintro p ⟨hp, h⟩
  exact ⟨_, h, absNorm_primeOfNat p hp⟩

theorem chebotarevSet_symmDiff_finite (f : ℤ[X]) (hdisc : f.discr ≠ 0)
    (C : ConjClasses (ChebotarevDensity.GalGroup f)) :
    (ChebotarevDensity.chebotarevSet f C ∆
      natSet (@NumberField.Chebotarev.frobeniusPrimeSet ℚ (ChebotarevDensity.SplitField f)
        _ _ _ _ (algQ f) (isGalois_splitField f) C)).Finite := by
  let _ := algQ f
  have := isGalois_splitField f
  refine ((B_finite_dvd _ hdisc).union
    (B_finite_ram (L := ChebotarevDensity.SplitField f))).subset ?_
  intro p hp
  by_contra hE
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists] at hE
  obtain ⟨hdvd, hram⟩ := hE
  have hmem : p ∈ ChebotarevDensity.chebotarevSet f C ↔
      p ∈ natSet (NumberField.Chebotarev.frobeniusPrimeSet ℚ
        (ChebotarevDensity.SplitField f) C) := by
    constructor
    · rintro ⟨hpr, -, h⟩
      refine ⟨hpr, ?_⟩
      have hn := hram hpr
      rw [NumberField.Chebotarev.mem_ramifiedPrimes_iff, not_not] at hn
      exact (B_iff C p hpr hn).mp h
    · rintro ⟨hpr, h⟩
      have hn := hram hpr
      rw [NumberField.Chebotarev.mem_ramifiedPrimes_iff, not_not] at hn
      exact ⟨hpr, hdvd, (B_iff C p hpr hn).mpr h⟩
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 (hmem.mp h1)
  · exact h2 (hmem.mpr h1)


/-! ### T3: natural density is insensitive to finite changes -/

open scoped Classical in
theorem C_card_filter_le {S T : Set ℕ} (hST : (S ∆ T).Finite) (x : ℕ) :
    (((Finset.Iic x).filter (fun p => p.Prime ∧ p ∈ T)).card : ℝ) ≤
      (((Finset.Iic x).filter (fun p => p.Prime ∧ p ∈ S)).card : ℝ) + hST.toFinset.card := by
  have hsub : (Finset.Iic x).filter (fun p => p.Prime ∧ p ∈ T) ⊆
      (Finset.Iic x).filter (fun p => p.Prime ∧ p ∈ S) ∪ hST.toFinset := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_union, Set.Finite.mem_toFinset,
      Set.mem_symmDiff] at hp ⊢
    by_cases hpS : p ∈ S
    · exact Or.inl ⟨hp.1, hp.2.1, hpS⟩
    · exact Or.inr (Or.inr ⟨hp.2.2, hpS⟩)
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  exact_mod_cast h1

open scoped Classical in
theorem C_card_filter_abs_le {S T : Set ℕ} (hST : (S ∆ T).Finite) (x : ℕ) :
    |(((Finset.Iic x).filter (fun p => p.Prime ∧ p ∈ T)).card : ℝ) -
      (((Finset.Iic x).filter (fun p => p.Prime ∧ p ∈ S)).card : ℝ)| ≤ hST.toFinset.card := by
  have h1 := C_card_filter_le hST x
  have hTS : (T ∆ S).Finite := by rwa [symmDiff_comm]
  have h2 := C_card_filter_le hTS x
  have e : hTS.toFinset = hST.toFinset := by
    ext p; simp [symmDiff_comm]
  rw [e] at h2
  rw [abs_le]; constructor <;> linarith

theorem C_tendsto_card_prime :
    Filter.Tendsto (fun x : ℕ => (((Finset.Iic x).filter Nat.Prime).card : ℝ))
      Filter.atTop Filter.atTop := by
  have h : ∀ x : ℕ, ((Finset.Iic x).filter Nat.Prime).card = Nat.primeCounting x := by
    intro x
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    congr 1
    ext p
    simp
  simp only [h]
  exact tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting

open scoped Classical in
theorem C_main {S T : Set ℕ} {δ : ℝ}
    (h : ChebotarevDensity.HasNaturalDensity S δ) (hST : (S ∆ T).Finite) :
    ChebotarevDensity.HasNaturalDensity T δ := by
  unfold ChebotarevDensity.HasNaturalDensity at h ⊢
  set k : ℝ := (hST.toFinset.card : ℝ) with hk
  set P : ℕ → ℝ := fun x => (((Finset.Iic x).filter Nat.Prime).card : ℝ) with hP
  have hPt : Filter.Tendsto P Filter.atTop Filter.atTop := C_tendsto_card_prime
  have hk0 : Filter.Tendsto (fun x => k / P x) Filter.atTop (nhds 0) :=
    hPt.const_div_atTop k
  have hdiff : Filter.Tendsto (fun x : ℕ =>
      ((((Finset.Iic x).filter (fun p => p.Prime ∧ p ∈ T)).card : ℝ) / P x) -
      ((((Finset.Iic x).filter (fun p => p.Prime ∧ p ∈ S)).card : ℝ) / P x))
      Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      ?_ hk0
    filter_upwards [hPt.eventually_gt_atTop 0] with x hx
    simp only [Function.comp_apply]
    rw [← sub_div, abs_div, abs_of_pos hx]
    exact div_le_div_of_nonneg_right (C_card_filter_abs_le hST x) hx.le
  have := h.add hdiff
  rw [add_zero] at this
  refine this.congr (fun x => ?_)
  ring

theorem hasNaturalDensity_of_finite_symmDiff {S T : Set ℕ} {δ : ℝ}
    (h : ChebotarevDensity.HasNaturalDensity S δ) (hST : (S ∆ T).Finite) :
    ChebotarevDensity.HasNaturalDensity T δ := C_main h hST

end ChebotarevBridge

theorem solution (f : ℤ[X]) (hf : f.Monic) (hdisc : f.discr ≠ 0)
    (C : ConjClasses (ChebotarevDensity.GalGroup f)) :
    ChebotarevDensity.HasDirichletDensity (ChebotarevDensity.chebotarevSet f C)
      ((Nat.card C.carrier : ℝ) / Nat.card (ChebotarevDensity.GalGroup f)) := by
  have h1 := @NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet ℚ
    (ChebotarevDensity.SplitField f) _ _ _ _ (ChebotarevBridge.algQ f)
    (ChebotarevBridge.isGalois_splitField f) C
  have h2 := ChebotarevBridge.hasNaturalDensity_natSet h1
  have h3 := ChebotarevBridge.hasNaturalDensity_of_finite_symmDiff h2
    (by rw [symmDiff_comm]; exact ChebotarevBridge.chebotarevSet_symmDiff_finite f hdisc C)
  exact ChebotarevDensity.hasDirichletDensity_of_hasNaturalDensity _ _ h3
