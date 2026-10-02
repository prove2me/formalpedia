-- Prove2me | solution 1 for ChebotarevDensity.frobenius_substitutions_form_conjClass
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T13:49:08.713767+00:00
-- url     : https://prove2.me/submissions/e3e4f9f1-6abe-4641-93f1-6848111783a8

import Definitions.Def_ChebotarevDensity_Defs

open Polynomial NumberField
open ChebotarevDensity
open scoped Pointwise

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

private lemma invariant (f : ℤ[X]) :
    Algebra.IsInvariant ℤ (𝓞 (SplitField f)) (GalGroup f) := by
  have hs : Polynomial.IsSplittingField ℚ (SplitField f) (ratPoly f) :=
    Polynomial.IsSplittingField.splittingField _
  have : Normal ℚ (SplitField f) := Normal.of_isSplittingField (ratPoly f)
  have : IsGalois ℚ (SplitField f) := {}
  have : IsGaloisGroup (GalGroup f) ℚ (SplitField f) := IsGaloisGroup.of_isGalois ℚ (SplitField f)
  exact (inferInstance : IsGaloisGroup (GalGroup f) ℤ (𝓞 (SplitField f))).isInvariant

private lemma exists_smul_eq (f : ℤ[X]) (Q Q' : Ideal (𝓞 (SplitField f))) [Q.IsPrime]
    [Q'.IsPrime] (h : Q.under ℤ = Q'.under ℤ) : ∃ τ : GalGroup f, Q' = τ • Q := by
  have := invariant f
  exact Algebra.IsInvariant.exists_smul_of_under_eq ℤ (𝓞 (SplitField f)) (GalGroup f) Q Q' h

private lemma exists_prime_over (f : ℤ[X]) (p : ℕ) (hp : p.Prime) :
    ∃ Q : Ideal (𝓞 (SplitField f)), Q.IsPrime ∧ (p : 𝓞 (SplitField f)) ∈ Q ∧
      Finite (𝓞 (SplitField f) ⧸ Q) := by
  have hP : (Ideal.span {(p : ℤ)}).IsMaximal := by
    have : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    exact PrincipalIdealRing.isMaximal_of_irreducible this.irreducible
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := 𝓞 (SplitField f)) (Ideal.span {(p : ℤ)}) ⊥
    (by rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp
      (FaithfulSMul.algebraMap_injective ℤ (𝓞 (SplitField f)))]; exact bot_le)
  have hpQ : (p : 𝓞 (SplitField f)) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 (SplitField f))) := by
      rw [hQP]; exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨Q, hQ, hpQ, ?_⟩
  refine Ideal.finiteQuotientOfFreeOfNeBot _ (fun h => ?_)
  rw [h] at hpQ
  simp only [Ideal.mem_bot] at hpQ
  exact hp.ne_zero (by exact_mod_cast hpQ)

private lemma splits_int (f : ℤ[X]) : (f.map (algebraMap ℤ (SplitField f))).Splits := by
  have h : ((ratPoly f).map (algebraMap ℚ (SplitField f))).Splits := SplittingField.splits _
  have e : (ratPoly f).map (algebraMap ℚ (SplitField f)) = f.map (algebraMap ℤ (SplitField f)) := by
    show (f.map (Int.castRingHom ℚ)).map (algebraMap ℚ (SplitField f)) = _
    rw [Polynomial.map_map]
    congr 1
  rw [← e]; exact h

private lemma inertia_trivial (f : ℤ[X]) (hf : f.Monic) (p : ℕ) (hp : p.Prime)
    (hpd : ¬ (p : ℤ) ∣ f.discr) (Q : Ideal (𝓞 (SplitField f))) [Q.IsPrime]
    (hpQ : (p : 𝓞 (SplitField f)) ∈ Q) (τ : GalGroup f) (hτ : τ ∈ Q.inertia (GalGroup f)) :
    τ = 1 := by
  apply Gal.ext
  intro x hx
  rw [mem_rootSet] at hx
  obtain ⟨-, hx⟩ := hx
  have hx' : aeval x f = 0 := by
    have h := aeval_map_algebraMap (R := ℤ) ℚ x f
    rw [← h]; exact hx
  have hint : IsIntegral ℤ x := ⟨f, hf, by
    rw [← aeval_def]; exact hx'⟩
  let α : 𝓞 (SplitField f) := ⟨x, hint⟩
  have hrootA : ∀ y : 𝓞 (SplitField f), aeval (y : SplitField f) f = 0 →
      (f.map (algebraMap ℤ (𝓞 (SplitField f)))).eval y = 0 := by
    intro y hy
    apply Subtype.ext
    have h0 : eval (y : SplitField f) (f.map (algebraMap ℤ (SplitField f))) = 0 := by
      rw [eval_map, ← aeval_def]; exact hy
    exact (eval_coe f y).symm.trans h0
  have hτx : aeval (τ x) f = 0 := by
    have := Polynomial.aeval_algHom_apply
      (((τ : SplitField f ≃ₐ[ℚ] SplitField f).restrictScalars ℤ).toAlgHom) x f
    rw [hx', map_zero] at this
    exact this
  by_contra hne
  have hne' : τ • α ≠ α := by
    intro h
    apply hne
    have := congrArg (fun y : 𝓞 (SplitField f) => (y : SplitField f)) h
    exact this
  have hmem : τ • α - α ∈ Q := hτ α
  have := disc_mem f hf (splits_int f) Q (τ • α) α (hrootA _ hτx) (hrootA _ hx') hne' hmem
  have hu := under_eq_span p hp Q hpQ
  have : (f.discr : ℤ) ∈ Q.under ℤ := by simpa [Ideal.under] using this
  rw [hu, Ideal.mem_span_singleton] at this
  exact hpd this

theorem solution (f : ℤ[X]) (hf : f.Monic) (hdisc : f.discr ≠ 0)
    (p : ℕ) (hp : p.Prime) (hpd : ¬ (p : ℤ) ∣ f.discr) :
    ∃ C : ConjClasses (GalGroup f), {σ : GalGroup f | IsFrobeniusAt f p σ} = C.carrier := by
  have := invariant f
  obtain ⟨Q0, hQ0, hpQ0, hfin⟩ := exists_prime_over f p hp
  obtain ⟨σ0, hσ0⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (GalGroup f) Q0
  refine ⟨ConjClasses.mk σ0, ?_⟩
  ext σ
  rw [Set.mem_ofPred_eq, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj,
    isConj_iff]
  constructor
  · rintro ⟨Q, hQ, hpQ, hF⟩
    obtain ⟨τ, hτ⟩ := exists_smul_eq f Q0 Q
      ((under_eq_span p hp Q0 hpQ0).trans (under_eq_span p hp Q hpQ).symm)
    have h1 : IsArithFrobAt ℤ (τ * σ0 * τ⁻¹) Q := hτ ▸ hσ0.conj τ
    have h3 := inertia_trivial f hf p hp hpd Q hpQ _ (hF.mul_inv_mem_inertia h1)
    have h4 : σ = τ * σ0 * τ⁻¹ := mul_inv_eq_one.mp h3
    refine ⟨τ⁻¹, ?_⟩
    rw [h4]; group
  · rintro ⟨c, hc⟩
    have h4 : σ = c⁻¹ * σ0 * c⁻¹⁻¹ := by
      rw [inv_inv, ← hc]; group
    refine ⟨c⁻¹ • Q0, hQ0.smul _, ?_, ?_⟩
    · rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
      rw [show c • (p : 𝓞 (SplitField f)) = (p : 𝓞 (SplitField f)) from
        map_natCast (MulSemiringAction.toRingHom (GalGroup f) (𝓞 (SplitField f)) c) p]
      exact hpQ0
    · rw [h4]; exact hσ0.conj c⁻¹

