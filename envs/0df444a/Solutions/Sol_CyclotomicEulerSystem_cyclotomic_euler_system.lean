-- Prove2me | solution 1 for CyclotomicEulerSystem.cyclotomic_euler_system
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:34:47.850442+00:00
-- url     : https://prove2.me/submissions/7fd88e5e-0105-4471-9309-1eed6b0b890a

import Definitions.Def_CyclotomicEulerSystem_defs

open Polynomial IntermediateField
open CyclotomicEulerSystem

private lemma relative_irreducible (ζ : ℕ → ℂ) (hζ : IsCompatibleRootSystem ζ)
    (n l : ℕ) (hn : Squarefree n) (hl : l.Prime) (hln : ¬l ∣ n) :
    Irreducible (cyclotomic l (cycField ζ n)) := by
  classical
  let K := cycField ζ n
  let L := IntermediateField.adjoin K {ζ l}
  have hn0 : n ≠ 0 := hn.ne_zero
  let : NeZero n := ⟨hn0⟩
  let : NeZero l := ⟨hl.ne_zero⟩
  have hnζ := hζ.1 n hn
  have hlζ := hζ.1 l hl.squarefree
  let : IsCyclotomicExtension {n} ℚ K :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin n ℚ ℂ K hnζ).2 rfl
  let : FiniteDimensional ℚ K := IsCyclotomicExtension.finiteDimensional {n} ℚ K
  have hi : IsIntegral K (ζ l) := (hlζ.isIntegral hl.pos).tower_top
  let : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hi
  let : FiniteDimensional ℚ L := FiniteDimensional.trans ℚ K L
  have hnL : IsPrimitiveRoot (algebraMap K L (zetaIn ζ n)) n :=
    (IsPrimitiveRoot.coe_submonoidClass_iff.mp hnζ).map_of_injective
      (algebraMap K L).injective
  have hlL : IsPrimitiveRoot (IntermediateField.AdjoinSimple.gen K (ζ l)) l :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp hlζ
  have hcop : n.Coprime l := ((hl.coprime_iff_not_dvd).2 hln).symm
  have hd := hnL.lcm_totient_le_finrank (K := ℚ) hlL
    (cyclotomic.irreducible_rat (Nat.lcm_pos (Nat.pos_of_ne_zero hn0) hl.pos))
  rw [hcop.lcm_eq_mul, Nat.totient_mul hcop,
    ← Module.finrank_mul_finrank ℚ K L,
    IsCyclotomicExtension.finrank K (cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hn0)),
    IntermediateField.adjoin.finrank hi] at hd
  have hdeg : l.totient ≤ (minpoly K (ζ l)).natDegree :=
    le_of_mul_le_mul_left hd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn0))
  have hz : aeval (ζ l) (cyclotomic l K) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hlζ.isRoot_cyclotomic hl.pos
  have heq : cyclotomic l K = minpoly K (ζ l) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi) (cyclotomic.monic l K)
      (minpoly.dvd K (ζ l) hz) (by simpa only [natDegree_cyclotomic] using hdeg)
  rw [heq]
  exact minpoly.irreducible hi

private lemma product_identity (a z : ℂ) (l : ℕ) (hl : l.Prime)
    (hz : IsPrimitiveRoot z l) (ha : a ≠ 1) :
    (∏ r ∈ primitiveRoots l ℂ, (1 - a * r)) = (1 - a ^ l) / (1 - a) := by
  classical
  have h := IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul (x := (1 : ℂ)) (y := a) hl.pos hz
  rw [one_pow, nthRootsFinset_eq_of_prime hl] at h
  have h1 : (1 : ℂ) ∉ primitiveRoots l ℂ := by
    intro hm
    exact ((mem_primitiveRoots hl.pos).mp hm).ne_one hl.one_lt rfl
  rw [Finset.prod_union (Finset.disjoint_singleton_right.mpr h1), Finset.prod_singleton,
    one_mul] at h
  have h' : 1 - a ^ l = (∏ r ∈ primitiveRoots l ℂ, (1 - a * r)) * (1 - a) := by
    simpa only [mul_comm a] using h
  exact (eq_div_iff (sub_ne_zero.mpr (Ne.symm ha))).2 h'.symm

private theorem norm_result (ζ : ℕ → ℂ) (hζ : IsCompatibleRootSystem ζ) (n l : ℕ)
    (hn : Squarefree n) (hn1 : 1 < n) (hl : l.Prime) (hln : ¬ l ∣ n)
    (Frob : cycField ζ n ≃ₐ[ℚ] cycField ζ n) (hFrob : Frob (zetaIn ζ n) = zetaIn ζ n ^ l) :
    ((Algebra.norm (cycField ζ n) (alphaExt ζ n (n * l)) : cycField ζ n) : ℂ) =
      (Frob (alphaIn ζ n) : ℂ) / alpha ζ n := by
  classical
  let K := cycField ζ n
  let L := IntermediateField.adjoin K {ζ l}
  have hnζ := hζ.1 n hn
  have hlζ := hζ.1 l hl.squarefree
  have hcop : n.Coprime l := ((hl.coprime_iff_not_dvd).2 hln).symm
  have hmul := hζ.2 n l hn hl.squarefree hcop
  have hnz : ζ n ≠ 0 := hnζ.ne_zero (by omega)
  have hL : cycExt ζ n (n * l) = L := by
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro _ rfl
      rw [hmul]
      exact mul_mem (L.algebraMap_mem (zetaIn ζ n))
        (IntermediateField.subset_adjoin K {ζ l} rfl)
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro _ rfl
      have h : ζ l = ζ (n*l) / ζ n := by rw [hmul, mul_div_cancel_left₀ _ hnz]
      rw [h]
      exact div_mem (IntermediateField.subset_adjoin K {ζ (n*l)} rfl)
        ((cycExt ζ n (n*l)).algebraMap_mem (zetaIn ζ n))
  let e := IntermediateField.equivOfEq hL
  let a : L := 1 - algebraMap K L (zetaIn ζ n) * IntermediateField.AdjoinSimple.gen K (ζ l)
  have hea : e (alphaExt ζ n (n*l)) = a := by
    apply Subtype.ext
    change 1 - ζ (n*l) = 1 - ζ n * ζ l
    rw [hmul]
  have hnorm : Algebra.norm K (alphaExt ζ n (n*l)) = Algebra.norm K a := by
    rw [← hea, Algebra.norm_eq_of_algEquiv e]
  let : NeZero l := ⟨hl.ne_zero⟩
  let : IsCyclotomicExtension {l} K L :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin l K ℂ L hlζ).2 rfl
  let : FiniteDimensional K L := IsCyclotomicExtension.finiteDimensional {l} K L
  have hzL : IsPrimitiveRoot (IntermediateField.AdjoinSimple.gen K (ζ l)) l :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp hlζ
  have hirr := relative_irreducible ζ hζ n l hn hl hln
  let E := hzL.embeddingsEquivPrimitiveRoots ℂ hirr
  have hprod : (Algebra.norm K a : ℂ) =
      ∏ r ∈ primitiveRoots l ℂ, (1 - ζ n * r) := by
    change algebraMap K ℂ (Algebra.norm K a) = _
    rw [Algebra.norm_eq_prod_embeddings K ℂ a]
    rw [← Finset.prod_coe_sort (primitiveRoots l ℂ)]
    apply Fintype.prod_equiv E
    intro σ
    simp only [a, map_sub, map_one, map_mul]
    have hs : σ (algebraMap K L (zetaIn ζ n)) = ζ n := σ.commutes (zetaIn ζ n)
    rw [hs]
    rfl
  change (Algebra.norm K (alphaExt ζ n (n*l)) : ℂ) = _
  rw [hnorm, hprod, product_identity (ζ n) (ζ l) l hl hlζ (hnζ.ne_one hn1)]
  have hAlpha : alphaIn ζ n = 1 - zetaIn ζ n := rfl
  rw [hAlpha, map_sub, map_one, hFrob]
  rfl

open NumberField

private theorem congruence_result (ζ : ℕ → ℂ) (hζ : IsCompatibleRootSystem ζ) (n l : ℕ)
    (hn : Squarefree n) (hl : l.Prime) (hln : ¬ l ∣ n)
    (P : Ideal (𝓞 (cycField ζ (n * l)))) (hP : P.IsPrime)
    (hlP : (l : 𝓞 (cycField ζ (n * l))) ∈ P)
    (x y : 𝓞 (cycField ζ (n * l)))
    (hx : ((x : cycField ζ (n * l)) : ℂ) = alpha ζ (n * l))
    (hy : ((y : cycField ζ (n * l)) : ℂ) = alpha ζ n) :
    x - y ∈ P := by
  let K := cycField ζ (n * l)
  let f : 𝓞 K →+* ℂ := (algebraMap K ℂ).comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := (algebraMap K ℂ).injective.comp
    RingOfIntegers.coe_injective
  have hcompat := hζ.2 n l hn hl.squarefree (hl.coprime_iff_not_dvd.mpr hln).symm
  have hroot := (hζ.1 l hl.squarefree).pow_eq_one
  have hpow : (1 - x) ^ l = (1 - y) ^ l := by
    apply hf
    simp only [map_pow, map_sub, map_one, f, RingHom.comp_apply,
      show algebraMap K ℂ (algebraMap (𝓞 K) K x) = alpha ζ (n * l) from hx,
      show algebraMap K ℂ (algebraMap (𝓞 K) K y) = alpha ζ n from hy,
      alpha, sub_sub_cancel, hcompat, mul_pow, hroot, mul_one]
  let : P.IsPrime := hP
  let : Fact l.Prime := ⟨hl⟩
  have hz : (l : (𝓞 K) ⧸ P) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hlP)
  let : CharP ((𝓞 K) ⧸ P) l := (CharP.charP_iff_prime_eq_zero hl).mpr hz
  have hq := congrArg (Ideal.Quotient.mk P) hpow
  simp only [map_pow, map_sub, map_one, sub_pow_char] at hq
  have hxy : (Ideal.Quotient.mk P x - Ideal.Quotient.mk P y) ^ l = 0 := by
    rw [sub_pow_char]
    linear_combination -hq
  have heq : Ideal.Quotient.mk P x - Ideal.Quotient.mk P y = 0 :=
    eq_zero_of_pow_eq_zero hxy
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_sub] using heq)

theorem solution (ζ : ℕ → ℂ) (hζ : IsCompatibleRootSystem ζ) (n l : ℕ)
    (hn : Squarefree n) (hl : l.Prime) (hln : ¬ l ∣ n) :
    (1 < n → ∀ Frob : cycField ζ n ≃ₐ[ℚ] cycField ζ n, Frob (zetaIn ζ n) = zetaIn ζ n ^ l →
      ((Algebra.norm (cycField ζ n) (alphaExt ζ n (n * l)) : cycField ζ n) : ℂ) =
        (Frob (alphaIn ζ n) : ℂ) / alpha ζ n) ∧
    (∀ P : Ideal (𝓞 (cycField ζ (n * l))), P.IsPrime →
      (l : 𝓞 (cycField ζ (n * l))) ∈ P →
      ∀ x y : 𝓞 (cycField ζ (n * l)),
        ((x : cycField ζ (n * l)) : ℂ) = alpha ζ (n * l) →
        ((y : cycField ζ (n * l)) : ℂ) = alpha ζ n → x - y ∈ P) := by
  constructor
  · intro hn1 Frob hFrob
    exact norm_result ζ hζ n l hn hn1 hl hln Frob hFrob
  · intro P hP hlP x y hx hy
    exact congruence_result ζ hζ n l hn hl hln P hP hlP x y hx hy
