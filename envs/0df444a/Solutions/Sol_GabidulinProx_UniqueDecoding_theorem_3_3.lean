-- Prove2me | solution 1 for GabidulinProx.UniqueDecoding.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:41:35.695093+00:00
-- url     : https://prove2.me/submissions/3047ea36-9ee3-4dd9-ae1b-d50511ab4e82

import Mathlib
import Definitions.Def_GabidulinProx_UniqueDecoding_Codes
import Definitions.Def_GabidulinProx_UniqueDecoding_Reconstruction
import Theorems.Thm_GabidulinProx_UniqueDecoding_lemma_2_2
import Theorems.Thm_GabidulinProx_UniqueDecoding_lemma_3_4
import Theorems.Thm_GabidulinProx_UniqueDecoding_lemma_3_6
import Theorems.Thm_GabidulinProx_UniqueDecoding_lemma_3_7

section
set_option autoImplicit false
open scoped BigOperators

namespace GabidulinProx.Dev.T33

open GabidulinProx.UniqueDecoding

section rank

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

lemma span_range_comp {n : ℕ} (χ : M →ₗ[K] N) (w : Fin n → M) :
    Submodule.span K (Set.range (fun r => χ (w r))) =
      Submodule.map χ (Submodule.span K (Set.range w)) := by
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

lemma wordRank_map_le {n : ℕ} (χ : M →ₗ[K] N) (w : Fin n → M) :
    wordRank K (fun r => χ (w r)) ≤ wordRank K w := by
  have : Module.Finite K (Submodule.span K (Set.range w)) :=
    Module.Finite.span_of_finite K (Set.finite_range w)
  unfold wordRank
  rw [span_range_comp]
  exact Submodule.finrank_map_le _ _

end rank

section dist

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Fintype L] {n : ℕ}

lemma exists_of_codeDistance_le (C : Submodule L (Fin n → L)) (v : Fin n → L) (e : ℕ)
    (h : codeDistance K C v ≤ e) : ∃ c ∈ C, wordRank K (v - c) ≤ e := by
  classical
  unfold codeDistance at h
  letI : Fintype C := Fintype.ofFinite C
  obtain ⟨c, _, hc⟩ := Finset.mem_image.1 (Finset.min'_mem
    (Finset.univ.image (fun c : C => wordRank K (v - c.val)))
    (Finset.image_nonempty.mpr Finset.univ_nonempty))
  exact ⟨c.val, c.2, by rw [hc]; exact h⟩

lemma codeDistance_le_of_mem (C : Submodule L (Fin n → L)) (v c : Fin n → L) (hc : c ∈ C) :
    codeDistance K C v ≤ wordRank K (v - c) := by
  classical
  unfold codeDistance
  letI : Fintype C := Fintype.ofFinite C
  apply Finset.min'_le
  rw [Finset.mem_image]
  exact ⟨⟨c, hc⟩, Finset.mem_univ _, rfl⟩

lemma pairDistance_le_of_mem (C : Submodule L (Fin n → L)) (u₀ u₁ c₀ c₁ : Fin n → L)
    (h₀ : c₀ ∈ C) (h₁ : c₁ ∈ C) :
    pairDistance K C u₀ u₁ ≤ pairRank K (u₀ - c₀) (u₁ - c₁) := by
  classical
  unfold pairDistance
  letI : Fintype C := Fintype.ofFinite C
  apply Finset.min'_le
  rw [Finset.mem_image]
  exact ⟨(⟨c₀, h₀⟩, ⟨c₁, h₁⟩), Finset.mem_univ _, rfl⟩

end dist

section lin

lemma eval_linearized {R : Type*} [CommSemiring R] (q : ℕ) {m : ℕ} (c : Fin m → R) (x : R) :
    (linearized q c).eval x = ∑ i, c i * x ^ (q ^ i.val) := by
  simp [linearized, Polynomial.eval_finsetSum]

lemma coeff_linearized {R : Type*} [CommSemiring R] (q : ℕ) (hq : 2 ≤ q) {m : ℕ}
    (c : Fin m → R) (j : Fin m) : (linearized q c).coeff (q ^ j.val) = c j := by
  simp only [linearized, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [if_neg]
    intro h
    exact hij (Fin.ext (Nat.pow_right_injective hq h))
  · intro h; exact absurd (Finset.mem_univ _) h

lemma two_le_card (K : Type*) [Field K] [Fintype K] : 2 ≤ Fintype.card K :=
  Fintype.one_lt_card

lemma exists_linear {K L : Type*} [Field K] [Fintype K] [Field L] [Algebra K L] {m : ℕ}
    (c : Fin m → L) :
    ∃ φ : L →ₗ[K] L, ∀ x, (linearized (Fintype.card K) c).eval x = φ x := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hadd : ∀ (x y : L) (i : ℕ), (x + y) ^ (Fintype.card K ^ i) =
      x ^ (Fintype.card K ^ i) + y ^ (Fintype.card K ^ i) := by
    intro x y i
    have : Fintype.card K ^ i = p ^ ((n : ℕ) * i) := by rw [hn, pow_mul]
    rw [this]
    exact add_pow_char_pow x y p _
  have hsmul : ∀ (a : K) (x : L) (i : ℕ), (a • x) ^ (Fintype.card K ^ i) =
      a • x ^ (Fintype.card K ^ i) := by
    intro a x i
    rw [Algebra.smul_def, mul_pow, ← map_pow, FiniteField.pow_card_pow, Algebra.smul_def]
  refine ⟨{ toFun := fun x => ∑ i, c i * x ^ (Fintype.card K ^ i.val)
            map_add' := ?_
            map_smul' := ?_ }, fun x => eval_linearized _ _ _⟩
  · intro x y
    simp only [hadd, mul_add, Finset.sum_add_distrib]
  · intro a x
    simp only [hsmul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm]

end lin

section ptform

open Polynomial in
lemma pt_eq {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L] {k : ℕ}
    (hk : 1 ≤ k) (x : Fin k → L) (hx : LinearIndependent K x)
    (pt : Fin k → Polynomial L) (A : Polynomial L) (F₀ F₁ : Fin k → L) (c₀ c₁ : Fin k → L)
    (h : ∀ i, familyEval (Fintype.card K) pt (x i) =
      A * (C (F₀ i) + X * C (F₁ i)))
    (h₀ : ∀ i, (linearized (Fintype.card K) c₀).eval (x i) = F₀ i)
    (h₁ : ∀ i, (linearized (Fintype.card K) c₁).eval (x i) = F₁ i) :
    ∀ j, pt j = A * (C (c₀ j) + X * C (c₁ j)) := by
  set q := Fintype.card K with hq
  have hq2 : 2 ≤ q := two_le_card K
  let T := RatFunc L
  let φ : L[X] →+* T := algebraMap L[X] T
  have hC : ∀ a : L, φ (C a) = algebraMap L T a := fun a =>
    (IsScalarTower.algebraMap_apply L L[X] T a).symm
  let Zt : T := φ X
  let g : Fin k → T := fun j => φ (pt j)
  let g' : Fin k → T := fun j => φ A * (algebraMap L T (c₀ j) + Zt * algebraMap L T (c₁ j))
  have hG : IsLinearized q k (linearized q g) := ⟨g, rfl⟩
  have hH : IsLinearized q k (linearized q g') := ⟨g', rfl⟩
  have hxT : ∀ i, algebraMap L T (x i) = algebraMap L T (x i) := fun _ => rfl
  have e1 : ∀ i, (linearized q g).eval (algebraMap L T (x i)) =
      φ A * (algebraMap L T (F₀ i) + Zt * algebraMap L T (F₁ i)) := by
    intro i
    have := congrArg φ (h i)
    rw [map_mul, map_add, map_mul, hC, hC] at this
    rw [← this, eval_linearized]
    unfold familyEval
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hC, map_pow]
  have e2 : ∀ i, (linearized q g').eval (algebraMap L T (x i)) =
      φ A * (algebraMap L T (F₀ i) + Zt * algebraMap L T (F₁ i)) := by
    intro i
    rw [eval_linearized, ← h₀ i, ← h₁ i, eval_linearized, eval_linearized]
    simp only [g', map_sum, map_mul, map_pow, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨f, _, huniq⟩ := lemma_2_2 (K := K) (L := L) (T := T) (n := k) hk x hx
    (fun i => (linearized q g).eval (algebraMap L T (x i)))
  have := (huniq _ ⟨hG, fun r => rfl⟩).trans (huniq _ ⟨hH, fun r => (e2 r).trans (e1 r).symm⟩).symm
  intro j
  have hcoef := congrArg (fun f => f.coeff (q ^ j.val)) this
  simp only [coeff_linearized q hq2] at hcoef
  apply RatFunc.algebraMap_injective L
  show φ (pt j) = φ _
  rw [map_mul, map_add, map_mul, hC, hC]
  exact hcoef

end ptform

section conclude

lemma conclude {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    {n k e : ℕ} (hdec : 2 * e < n - k + 1) (α : Fin n → L) (hα : LinearIndependent K α)
    (u₀ u₁ : Fin n → L) (f₀ f₁ : Polynomial L)
    (hf₀ : IsLinearized (Fintype.card K) n f₀) (hf₁ : IsLinearized (Fintype.card K) n f₁)
    (hu₀ : ∀ r, f₀.eval (α r) = u₀ r) (hu₁ : ∀ r, f₁.eval (α r) = u₁ r)
    (c₀ c₁ : Fin k → L) (E : Submodule K L)
    (hEV : E ≤ Submodule.span K (Set.range α)) (hE : Module.finrank K E = n - e)
    (hEeq₀ : ∀ x ∈ E, (linearized (Fintype.card K) c₀).eval x = f₀.eval x)
    (hEeq₁ : ∀ x ∈ E, (linearized (Fintype.card K) c₁).eval x = f₁.eval x) :
    pairDistance K (gabidulin K α k) u₀ u₁ ≤ e ∧
      ∀ z : L, codeDistance K (gabidulin K α k) (linePoint u₀ u₁ z) ≤ e := by
  obtain ⟨d₀, rfl⟩ := hf₀
  obtain ⟨d₁, rfl⟩ := hf₁
  obtain ⟨φ₀, hφ₀⟩ := exists_linear (K := K) d₀
  obtain ⟨φ₁, hφ₁⟩ := exists_linear (K := K) d₁
  obtain ⟨ψ₀, hψ₀⟩ := exists_linear (K := K) c₀
  obtain ⟨ψ₁, hψ₁⟩ := exists_linear (K := K) c₁
  let Ψ : L →ₗ[K] L × L := (φ₀ - ψ₀).prod (φ₁ - ψ₁)
  let w₀ : Fin n → L := evaluateWord α (linearized (Fintype.card K) c₀)
  let w₁ : Fin n → L := evaluateWord α (linearized (Fintype.card K) c₁)
  have hw₀ : w₀ ∈ gabidulin K α k := ⟨c₀, by
    funext r; simp [gabidulinEncoder, w₀, evaluateWord, eval_linearized]⟩
  have hw₁ : w₁ ∈ gabidulin K α k := ⟨c₁, by
    funext r; simp [gabidulinEncoder, w₁, evaluateWord, eval_linearized]⟩
  have hword : (fun r => ((u₀ - w₀) r, (u₁ - w₁) r)) = fun r => Ψ (α r) := by
    funext r
    simp only [Pi.sub_apply, Ψ, LinearMap.prod_apply, Function.prod_apply, LinearMap.sub_apply, w₀, w₁,
      evaluateWord, ← hu₀, ← hu₁, hφ₀, hφ₁, hψ₀, hψ₁]
  have hpair : pairRank K (u₀ - w₀) (u₁ - w₁) ≤ e := by
    unfold pairRank
    rw [hword]
    unfold wordRank
    rw [span_range_comp]
    set V := Submodule.span K (Set.range α)
    have : Module.Finite K V := Module.Finite.span_of_finite K (Set.finite_range α)
    have hV : Module.finrank K V = n := by
      rw [finrank_span_eq_card hα]; simp
    let R := Ψ.domRestrict V
    have hrk := LinearMap.finrank_range_add_finrank_ker R
    have hker : Submodule.comap V.subtype E ≤ LinearMap.ker R := by
      intro v hv
      rw [LinearMap.mem_ker]
      have hv' : (v : L) ∈ E := hv
      show Ψ v = 0
      simp only [Ψ, LinearMap.prod_apply, Function.prod_apply, LinearMap.sub_apply]
      rw [← hφ₀, ← hφ₁, ← hψ₀, ← hψ₁, hEeq₀ _ hv', hEeq₁ _ hv']
      simp
    have h1 : Module.finrank K E ≤ Module.finrank K (LinearMap.ker R) := by
      rw [← LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hEV)]
      exact Submodule.finrank_mono hker
    have h2 : LinearMap.range R = Submodule.map Ψ V := LinearMap.range_domRestrict _ _
    rw [h2] at hrk
    omega
  refine ⟨?_, fun z => ?_⟩
  · exact (pairDistance_le_of_mem _ u₀ u₁ w₀ w₁ hw₀ hw₁).trans hpair
  · have hmem : w₀ + z • w₁ ∈ gabidulin K α k := Submodule.add_mem _ hw₀ (Submodule.smul_mem _ _ hw₁)
    refine (codeDistance_le_of_mem _ _ _ hmem).trans ?_
    let χ : L × L →ₗ[K] L :=
      { toFun := fun p => p.1 + z * p.2
        map_add' := by intro a b; simp only [Prod.fst_add, Prod.snd_add]; ring
        map_smul' := by
          intro a p
          simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_add, mul_smul_comm] }
    have : (linePoint u₀ u₁ z - (w₀ + z • w₁)) = fun r => χ ((u₀ - w₀) r, (u₁ - w₁) r) := by
      funext r
      simp only [linePoint, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, χ,
        LinearMap.coe_mk, AddHom.coe_mk]
      ring
    rw [this]
    exact (wordRank_map_le χ _).trans hpair

end conclude

end GabidulinProx.Dev.T33

namespace GabidulinProx.UniqueDecoding

open GabidulinProx.Dev.T33 Polynomial

/-- Theorem 3.3, p.19, including its consequence for every point on the line. -/
theorem chk_theorem_3_3 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] {n k e : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (he : 1 ≤ e)
    (hdec : 2 * e < n - k + 1) (α : Fin n → L) (hα : LinearIndependent K α)
    (u₀ u₁ : Fin n → L)
    (hprob : uniformFraction (fun z => codeDistance K (gabidulin K α k) (linePoint u₀ u₁ z) ≤ e) >
      (tau (Fintype.card K) k e : ℝ) / (Fintype.card L : ℝ)) :
    pairDistance K (gabidulin K α k) u₀ u₁ ≤ e ∧
      ∀ z : L, codeDistance K (gabidulin K α k) (linePoint u₀ u₁ z) ≤ e := by
  classical
  have hn : 1 ≤ n := hk.trans hkn
  have hq2 : 2 ≤ Fintype.card K := two_le_card K
  set S := goodParameters K α k e u₀ u₁ with hSdef
  have hSτ : tau (Fintype.card K) k e < S.card := by
    have hL : (0 : ℝ) < Fintype.card L := Nat.cast_pos.2 Fintype.card_pos
    have h1 : uniformFraction (fun z => codeDistance K (gabidulin K α k)
        (linePoint u₀ u₁ z) ≤ e) = (S.card : ℝ) / (Fintype.card L : ℝ) := by
      unfold uniformFraction
      rw [hSdef]
      unfold goodParameters
      congr!
    rw [h1, gt_iff_lt, div_lt_div_iff_of_pos_right hL] at hprob
    exact_mod_cast hprob
  have hσ1 : 1 ≤ sigma (Fintype.card K) e := by
    unfold sigma
    calc 1 = (Fintype.card K) ^ 0 := by simp
      _ ≤ _ := Finset.single_le_sum (f := fun i => Fintype.card K ^ i)
        (fun i _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.succ_pos e))
  have htau : tau (Fintype.card K) k e =
      (sigma (Fintype.card K) e - 1) +
        sigma (Fintype.card K) e * clearingBound (Fintype.card K) k e := rfl
  have hcb : 1 ≤ clearingBound (Fintype.card K) k e := by
    unfold clearingBound; omega
  have hσS : sigma (Fintype.card K) e < S.card := by
    have : sigma (Fintype.card K) e ≤ sigma (Fintype.card K) e *
        clearingBound (Fintype.card K) k e := Nat.le_mul_of_pos_right _ hcb
    omega
  -- decoded family
  have hdecS : ∀ z ∈ S, ∃ P : Polynomial L, IsLinearized (Fintype.card K) k P ∧
      wordRank K (linePoint u₀ u₁ z - evaluateWord α P) ≤ e := by
    intro z hz
    have hz' : codeDistance K (gabidulin K α k) (linePoint u₀ u₁ z) ≤ e :=
      (Finset.mem_filter.1 hz).2
    obtain ⟨c, ⟨m, rfl⟩, hc⟩ := exists_of_codeDistance_le _ _ _ hz'
    refine ⟨linearized (Fintype.card K) m, ⟨m, rfl⟩, ?_⟩
    have : evaluateWord α (linearized (Fintype.card K) m) = gabidulinEncoder K α k m := by
      funext r; simp [gabidulinEncoder, evaluateWord, eval_linearized]
    rw [this]; exact hc
  choose! Pz hPz using hdecS
  have hDF : DecodedFamily K α u₀ u₁ k e S Pz := fun z hz => hPz z hz
  obtain ⟨a, b, hid, hb⟩ := lemma_3_4 hk hkn he hdec α hα u₀ u₁ hσS
  obtain ⟨pt, hptdeg, -, hptspec⟩ :=
    lemma_3_6 hk hkn he hdec α hα u₀ u₁ a b hid hb hσS Pz hDF
  have ha0 : a 0 ≠ 0 := hb.1
  have hdeg : (a 0).natDegree ≤ sigma (Fintype.card K) e - 1 := by
    have := hb.2.1 0
    simpa using this
  have hlarge : sigma (Fintype.card K) e * clearingBound (Fintype.card K) k e <
      (regularParameters S (a 0)).card := by
    have h1 := Finset.card_filter_add_card_filter_not (s := S) (fun z => (a 0).eval z ≠ 0)
    have h2 : (S.filter (fun z => ¬ ((a 0).eval z ≠ 0))).card ≤ (a 0).natDegree := by
      calc _ ≤ (a 0).roots.toFinset.card := by
            apply Finset.card_le_card
            intro z hz
            rw [Finset.mem_filter, not_not] at hz
            rw [Multiset.mem_toFinset, mem_roots ha0]
            exact hz.2
        _ ≤ (a 0).roots.card := Multiset.toFinset_card_le _
        _ ≤ _ := card_roots' _
    have h3 : (regularParameters S (a 0)).card = (S.filter (fun z => (a 0).eval z ≠ 0)).card := by
      unfold regularParameters
      congr
    rw [h3]
    omega
  obtain ⟨f₀, ⟨hf₀, hf₀e⟩, -⟩ := lemma_2_2 (K := K) (L := L) (T := L) (n := n) hn α hα u₀
  obtain ⟨f₁, ⟨hf₁, hf₁e⟩, -⟩ := lemma_2_2 (K := K) (L := L) (T := L) (n := n) hn α hα u₁
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hf₀e hf₁e
  obtain ⟨E, hEV, hEdim, hEfam⟩ := lemma_3_7 hk hkn he hdec α hα u₀ u₁ f₀ f₁ hf₀ hf₁ hf₀e hf₁e
    (a 0) hdeg Pz hDF pt hptdeg hptspec hlarge
  -- independent points in E
  have hkE : k ≤ Module.finrank K E := by omega
  let bE := Module.finBasis K E
  let xs : Fin k → E := fun i => bE (Fin.castLE hkE i)
  have hxs : LinearIndependent K xs :=
    bE.linearIndependent.comp _ (Fin.castLE_injective hkE)
  have hx : LinearIndependent K (fun i => (xs i : L)) :=
    hxs.map' E.subtype (Submodule.ker_subtype E)
  obtain ⟨P₀, ⟨hP₀, hP₀e⟩, -⟩ := lemma_2_2 (K := K) (L := L) (T := L) (n := k) hk
    (fun i => (xs i : L)) hx (fun i => f₀.eval (xs i : L))
  obtain ⟨P₁, ⟨hP₁, hP₁e⟩, -⟩ := lemma_2_2 (K := K) (L := L) (T := L) (n := k) hk
    (fun i => (xs i : L)) hx (fun i => f₁.eval (xs i : L))
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hP₀e hP₁e
  obtain ⟨c₀, rfl⟩ := hP₀
  obtain ⟨c₁, rfl⟩ := hP₁
  have hpt := pt_eq hk (fun i => (xs i : L)) hx pt
    (a 0 ^ sigma (Fintype.card K) (k - 1)) (fun i => f₀.eval (xs i : L))
    (fun i => f₁.eval (xs i : L)) c₀ c₁
    (fun i => hEfam _ (xs i).2) hP₀e hP₁e
  have hA : a 0 ^ sigma (Fintype.card K) (k - 1) ≠ 0 := pow_ne_zero _ ha0
  have key : ∀ x ∈ E,
      (linearized (Fintype.card K) c₀).eval x = f₀.eval x ∧
      (linearized (Fintype.card K) c₁).eval x = f₁.eval x := by
    intro x hxE
    have h1 := hEfam x hxE
    have h2 : familyEval (Fintype.card K) pt x =
        a 0 ^ sigma (Fintype.card K) (k - 1) *
          (C ((linearized (Fintype.card K) c₀).eval x) +
            X * C ((linearized (Fintype.card K) c₁).eval x)) := by
      unfold familyEval
      simp only [hpt, eval_linearized, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        map_mul, map_pow]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have h3 := mul_left_cancel₀ hA (h2.symm.trans h1)
    have c0 := congrArg (fun f => f.coeff 0) h3
    have c1 := congrArg (fun f => f.coeff 1) h3
    simp at c0 c1
    exact ⟨c0, c1⟩
  exact conclude hdec α hα u₀ u₁ f₀ f₁ hf₀ hf₁ hf₀e hf₁e c₀ c₁ E hEV hEdim
    (fun x hx => (key x hx).1) (fun x hx => (key x hx).2)

end GabidulinProx.UniqueDecoding
end

theorem solution : type_of% @GabidulinProx.UniqueDecoding.chk_theorem_3_3 := @GabidulinProx.UniqueDecoding.chk_theorem_3_3
