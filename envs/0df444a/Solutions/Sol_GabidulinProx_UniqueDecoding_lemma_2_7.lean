-- Prove2me | solution 1 for GabidulinProx.UniqueDecoding.lemma_2_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:41:32.877224+00:00
-- url     : https://prove2.me/submissions/0d95077d-4047-4a7a-a3bc-b1d1d1fe0a50

import Mathlib
import Definitions.Def_GabidulinProx_UniqueDecoding_Reconstruction

section
set_option autoImplicit false

open scoped BigOperators
open Polynomial GabidulinProx.UniqueDecoding

namespace GabidulinProx.Dev.Rec

section Supp

variable {L : Type*} [Field L]

/-- Support of `f` lies among the exponents `q^i`, `i < m`. -/
def SuppIn (q m : ℕ) (f : L[X]) : Prop := ∀ n, f.coeff n ≠ 0 → ∃ i < m, n = q ^ i

lemma suppIn_zero (q m : ℕ) : SuppIn q m (0 : L[X]) := by
  intro n h; simp at h

lemma suppIn_add {q m : ℕ} {f g : L[X]} (hf : SuppIn q m f) (hg : SuppIn q m g) :
    SuppIn q m (f + g) := by
  intro n h
  rw [coeff_add] at h
  by_cases h1 : f.coeff n = 0
  · rw [h1, zero_add] at h; exact hg n h
  · exact hf n h1

lemma suppIn_neg {q m : ℕ} {f : L[X]} (hf : SuppIn q m f) : SuppIn q m (-f) := by
  intro n h
  rw [coeff_neg] at h
  exact hf n (fun h0 => h (by rw [h0, neg_zero]))

lemma suppIn_sub {q m : ℕ} {f g : L[X]} (hf : SuppIn q m f) (hg : SuppIn q m g) :
    SuppIn q m (f - g) := by
  rw [sub_eq_add_neg]; exact suppIn_add hf (suppIn_neg hg)

lemma suppIn_Cmul {q m : ℕ} (a : L) {f : L[X]} (hf : SuppIn q m f) :
    SuppIn q m (C a * f) := by
  intro n h
  rw [coeff_C_mul] at h
  exact hf n (fun h0 => h (by rw [h0, mul_zero]))

lemma suppIn_mono {q m m' : ℕ} (h : m ≤ m') {f : L[X]} (hf : SuppIn q m f) :
    SuppIn q m' f := by
  intro n hn
  obtain ⟨i, hi, e⟩ := hf n hn
  exact ⟨i, lt_of_lt_of_le hi h, e⟩

lemma suppIn_sum {q m : ℕ} {ι : Type*} (s : Finset ι) (f : ι → L[X])
    (h : ∀ i ∈ s, SuppIn q m (f i)) : SuppIn q m (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using suppIn_zero q m
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact suppIn_add (h a (Finset.mem_insert_self _ _))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma suppIn_monomial {q m j : ℕ} (hj : j < m) (c : L) : SuppIn q m (monomial (q ^ j) c) := by
  intro n h
  rw [coeff_monomial] at h
  by_cases e : q ^ j = n
  · exact ⟨j, hj, e.symm⟩
  · rw [if_neg e] at h; exact absurd rfl h

lemma suppIn_coeff_zero {q m : ℕ} (hq : 2 ≤ q) {f : L[X]} (hf : SuppIn q m f) :
    f.coeff 0 = 0 := by
  by_contra h
  obtain ⟨i, _, e⟩ := hf 0 h
  have : 0 < q ^ i := Nat.pow_pos (by omega)
  omega

lemma suppIn_natDegree {q m : ℕ} (hq : 1 ≤ q) {f : L[X]} (hf : SuppIn q m f) :
    f.natDegree ≤ q ^ (m - 1) := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  by_contra h
  obtain ⟨i, hi, e⟩ := hf N h
  have : q ^ i ≤ q ^ (m - 1) := Nat.pow_le_pow_right hq (by omega)
  omega

end Supp


section Lin

variable {L : Type*} [Field L]

lemma coeff_linearized_apply {q k : ℕ} (c : Fin k → L) (n : ℕ) :
    (linearized q c).coeff n = ∑ i : Fin k, if q ^ i.val = n then c i else 0 := by
  unfold linearized
  rw [finsetSum_coeff]
  simp only [coeff_monomial]

lemma coeff_linearized {q k : ℕ} (hq : 2 ≤ q) (c : Fin k → L) (i : Fin k) :
    (linearized q c).coeff (q ^ i.val) = c i := by
  rw [coeff_linearized_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have : q ^ j.val ≠ q ^ i.val := fun h =>
      hj (Fin.ext (Nat.pow_right_injective hq h))
    simp [this]
  · simp

lemma linearized_suppIn {q k : ℕ} (c : Fin k → L) : SuppIn q k (linearized q c) := by
  unfold linearized
  apply suppIn_sum
  intro i _
  exact suppIn_monomial i.isLt _

lemma isLinearized_of_suppIn {q m : ℕ} (hq : 2 ≤ q) {f : L[X]} (hf : SuppIn q m f) :
    IsLinearized q m f := by
  refine ⟨fun i => f.coeff (q ^ i.val), ?_⟩
  ext n
  rw [coeff_linearized_apply]
  by_cases hn : f.coeff n = 0
  · rw [hn]
    symm
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with h
    · rw [h]; exact hn
    · rfl
  · obtain ⟨i, hi, e⟩ := hf n hn
    rw [Finset.sum_eq_single ⟨i, hi⟩]
    · simp [e]
    · intro j _ hj
      have : q ^ j.val ≠ n := by
        rw [e]; intro h
        exact hj (Fin.ext (by simpa using Nat.pow_right_injective hq h))
      simp [this]
    · simp

lemma isLinearized_iff {q m : ℕ} (hq : 2 ≤ q) {f : L[X]} :
    IsLinearized q m f ↔ SuppIn q m f := by
  constructor
  · rintro ⟨c, rfl⟩; exact linearized_suppIn c
  · exact isLinearized_of_suppIn hq

lemma eval_linearized {q k : ℕ} (c : Fin k → L) (x : L) :
    (linearized q c).eval x = ∑ i, c i * x ^ (q ^ i.val) := by
  unfold linearized
  simp [eval_finsetSum]

lemma linearized_ne_zero {q k : ℕ} (hq : 2 ≤ q) {c : Fin k → L} (hc : c ≠ 0) :
    linearized q c ≠ 0 := by
  intro h
  apply hc
  funext i
  have := coeff_linearized hq c i
  rw [h, coeff_zero] at this
  simpa using this.symm

end Lin


section Frob

lemma sum_comp' {R : Type*} [CommSemiring R] {ι : Type*} (s : Finset ι) (f : ι → R[X]) (g : R[X]) :
    (∑ i ∈ s, f i).comp g = ∑ i ∈ s, (f i).comp g := by
  simpa using map_sum (Polynomial.compRingHom g) f s

lemma frob_add {R : Type*} [CommSemiring R] {p s q : ℕ} [Fact p.Prime] [CharP R p]
    (hq : q = p ^ s) (x y : R) (i : ℕ) : (x + y) ^ (q ^ i) = x ^ (q ^ i) + y ^ (q ^ i) := by
  rw [hq, ← pow_mul]
  exact add_pow_char_pow x y p (s * i)

variable {L : Type*} [Field L] {p s q : ℕ} [Fact p.Prime] [CharP L p] (hq : q = p ^ s)
include hq

lemma comp_add {m : ℕ} {f : L[X]} (hf : IsLinearized q m f) (g h : L[X]) :
    f.comp (g + h) = f.comp g + f.comp h := by
  obtain ⟨c, rfl⟩ := hf
  unfold linearized
  simp only [sum_comp', monomial_comp, frob_add hq, mul_add,
    Finset.sum_add_distrib]

lemma eval_add' {m : ℕ} {f : L[X]} (hf : IsLinearized q m f) (x y : L) :
    f.eval (x + y) = f.eval x + f.eval y := by
  obtain ⟨c, rfl⟩ := hf
  simp only [eval_linearized, frob_add hq, mul_add, Finset.sum_add_distrib]

lemma suppIn_pow {m : ℕ} (hq2 : 2 ≤ q) {P : L[X]} (hP : SuppIn q m P) (i : ℕ) :
    SuppIn q (m + i) (P ^ (q ^ i)) := by
  obtain ⟨c, rfl⟩ := (isLinearized_iff hq2).2 hP
  have : ExpChar L[X] p := ExpChar.prime (Fact.out)
  have : q ^ i = p ^ (s * i) := by rw [hq, pow_mul]
  unfold linearized
  rw [this, sum_pow_char_pow]
  apply suppIn_sum
  intro j _
  rw [monomial_pow, ← this, ← pow_add]
  exact suppIn_monomial (by have := j.isLt; omega) _

lemma comp_isLinearized {t k : ℕ} (hq2 : 2 ≤ q) {A P : L[X]} (hA : IsLinearized q (t + 1) A)
    (hP : IsLinearized q k P) : IsLinearized q (k + t) (A.comp P) := by
  rw [isLinearized_iff hq2]
  obtain ⟨c, rfl⟩ := hA
  unfold linearized
  simp only [sum_comp', monomial_comp]
  apply suppIn_sum
  intro i _
  apply suppIn_Cmul
  exact suppIn_mono (by have := i.isLt; omega)
    (suppIn_pow hq hq2 ((isLinearized_iff hq2).1 hP) i.val)

end Frob


section KLin

variable {K L : Type*} [Field K] [Fintype K] [Field L] [Algebra K L]

lemma eval_smul' {m : ℕ} {f : L[X]} (hf : IsLinearized (Fintype.card K) m f) (a : K) (x : L) :
    f.eval (algebraMap K L a * x) = algebraMap K L a * f.eval x := by
  obtain ⟨c, rfl⟩ := hf
  simp only [eval_linearized, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← map_pow, FiniteField.pow_card_pow]; ring

/-- Evaluation of a q-polynomial as a K-linear map. -/
noncomputable def evalLin {p s : ℕ} [Fact p.Prime] [CharP L p] (hq : Fintype.card K = p ^ s)
    {m : ℕ} {f : L[X]} (hf : IsLinearized (Fintype.card K) m f) : L →ₗ[K] L where
  toFun x := f.eval x
  map_add' x y := eval_add' hq hf x y
  map_smul' a x := by
    simp only [Algebra.smul_def, RingHom.id_apply]
    exact eval_smul' hf a x

lemma evalLin_apply {p s : ℕ} [Fact p.Prime] [CharP L p] (hq : Fintype.card K = p ^ s)
    {m : ℕ} {f : L[X]} (hf : IsLinearized (Fintype.card K) m f) (x : L) :
    evalLin hq hf x = f.eval x := rfl

end KLin

section Sub

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Fintype L]

lemma exists_finset_mem (W : Submodule K L) :
    ∃ S : Finset L, ∀ v, v ∈ S ↔ v ∈ W := by
  classical
  exact ⟨Finset.univ.filter (· ∈ W), by simp⟩

lemma annihilator_eq {W : Submodule K L} (S : Finset L) (hS : ∀ v, v ∈ S ↔ v ∈ W) :
    annihilator K W = ∏ v ∈ S, (X - C v) := by
  classical
  unfold annihilator
  exact (Finset.prod_subtype S (p := (· ∈ W)) hS (fun v => X - C v)).symm

lemma card_finset_eq {W : Submodule K L} [Fintype K] (S : Finset L) (hS : ∀ v, v ∈ S ↔ v ∈ W) :
    S.card = Fintype.card K ^ Module.finrank K W := by
  classical
  have : S = Finset.univ.filter (· ∈ W) := by ext v; simp [hS]
  subst this
  rw [← Fintype.card_subtype]
  exact Module.card_eq_pow_finrank (K := K) (V := W)

end Sub


section Ann

variable {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
  {p s : ℕ} [Fact p.Prime] [CharP L p] (hq : Fintype.card K = p ^ s)
include hq

lemma exists_vanishing (W : Submodule K L) :
    ∃ c : Fin (Module.finrank K W + 1) → L, c ≠ 0 ∧
      ∀ w ∈ W, (linearized (Fintype.card K) c).eval w = 0 := by
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have : Module.Finite K L := inferInstance
  set d := Module.finrank K W with hd
  let b : Module.Basis (Fin d) K W := Module.finBasis K W
  let Φ : (Fin (d + 1) → L) →ₗ[L] (Fin d → L) :=
    { toFun := fun c j => ∑ i, c i * ((b j : L)) ^ (Fintype.card K ^ i.val)
      map_add' := by intro c c'; ext j; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro a c; ext j; simp [Finset.mul_sum, mul_assoc] }
  have hlt : Module.finrank L (Fin d → L) < Module.finrank L (Fin (d + 1) → L) := by
    simp
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) hlt
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hker
  refine ⟨c, hc0, ?_⟩
  have hlin : IsLinearized (Fintype.card K) (d + 1) (linearized (Fintype.card K) c) := ⟨c, rfl⟩
  intro w hw
  have hbj : ∀ j, (linearized (Fintype.card K) c).eval (b j : L) = 0 := by
    intro j
    have := congrFun (LinearMap.mem_ker.1 hc) j
    rw [eval_linearized]
    exact this
  have hsum : w = ∑ j, (b.repr ⟨w, hw⟩ j) • (b j : L) := by
    have h := congrArg (fun x : W => (x : L)) (b.sum_repr ⟨w, hw⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  have := evalLin_apply hq hlin w
  rw [← this, hsum, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_smul, evalLin_apply, hbj, smul_zero]

lemma annihilator_props (W : Submodule K L) {t : ℕ} (ht : Module.finrank K W ≤ t) :
    (annihilator K W).Monic ∧ IsLinearized (Fintype.card K) (t + 1) (annihilator K W) := by
  classical
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  obtain ⟨S, hS⟩ := exists_finset_mem W
  have hcard := card_finset_eq S hS
  set d := Module.finrank K W with hd
  have hmon : (annihilator K W).Monic := by
    rw [annihilator_eq S hS]
    exact monic_prod_of_monic _ _ (fun v _ => monic_X_sub_C v)
  refine ⟨hmon, ?_⟩
  obtain ⟨c, hc, hvan⟩ := exists_vanishing hq W
  set f := linearized (Fintype.card K) c with hf
  have hf0 : f ≠ 0 := linearized_ne_zero hq2 hc
  have hsupp : SuppIn (Fintype.card K) (d + 1) f := linearized_suppIn c
  have hdeg : f.natDegree ≤ Fintype.card K ^ d := by
    simpa using suppIn_natDegree (by omega) hsupp
  have hdvd : (∏ v ∈ S, (X - C v)) ∣ f := by
    have := (Multiset.prod_X_sub_C_dvd_iff_le_roots hf0 S.val).2
      ((Multiset.le_iff_subset S.nodup).2 (by
        intro v hv
        rw [mem_roots hf0]
        exact hvan v ((hS v).1 hv)))
    rw [Finset.prod_eq_multiset_prod]; exact this
  obtain ⟨g, hg⟩ := hdvd
  have hΛ0 : (∏ v ∈ S, (X - C v)) ≠ 0 := by
    rw [← annihilator_eq S hS]; exact hmon.ne_zero
  have hg0 : g ≠ 0 := by
    rintro rfl; apply hf0; rw [hg, mul_zero]
  have hdegΛ : (∏ v ∈ S, (X - C v)).natDegree = Fintype.card K ^ d := by
    rw [natDegree_finsetProd_X_sub_C_eq_card S (fun v => v)]
    exact hcard
  have : g.natDegree = 0 := by
    have h1 := natDegree_mul hΛ0 hg0
    rw [← hg, hdegΛ] at h1
    omega
  have hgC := eq_C_of_natDegree_eq_zero this
  set a := g.coeff 0 with ha
  have ha0 : a ≠ 0 := by
    intro h; apply hg0; rw [hgC, h, C_0]
  have : annihilator K W = C a⁻¹ * f := by
    rw [annihilator_eq S hS, hg, hgC, ← mul_assoc, mul_comm (C a⁻¹), mul_assoc, ← C_mul,
      inv_mul_cancel₀ ha0, C_1, mul_one]
  rw [this, isLinearized_iff hq2]
  exact suppIn_mono (by omega : d + 1 ≤ t + 1) (suppIn_Cmul _ hsupp)

end Ann


section Uniq

variable {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
  {p s : ℕ} [Fact p.Prime] [CharP L p] (hq : Fintype.card K = p ^ s)
include hq

lemma uniq {n k t : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (ht : 2 * t < n - k + 1)
    (α : Fin n → L) (hα : LinearIndependent K α)
    (P : Polynomial L) (hP : IsLinearized (Fintype.card K) k P)
    (err y : Fin n → L) (hy : y = evaluateWord α P + err) (herr : wordRank K err ≤ t)
    (A B : Polynomial L) (hAB : IsReconstruction (Fintype.card K) k t α y A B) :
    B = A.comp P := by
  classical
  obtain ⟨hA, hB, -, hev⟩ := hAB
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hAP : IsLinearized (Fintype.card K) (k + t) (A.comp P) := comp_isLinearized hq hq2 hA hP
  have hD : IsLinearized (Fintype.card K) (k + t) (B - A.comp P) := by
    rw [isLinearized_iff hq2] at hB hAP ⊢
    exact suppIn_sub hB hAP
  set D := B - A.comp P with hDdef
  have hDsupp : SuppIn (Fintype.card K) (k + t) D := (isLinearized_iff hq2).1 hD
  have key : ∀ r, D.eval (α r) = A.eval (err r) := by
    intro r
    have h1 := hev r
    rw [hy] at h1
    simp only [Pi.add_apply, evaluateWord] at h1
    rw [eval_add' hq hA] at h1
    rw [hDdef, eval_sub, ← h1, eval_comp]
    ring
  set W : Submodule K L := Submodule.span K (Set.range err) with hW
  have hWd : Module.finrank K W ≤ t := herr
  let Al := evalLin hq hA
  let Dl := evalLin hq hD
  set W' : Submodule K L := W.map Al with hW'
  have hmap : (Submodule.span K (Set.range α)).map Dl ≤ W' := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
    exact ⟨err r, Submodule.subset_span ⟨r, rfl⟩, (key r).symm⟩
  obtain ⟨SW, hSW⟩ := exists_finset_mem W'
  obtain ⟨SV, hSV⟩ := exists_finset_mem (Submodule.span K (Set.range α))
  have hcW := card_finset_eq SW hSW
  have hcV := card_finset_eq SV hSV
  have hW'd : Module.finrank K W' ≤ t :=
    (Submodule.finrank_map_le Al W).trans hWd
  have hVd : Module.finrank K (Submodule.span K (Set.range α)) = n := by
    rw [finrank_span_eq_card hα]; simp
  set Γ : L[X] := ∏ v ∈ SW, (X - C v) with hΓ
  have hΓdeg : Γ.natDegree ≤ Fintype.card K ^ t := by
    rw [hΓ, natDegree_finsetProd_X_sub_C_eq_card SW (fun v => v), hcW]
    exact Nat.pow_le_pow_right (by omega) hW'd
  have hΓmon : Γ.Monic := monic_prod_of_monic _ _ (fun v _ => monic_X_sub_C v)
  have hDdeg : D.natDegree ≤ Fintype.card K ^ (k + t - 1) :=
    suppIn_natDegree (by omega) hDsupp
  have hlt : (Γ.comp D).natDegree < SV.card := by
    rw [natDegree_comp, hcV, hVd]
    calc Γ.natDegree * D.natDegree ≤ Fintype.card K ^ t * Fintype.card K ^ (k + t - 1) :=
          Nat.mul_le_mul hΓdeg hDdeg
      _ = Fintype.card K ^ (t + (k + t - 1)) := (pow_add _ _ _).symm
      _ < Fintype.card K ^ n := Nat.pow_lt_pow_right (by omega) (by omega)
  have hzero : Γ.comp D = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ SV _ hlt
    intro v hv
    have hvV := (hSV v).1 hv
    have hmem : D.eval v ∈ W' := hmap ⟨v, hvV, rfl⟩
    rw [eval_comp, hΓ, eval_prod]
    exact Finset.prod_eq_zero ((hSW _).2 hmem) (by simp)
  rcases comp_eq_zero_iff.1 hzero with h | ⟨-, h⟩
  · exact absurd h hΓmon.ne_zero
  · rw [suppIn_coeff_zero hq2 hDsupp, C_0] at h
    exact sub_eq_zero.1 h

end Uniq

end GabidulinProx.Dev.Rec

namespace GabidulinProx.UniqueDecoding

theorem chk_lemma_2_7 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] {n k t : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (ht : 2 * t < n - k + 1) (α : Fin n → L) (hα : LinearIndependent K α)
    (P : Polynomial L) (hP : IsLinearized (Fintype.card K) k P)
    (err y : Fin n → L) (hy : y = evaluateWord α P + err) (herr : wordRank K err ≤ t) :
    (∃ A B : Polynomial L, IsReconstruction (Fintype.card K) k t α y A B) ∧
    (let Λ := annihilator K (Submodule.span K (Set.range err))
     Λ.Monic ∧ Λ ≠ 0 ∧ IsReconstruction (Fintype.card K) k t α y Λ (Λ.comp P)) ∧
    (∀ A B : Polynomial L, IsReconstruction (Fintype.card K) k t α y A B → B = A.comp P) ∧
    (∀ A B P' : Polynomial L, IsReconstruction (Fintype.card K) k t α y A B →
      IsLinearized (Fintype.card K) k P' → B = A.comp P → B = A.comp P' → P = P') := by
  classical
  obtain ⟨p, hpK⟩ := CharP.exists K
  obtain ⟨s, hp, hcard⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hq : Fintype.card K = p ^ (s : ℕ) := hcard
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  set W : Submodule K L := Submodule.span K (Set.range err) with hW
  have hWd : Module.finrank K W ≤ t := herr
  obtain ⟨hmon, hlin⟩ := GabidulinProx.Dev.Rec.annihilator_props hq W hWd
  have hrec : IsReconstruction (Fintype.card K) k t α y (annihilator K W)
      ((annihilator K W).comp P) := by
    refine ⟨hlin, GabidulinProx.Dev.Rec.comp_isLinearized hq hq2 hlin hP,
      Or.inl hmon.ne_zero, ?_⟩
    intro r
    obtain ⟨S, hS⟩ := GabidulinProx.Dev.Rec.exists_finset_mem W
    have hy' : y r = P.eval (α r) + err r := by rw [hy]; rfl
    have hzero : (annihilator K W).eval (err r) = 0 := by
      rw [GabidulinProx.Dev.Rec.annihilator_eq S hS, eval_prod]
      exact Finset.prod_eq_zero ((hS _).2 (Submodule.subset_span ⟨r, rfl⟩)) (by simp)
    rw [hy', GabidulinProx.Dev.Rec.eval_add' hq hlin, hzero, add_zero, eval_comp]
  have huniq : ∀ A B : Polynomial L,
      IsReconstruction (Fintype.card K) k t α y A B → B = A.comp P :=
    fun A B h => GabidulinProx.Dev.Rec.uniq hq hk hkn ht α hα P hP err y hy herr A B h
  refine ⟨⟨_, _, hrec⟩, ⟨hmon, hmon.ne_zero, hrec⟩, huniq, ?_⟩
  intro A B P' hAB hP' h1 h2
  obtain ⟨hA, hB, hne, -⟩ := hAB
  have hA0 : A ≠ 0 := by
    rintro rfl
    rcases hne with h | h
    · exact h rfl
    · apply h; rw [h1]; simp
  have hdiff : A.comp (P - P') = 0 := by
    have := GabidulinProx.Dev.Rec.comp_add hq hA (P - P') P'
    rw [sub_add_cancel] at this
    rw [← h1, ← h2] at this
    simpa using this
  have hsupp : GabidulinProx.Dev.Rec.SuppIn (Fintype.card K) k (P - P') :=
    GabidulinProx.Dev.Rec.suppIn_sub ((GabidulinProx.Dev.Rec.isLinearized_iff hq2).1 hP)
      ((GabidulinProx.Dev.Rec.isLinearized_iff hq2).1 hP')
  rcases comp_eq_zero_iff.1 hdiff with h | ⟨-, h⟩
  · exact absurd h hA0
  · rw [GabidulinProx.Dev.Rec.suppIn_coeff_zero hq2 hsupp, C_0] at h
    exact sub_eq_zero.1 h

end GabidulinProx.UniqueDecoding
end

theorem solution : type_of% @GabidulinProx.UniqueDecoding.chk_lemma_2_7 := @GabidulinProx.UniqueDecoding.chk_lemma_2_7
