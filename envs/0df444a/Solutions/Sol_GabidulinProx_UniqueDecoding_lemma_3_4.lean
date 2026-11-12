-- Prove2me | solution 1 for GabidulinProx.UniqueDecoding.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:41:33.481172+00:00
-- url     : https://prove2.me/submissions/961f580e-fa88-40dd-bab3-70f45cfee70a

import Mathlib
import Definitions.Def_GabidulinProx_UniqueDecoding_Reconstruction
import Theorems.Thm_GabidulinProx_UniqueDecoding_lemma_2_7

section
set_option autoImplicit false
open scoped BigOperators
open Polynomial Matrix

namespace GabidulinProx.Dev.L34

section Abstract
variable {L : Type*} [Field L]

lemma natDegree_det_le {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m L[X])
    (D : m → ℕ) (h : ∀ i j, (A i j).natDegree ≤ D j) : A.det.natDegree ≤ ∑ j, D j := by
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ (fun σ _ => ?_)
  have h1 : (Equiv.Perm.sign σ • ∏ i, A (σ i) i).natDegree ≤ (∏ i, A (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  exact h1.trans ((natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => h _ _))

lemma bordered {R : Type*} [CommRing R] [IsDomain R] {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m R) (hA : A.det ≠ 0) (B C : m → R) (D : R) :
    (Matrix.fromBlocks A (Matrix.of fun i (_ : Unit) => B i) (Matrix.of fun (_ : Unit) j => C j)
      (Matrix.of fun (_ : Unit) (_ : Unit) => D)).det = A.det * D - C ⬝ᵥ (A.adjugate *ᵥ B) := by
  classical
  have hinj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  apply hinj
  set φ := algebraMap R (FractionRing R) with hφ
  have hdetA : IsUnit (A.map φ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hinj).2 hA)
  letI : Invertible (A.map φ) := Matrix.invertibleOfIsUnitDet _ hdetA
  have h1 := Matrix.det_fromBlocks₁₁ (A.map φ) (Matrix.of fun i (_ : Unit) => φ (B i))
    (Matrix.of fun (_ : Unit) j => φ (C j)) (Matrix.of fun (_ : Unit) (_ : Unit) => φ D)
  have h2 : φ (fromBlocks A (Matrix.of fun i (_ : Unit) => B i)
      (Matrix.of fun (_ : Unit) j => C j) (Matrix.of fun (_ : Unit) (_ : Unit) => D)).det
      = (fromBlocks (A.map φ) (Matrix.of fun i (_ : Unit) => φ (B i))
        (Matrix.of fun (_ : Unit) j => φ (C j)) (Matrix.of fun (_ : Unit) (_ : Unit) => φ D)).det := by
    rw [RingHom.map_det]
    congr 1
    ext (i | i) (j | j) <;> simp [fromBlocks]
  rw [h2, h1]
  have hne : (A.map φ).det ≠ 0 := hdetA.ne_zero
  have h4 : (A.map φ).adjugate = (A.adjugate).map φ := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]; rfl
  have h5 : (A.map φ).det = φ A.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have h6 : (⅟(A.map φ) : Matrix m m _) = (A.map φ).det⁻¹ • (A.map φ).adjugate := by
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h6]
  have h8 : ∀ X : Matrix Unit Unit (FractionRing R), X.det = X () () := fun X => Matrix.det_unique X
  rw [h8]
  simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_unique,
    Matrix.smul_apply, smul_eq_mul]
  rw [map_sub, map_mul, h5, h4]
  have hd : φ A.det ≠ 0 := h5 ▸ hne
  simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.map_apply]
  field_simp

lemma det_updateCol_finsum {R : Type*} [CommRing R] {m ι : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m R) (j : m) (s : Finset ι) (v : ι → m → R) :
    (A.updateCol j (fun i => ∑ t ∈ s, v t i)).det = ∑ t ∈ s, (A.updateCol j (v t)).det := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [(by funext i; simp : (fun _ : m => (0 : R)) = (0 : R) • (fun _ : m => (0 : R))),
      det_updateCol_smul]
    simp
  | insert a s ha ih =>
    have e : (fun i => ∑ t ∈ insert a s, v t i) = v a + (fun i => ∑ t ∈ s, v t i) := by
      funext i; simp [Finset.sum_insert ha]
    rw [e, det_updateCol_add, ih, Finset.sum_insert ha]

variable {ρ ι : Type*} [Fintype ρ] [Fintype ι] [DecidableEq ρ] [DecidableEq ι]

def MinorNZ (M : Matrix ρ ι L[X]) (r : ℕ) : Prop :=
  ∃ (f : Fin r → ρ) (g : Fin r → ι), (M.submatrix f g).det ≠ 0

omit [Fintype ρ] [Fintype ι] [DecidableEq ρ] [DecidableEq ι] in
lemma minorNZ_zero (M : Matrix ρ ι L[X]) : MinorNZ M 0 :=
  ⟨Fin.elim0, Fin.elim0, by simp⟩

omit [Fintype ρ] [Fintype ι] [DecidableEq ρ] [DecidableEq ι] in
lemma inj_of_det_ne {M : Matrix ρ ι L[X]} {r : ℕ} {f : Fin r → ρ} {g : Fin r → ι}
    (h : (M.submatrix f g).det ≠ 0) : Function.Injective f ∧ Function.Injective g := by
  constructor
  · intro i j hij
    by_contra hne
    exact h (det_zero_of_row_eq hne (by ext k; simp [hij]))
  · intro i j hij
    by_contra hne
    exact h (det_zero_of_column_eq hne (fun k => by simp [hij]))

lemma minorNZ_le {M : Matrix ρ ι L[X]} {r : ℕ} (h : MinorNZ M r) : r ≤ Fintype.card ρ := by
  obtain ⟨f, g, hd⟩ := h
  simpa using Fintype.card_le_of_injective f (inj_of_det_ne hd).1

lemma exists_max (M : Matrix ρ ι L[X]) : ∃ r, MinorNZ M r ∧ ¬ MinorNZ M (r + 1) := by
  classical
  refine ⟨Nat.findGreatest (MinorNZ M) (Fintype.card ρ), ?_, ?_⟩
  · exact Nat.findGreatest_spec (P := MinorNZ M) (Nat.zero_le _) (minorNZ_zero M)
  · intro h
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (minorNZ_le h) h

omit [Fintype ρ] [Fintype ι] [DecidableEq ρ] [DecidableEq ι] in
lemma vanish {M : Matrix ρ ι L[X]} {r : ℕ} (hr : ¬ MinorNZ M (r + 1)) {m : Type*} [Fintype m]
    [DecidableEq m] (hm : Fintype.card m = r + 1) (f : m → ρ) (g : m → ι) :
    (M.submatrix f g).det = 0 := by
  by_contra h
  apply hr
  let e : m ≃ Fin (r + 1) := Fintype.equivFinOfCardEq hm
  refine ⟨f ∘ e.symm, g ∘ e.symm, ?_⟩
  have : M.submatrix (f ∘ e.symm) (g ∘ e.symm) = (M.submatrix f g).submatrix e.symm e.symm := rfl
  rw [this, det_submatrix_equiv_self]
  exact h

lemma sum_le_of_inj {r : ℕ} (g : Fin r → ι) (hg : Function.Injective g) (d : ι → ℕ) :
    ∑ j, d (g j) ≤ ∑ t, d t := by
  classical
  calc ∑ j, d (g j) = ∑ t ∈ Finset.univ.image g, d t :=
        (Finset.sum_image (fun a _ b _ h => hg h)).symm
    _ ≤ ∑ t, d t := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem solve (M : Matrix ρ ι L[X]) (c : ρ → L[X]) (d : ι → ℕ) (dc : ℕ)
    (hM : ∀ r t, (M r t).natDegree ≤ d t) (hc : ∀ r, (c r).natDegree ≤ dc)
    (S : Finset L) (hS : ∑ t, d t + dc < S.card)
    (hsol : ∀ z ∈ S, ∃ x : ι → L, ∀ r, ∑ t, (M r t).eval z * x t = (c r).eval z) :
    ∃ (h : L[X]) (x : ι → L[X]), h ≠ 0 ∧ h.natDegree ≤ ∑ t, d t ∧
      (∀ t, (x t).natDegree + d t ≤ ∑ t, d t + dc) ∧ ∀ r, ∑ t, M r t * x t = h * c r := by
  classical
  obtain ⟨r0, ⟨f, g, hA⟩, hnot⟩ := exists_max M
  set A := M.submatrix f g with hAdef
  obtain ⟨hfi, hgi⟩ := inj_of_det_ne hA
  set w : Fin r0 → L[X] := A.adjugate *ᵥ (fun i => c (f i)) with hw
  have hgsum := sum_le_of_inj g hgi d
  have hN : ∀ s, (Matrix.fromBlocks A (Matrix.of fun i (_ : Unit) => c (f i))
      (Matrix.of fun (_ : Unit) j => M s (g j)) (Matrix.of fun (_ : Unit) (_ : Unit) => c s)).det
      = 0 := by
    intro s
    set N := Matrix.fromBlocks A (Matrix.of fun i (_ : Unit) => c (f i))
      (Matrix.of fun (_ : Unit) j => M s (g j)) (Matrix.of fun (_ : Unit) (_ : Unit) => c s)
      with hNdef
    have hdeg : N.det.natDegree ≤ ∑ t, d t + dc := by
      refine (natDegree_det_le N (Sum.elim (fun j => d (g j)) (fun _ => dc)) ?_).trans ?_
      · rintro (i | i) (j | j) <;> simp [hNdef, hAdef, hM, hc]
      · rw [Fintype.sum_sum_type]
        simpa using hgsum
    have hz : ∀ z ∈ S, N.det.eval z = 0 := by
      intro z hz
      obtain ⟨x, hx⟩ := hsol z hz
      let f' : Fin r0 ⊕ Unit → ρ := Sum.elim f (fun _ => s)
      have hcard : Fintype.card (Fin r0 ⊕ Unit) = r0 + 1 := by simp
      have e1 : N.det.eval z = (N.map (evalRingHom z)).det := by
        have := RingHom.map_det (evalRingHom z) N
        simpa [RingHom.mapMatrix_apply] using this
      set N' := N.map (evalRingHom z) with hN'
      let J : Fin r0 ⊕ Unit := Sum.inr ()
      let v : ι → (Fin r0 ⊕ Unit) → L := fun t i => x t * (M (f' i) t).eval z
      have hcol : (fun i => N' i J) = fun i => ∑ t, v t i := by
        funext i
        have : N' i J = (c (f' i)).eval z := by
          rcases i with i | i <;> simp [hN', hNdef, J, f']
        rw [this, ← hx (f' i)]
        simp only [v]
        exact Finset.sum_congr rfl fun t _ => mul_comm _ _
      have e2 : N' = N'.updateCol J (fun i => ∑ t, v t i) := by
        rw [← hcol]; simp
      have e3 : (N'.updateCol J (fun i => ∑ t, v t i)).det = ∑ t, (N'.updateCol J (v t)).det :=
        by
        exact det_updateCol_finsum N' J Finset.univ v
      have e4 : ∀ t, (N'.updateCol J (v t)).det = 0 := by
        intro t
        have hv : v t = x t • (fun i => (M (f' i) t).eval z) := by
          funext i; simp [v]
        have hu : N'.updateCol J (fun i => (M (f' i) t).eval z) =
            (M.submatrix f' (Sum.elim g (fun _ => t))).map (evalRingHom z) := by
          ext i k
          rcases k with k | k
          · rcases i with i | i <;> simp [hN', hNdef, hAdef, f']
          · simp [J, f']
        have h0 : ((M.submatrix f' (Sum.elim g (fun _ => t))).map (evalRingHom z)).det = 0 := by
          have := RingHom.map_det (evalRingHom z) (M.submatrix f' (Sum.elim g (fun _ => t)))
          rw [vanish hnot hcard, map_zero] at this
          exact this.symm
        rw [hv, det_updateCol_smul, hu, h0, mul_zero]
      rw [e1, e2, e3]
      exact Finset.sum_eq_zero fun t _ => e4 t
    exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' N.det S hz
      (lt_of_le_of_lt hdeg hS)
  have hident : ∀ s, ∑ j, M s (g j) * w j = A.det * c s := by
    intro s
    have h1 := hN s
    rw [bordered A hA (fun i => c (f i)) (fun j => M s (g j)) (c s), sub_eq_zero] at h1
    rw [h1]
    rfl
  refine ⟨A.det, fun t => ∑ j, if g j = t then w j else 0, hA, ?_, ?_, ?_⟩
  · exact (natDegree_det_le A (fun j => d (g j)) (fun i j => hM _ _)).trans hgsum
  · intro t
    beta_reduce
    by_cases ht : ∃ j, g j = t
    · obtain ⟨j, rfl⟩ := ht
      have hx : (∑ j', if g j' = g j then w j' else 0) = w j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb
          exact if_neg (fun h => hb (hgi h))
        · simp
      rw [hx]
      have hwj : w j = (A.updateCol j (fun i => c (f i))).det := by
        have := cramer_eq_adjugate_mulVec A (fun i => c (f i))
        rw [← cramer_apply, this]
      rw [hwj]
      have hb := natDegree_det_le (A.updateCol j (fun i => c (f i)))
        (fun k => if k = j then dc else d (g k)) (by
          intro a k
          by_cases hk : k = j
          · subst hk; simpa using hc _
          · simpa [hk, hAdef] using hM _ _)
      refine (Nat.add_le_add_right hb _).trans ?_
      have hpt : ∀ k, (if k = j then dc else d (g k)) + (if k = j then d (g j) else 0) ≤
          (if k = j then dc else 0) + d (g k) := by
        intro k
        by_cases hk : k = j
        · subst hk; simp
        · simp [hk]
      have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hpt k)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
      omega
    · have : (∑ j, if g j = t then w j else 0) = 0 :=
        Finset.sum_eq_zero fun j _ => if_neg (fun h => ht ⟨j, h⟩)
      rw [this]
      have : d t ≤ ∑ t, d t := Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ t)
      simp only [natDegree_zero]
      omega
  · intro r
    rw [← hident r]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_ite]

end Abstract
open GabidulinProx.UniqueDecoding

section Concrete

variable {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

lemma eval_linearized' {R : Type*} [CommSemiring R] (q : ℕ) {k : ℕ} (c : Fin k → R) (x : R) :
    (linearized q c).eval x = ∑ i, c i * x ^ (q ^ i.val) := by
  simp [linearized, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

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

lemma exists_finset_mem (W : Submodule K L) :
    ∃ S : Finset L, ∀ v, v ∈ S ↔ v ∈ W := by
  classical
  exact ⟨Finset.univ.filter (· ∈ W), by simp⟩

lemma annihilator_eq {W : Submodule K L} (S : Finset L) (hS : ∀ v, v ∈ S ↔ v ∈ W) :
    annihilator K W = ∏ v ∈ S, (X - C v) := by
  classical
  unfold annihilator
  exact (Finset.prod_subtype S (p := (· ∈ W)) hS (fun v => X - C v)).symm

theorem annihilator_coeff_one_ne_zero (W : Submodule K L) :
    (annihilator K W).coeff 1 ≠ 0 := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_mem W
  rw [annihilator_eq S hS]
  have h0 : (0 : L) ∈ S := (hS 0).2 (Submodule.zero_mem W)
  rw [← Finset.mul_prod_erase S (fun v => X - C v) h0]
  simp only [map_zero, sub_zero]
  rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul, coeff_zero_eq_eval_zero, eval_prod]
  apply Finset.prod_ne_zero_iff.2
  intro v hv
  simp only [eval_sub, eval_X, eval_C, zero_sub, ne_eq, neg_eq_zero]
  exact (Finset.mem_erase.1 hv).1

lemma exists_close {n : ℕ} (C : Submodule L (Fin n → L)) (v : Fin n → L) {e : ℕ}
    (hz : codeDistance K C v ≤ e) : ∃ c ∈ C, wordRank K (v - c) ≤ e := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  unfold codeDistance at hz
  obtain ⟨c, -, hc⟩ := Finset.mem_image.1
    (Finset.min'_mem (Finset.univ.image (fun c : C => wordRank K (v - c.val)))
      (Finset.image_nonempty.mpr Finset.univ_nonempty))
  exact ⟨c.val, c.2, hc ▸ hz⟩

lemma per_z {n k e : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hdec : 2 * e < n - k + 1) (α : Fin n → L) (hα : LinearIndependent K α)
    (u₀ u₁ : Fin n → L) (z : L)
    (hz : codeDistance K (gabidulin K α k) (linePoint u₀ u₁ z) ≤ e) :
    ∃ (lam : Fin (e + 1) → L) (ω : Fin (k + e) → L), lam 0 ≠ 0 ∧
      ∀ r, ∑ i, lam i * (u₀ r + z * u₁ r) ^ (Fintype.card K ^ i.val) =
        ∑ j, ω j * α r ^ (Fintype.card K ^ j.val) := by
  set q := Fintype.card K with hq
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  obtain ⟨c, hcC, hc⟩ := exists_close (K := K) (gabidulin K α k) _ hz
  obtain ⟨coef, rfl⟩ := hcC
  set P := linearized q coef with hP
  have hPlin : IsLinearized q k P := ⟨coef, rfl⟩
  set y := linePoint u₀ u₁ z with hy
  set err := y - gabidulinEncoder K α k coef with herr
  have hyeq : y = evaluateWord α P + err := by
    have : evaluateWord α P = gabidulinEncoder K α k coef := by
      funext r
      simp [evaluateWord, hP, eval_linearized', gabidulinEncoder]
      rfl
    rw [this, herr]; abel
  have h27 := (GabidulinProx.UniqueDecoding.lemma_2_7 (K := K) hk hkn hdec α hα P hPlin err y
    hyeq hc).2.1
  obtain ⟨hmon, hne, hlin, hlin2, -, hid⟩ := h27
  obtain ⟨lam, hlam⟩ := hlin
  obtain ⟨ω, hω⟩ := hlin2
  refine ⟨lam, ω, ?_, ?_⟩
  · have h1 := annihilator_coeff_one_ne_zero (K := K)
      (Submodule.span K (Set.range err))
    rw [hlam] at h1
    have := coeff_linearized hq2 lam 0
    simp only [Fin.val_zero, pow_zero] at this
    rwa [this] at h1
  · intro r
    have := hid r
    rw [hω, hlam, eval_linearized', eval_linearized'] at this
    exact this

end Concrete

lemma natDegree_lin_pow {L : Type*} [Field L] (a b : L) (m : ℕ) :
    ((C a + X * C b : L[X]) ^ m).natDegree ≤ m := by
  have h : (C a + X * C b : L[X]).natDegree ≤ 1 := by compute_degree
  calc ((C a + X * C b : L[X]) ^ m).natDegree ≤ m * (C a + X * C b : L[X]).natDegree :=
        natDegree_pow_le
    _ ≤ m * 1 := Nat.mul_le_mul_left _ h
    _ = m := mul_one m

end GabidulinProx.Dev.L34

namespace GabidulinProx.UniqueDecoding

open GabidulinProx.Dev.L34

theorem chk_lemma_3_4 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] {n k e : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (he : 1 ≤ e)
    (hdec : 2 * e < n - k + 1) (α : Fin n → L) (hα : LinearIndependent K α)
    (u₀ u₁ : Fin n → L)
    (hS : sigma (Fintype.card K) e < (goodParameters K α k e u₀ u₁).card) :
    ∃ (a : Fin (e + 1) → Polynomial L) (b : Fin (k + e) → Polynomial L),
      GlobalIdentity (Fintype.card K) α u₀ u₁ a b ∧ GlobalBounds (Fintype.card K) a b := by
  classical
  set q := Fintype.card K with hq
  set S := goodParameters K α k e u₀ u₁ with hSdef
  let M : Matrix (Fin n) (Fin e ⊕ Fin (k + e)) L[X] := fun r t =>
    Sum.elim (fun i : Fin e => (C (u₀ r) + X * C (u₁ r)) ^ (q ^ (i.val + 1)))
      (fun j : Fin (k + e) => C (α r ^ (q ^ j.val))) t
  let c : Fin n → L[X] := fun r => C (u₀ r) + X * C (u₁ r)
  let d : Fin e ⊕ Fin (k + e) → ℕ := Sum.elim (fun i => q ^ (i.val + 1)) (fun _ => 0)
  have hσ : ∑ t, d t + 1 = sigma q e := by
    rw [Fintype.sum_sum_type]
    simp only [d, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, add_zero]
    rw [Fin.sum_univ_eq_sum_range (fun i => q ^ (i + 1)) e, sigma, Finset.sum_range_succ']
    simp
  have hM : ∀ r t, (M r t).natDegree ≤ d t := by
    intro r t
    rcases t with i | j
    · exact natDegree_lin_pow _ _ _
    · simp [M, d]
  have hc : ∀ r, (c r).natDegree ≤ 1 := by
    intro r
    show (C (u₀ r) + X * C (u₁ r) : L[X]).natDegree ≤ 1
    compute_degree
  have hsol : ∀ z ∈ S, ∃ x : Fin e ⊕ Fin (k + e) → L,
      ∀ r, ∑ t, (M r t).eval z * x t = (c r).eval z := by
    intro z hz
    have hz' : codeDistance K (gabidulin K α k) (linePoint u₀ u₁ z) ≤ e := by
      simpa [hSdef, goodParameters] using hz
    obtain ⟨lam, ω, h0, hrel⟩ := per_z hk hkn hdec α hα u₀ u₁ z hz'
    refine ⟨Sum.elim (fun i : Fin e => -lam i.succ / lam 0) (fun j => ω j / lam 0), ?_⟩
    intro r
    have h := hrel r
    rw [Fin.sum_univ_succ] at h
    simp only [Fin.val_zero, pow_zero, pow_one, Fin.val_succ] at h
    rw [Fintype.sum_sum_type]
    simp only [M, c, Sum.elim_inl, Sum.elim_inr, eval_pow, eval_add, eval_C, eval_mul, eval_X]
    have e1 : ∑ i : Fin e, (u₀ r + z * u₁ r) ^ q ^ (i.val + 1) * (-lam i.succ / lam 0) =
        -(∑ i : Fin e, lam i.succ * (u₀ r + z * u₁ r) ^ q ^ (i.val + 1)) / lam 0 := by
      rw [← Finset.sum_neg_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ j : Fin (k + e), α r ^ q ^ j.val * (ω j / lam 0) =
        (∑ j : Fin (k + e), ω j * α r ^ q ^ j.val) / lam 0 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2]
    field_simp
    linear_combination (-1 : L) * h
  have hS' : ∑ t, d t + 1 < S.card := by rw [hσ]; exact hS
  obtain ⟨h, x, hh, hdeg, hxdeg, hid⟩ := solve M c d 1 hM hc S hS' hsol
  refine ⟨Fin.cons h (fun i => -x (Sum.inl i)), fun j => -x (Sum.inr j), ?_, ?_⟩
  · intro r
    have h1 := hid r
    rw [Fintype.sum_sum_type] at h1
    simp only [M, c, Sum.elim_inl, Sum.elim_inr] at h1
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, pow_one, Fin.val_succ,
      neg_mul, Finset.sum_neg_distrib]
    simp only [mul_comm _ (x (Sum.inl _)), mul_comm _ (x (Sum.inr _))] at h1
    linear_combination (-1 : L[X]) * h1
  · refine ⟨hh, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero, Fin.val_zero, pow_zero]
        rw [← hσ]; simpa using hdeg
      · simp only [Fin.cons_succ, Fin.val_succ, natDegree_neg]
        have := hxdeg (Sum.inl i)
        have hd : d (Sum.inl i) = q ^ (i.val + 1) := rfl
        rw [hd] at this
        omega
    · intro j
      simp only [natDegree_neg]
      have := hxdeg (Sum.inr j)
      have hd : d (Sum.inr j) = 0 := rfl
      rw [hd] at this
      omega

end GabidulinProx.UniqueDecoding

end

theorem solution : type_of% @GabidulinProx.UniqueDecoding.chk_lemma_3_4 := @GabidulinProx.UniqueDecoding.chk_lemma_3_4
