-- Prove2me | solution 1 for BaconThesis.ExchangeUniv.eq_D_5_D_7
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T22:30:02.250883+00:00
-- url     : https://prove2.me/submissions/484ec0e3-1c1c-4b02-a027-22449e3b019a

import Mathlib
import Definitions.Def_BaconThesis_ExchangeUniv_collS

open scoped Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace BaconThesis.ExchangeUniv.SolD5

open Matrix BaconThesis.Collective BaconThesis.ExchangeUniv

section Qubit

variable {n : ℕ}

abbrev St (n : ℕ) := Fin n → Fin 2

lemma sum_agr (i : Fin n) (x : St n) (g : St n → ℂ) :
    ∑ y, (if ∀ k, k ≠ i → x k = y k then g y else 0) = ∑ t, g (Function.update x i t) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun t _ => Function.update x i t)
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro k hk
    rw [Function.update_of_ne hk]
  · intro t _ t' _ h
    have := congrFun h i
    simpa using this
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨y i, Finset.mem_univ _, ?_⟩
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_of_ne hk, hy k hk]
  · intro t _; rfl

lemma onQubit_add (i : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    onQubit i (A + B) = onQubit i A + onQubit i B := by
  ext x y; simp only [onQubit, Matrix.add_apply]; split_ifs <;> simp

lemma onQubit_smul (i : Fin n) (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    onQubit i (c • A) = c • onQubit i A := by
  ext x y; simp only [onQubit, Matrix.smul_apply]; split_ifs <;> simp

lemma onQubit_star (i : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (onQubit i A)ᴴ = onQubit i Aᴴ := by
  ext x y
  simp only [onQubit, conjTranspose_apply]
  by_cases h : ∀ k, k ≠ i → x k = y k
  · rw [if_pos h, if_pos (fun k hk => (h k hk).symm)]
  · rw [if_neg h, if_neg (fun h' => h (fun k hk => (h' k hk).symm)), star_zero]

lemma onQubit_mul_same (i : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    onQubit i A * onQubit i B = onQubit i (A * B) := by
  ext x z
  rw [Matrix.mul_apply]
  have : ∀ y, onQubit i A x y * onQubit i B y z
      = if ∀ k, k ≠ i → x k = y k then A (x i) (y i) * onQubit i B y z else 0 := by
    intro y; simp only [onQubit]; split_ifs <;> simp
  simp only [this]
  rw [sum_agr]
  simp only [onQubit, Function.update_self, Matrix.mul_apply]
  by_cases h : ∀ k, k ≠ i → x k = z k
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [if_pos (fun k hk => by rw [Function.update_of_ne hk]; exact h k hk)]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg (fun h' => h (fun k hk => by have := h' k hk; rwa [Function.update_of_ne hk] at this)),
      mul_zero]

lemma onQubit_mul_ne (i j : Fin n) (hij : i ≠ j) (A B : Matrix (Fin 2) (Fin 2) ℂ) (x z : St n) :
    (onQubit i A * onQubit j B) x z
      = if ∀ k, k ≠ i → k ≠ j → x k = z k then A (x i) (z i) * B (x j) (z j) else 0 := by
  rw [Matrix.mul_apply]
  have : ∀ y, onQubit i A x y * onQubit j B y z
      = if ∀ k, k ≠ i → x k = y k then A (x i) (y i) * onQubit j B y z else 0 := by
    intro y; simp only [onQubit]; split_ifs <;> simp
  simp only [this]
  rw [sum_agr]
  simp only [onQubit, Function.update_self, Function.update_of_ne hij.symm]
  rw [Finset.sum_eq_single (z i)]
  · by_cases h : ∀ k, k ≠ i → k ≠ j → x k = z k
    · rw [if_pos h, if_pos]
      intro k hk
      by_cases hki : k = i
      · subst hki; simp
      · rw [Function.update_of_ne hki]; exact h k hki hk
    · rw [if_neg h, if_neg, mul_zero]
      intro h'
      apply h
      intro k hki hkj
      have := h' k hkj
      rwa [Function.update_of_ne hki] at this
  · intro t _ ht
    rw [if_neg, mul_zero]
    intro h'
    have := h' i hij
    rw [Function.update_self] at this
    exact ht this
  · simp

lemma onQubit_comm (i j : Fin n) (hij : i ≠ j) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    onQubit i A * onQubit j B = onQubit j B * onQubit i A := by
  ext x z
  rw [onQubit_mul_ne i j hij, onQubit_mul_ne j i hij.symm]
  by_cases h : ∀ k, k ≠ i → k ≠ j → x k = z k
  · rw [if_pos h, if_pos (fun k h1 h2 => h k h2 h1), mul_comm]
  · rw [if_neg h, if_neg (fun h' => h (fun k h1 h2 => h' k h2 h1))]

variable (n) in
/-- `Σ_i O^(i)`. -/
noncomputable def coll (O : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (St n) (St n) ℂ :=
  ∑ i : Fin n, onQubit i O

lemma coll_add (A B : Matrix (Fin 2) (Fin 2) ℂ) : coll n (A + B) = coll n A + coll n B := by
  simp [coll, onQubit_add, Finset.sum_add_distrib]

lemma coll_smul (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) : coll n (c • A) = c • coll n A := by
  simp [coll, onQubit_smul, Finset.smul_sum]

lemma coll_sub (A B : Matrix (Fin 2) (Fin 2) ℂ) : coll n (A - B) = coll n A - coll n B := by
  rw [sub_eq_add_neg, coll_add, ← neg_one_smul ℂ B, coll_smul]; module

lemma coll_star (A : Matrix (Fin 2) (Fin 2) ℂ) : (coll n A)ᴴ = coll n Aᴴ := by
  simp [coll, conjTranspose_sum, onQubit_star]

lemma coll_comm (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    coll n A * coll n B - coll n B * coll n A = coll n (A * B - B * A) := by
  simp only [coll, Finset.sum_mul_sum]
  rw [Finset.sum_comm (f := fun i j => onQubit i B * onQubit j A), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · rw [onQubit_mul_same, onQubit_mul_same, sub_eq_add_neg (A * B), ← neg_one_smul ℂ (B * A),
      onQubit_add, onQubit_smul, neg_one_smul, ← sub_eq_add_neg]
  · intro j _ hj
    rw [onQubit_comm i j (Ne.symm hj), sub_self]
  · simp

def sp : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
def sm : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
noncomputable def sz : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 0; 0, -1 / 2]

lemma collS_eq (α : Fin 3) : collS n α = coll n ((1 / 2 : ℂ) • pauli α) := by
  simp [collS, coll, onQubit_smul, Finset.smul_sum]

lemma Sp_eq : collS n 0 + Complex.I • collS n 1 = coll n sp := by
  rw [collS_eq, collS_eq, ← coll_smul, ← coll_add]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli, sp] <;> ring_nf <;> (try simp [Complex.I_sq]) <;> norm_num

lemma Sm_eq : collS n 0 - Complex.I • collS n 1 = coll n sm := by
  rw [collS_eq, collS_eq, ← coll_smul, ← coll_sub]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli, sm] <;> ring_nf <;> (try simp [Complex.I_sq]) <;> norm_num

lemma Sz_eq : collS n 2 = coll n sz := by
  rw [collS_eq]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli, sz] <;> norm_num

lemma sm_star : (coll n sm)ᴴ = coll n sp := by
  rw [coll_star]; congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [sp, sm]

lemma comm_pm : coll n sp * coll n sm - coll n sm * coll n sp = (2 : ℂ) • coll n sz := by
  rw [coll_comm, ← coll_smul]; congr 1
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sp, sm, sz, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

lemma onQubit_mulVec (i : Fin n) (O : Matrix (Fin 2) (Fin 2) ℂ) (g : St n → ℂ) (x : St n) :
    (onQubit i O *ᵥ g) x = ∑ s, O (x i) s * g (Function.update x i s) := by
  simp only [Matrix.mulVec, dotProduct, onQubit, ite_mul, zero_mul]
  rw [sum_agr i x (fun y => O (x i) (y i) * g y)]
  simp

end Qubit

/-- `f ⊗ |t⟩` with the new qubit last. -/
def app {m : ℕ} (f : St m → ℂ) (t : Fin 2) : St (m + 1) → ℂ :=
  fun x => if x (Fin.last m) = t then f (Fin.init x) else 0

lemma coll_last {m : ℕ} (O : Matrix (Fin 2) (Fin 2) ℂ) (f : St m → ℂ) (t : Fin 2) (x : St (m + 1)) :
    (coll (m + 1) O *ᵥ app f t) x =
      (if x (Fin.last m) = t then (coll m O *ᵥ f) (Fin.init x) else 0) +
        O (x (Fin.last m)) t * f (Fin.init x) := by
  rw [coll, Fin.sum_univ_castSucc, Matrix.add_mulVec, Matrix.sum_mulVec, Pi.add_apply,
    Finset.sum_apply]
  congr 1
  · by_cases h : x (Fin.last m) = t
    · rw [if_pos h, coll, Matrix.sum_mulVec, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [onQubit_mulVec, onQubit_mulVec]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp [app, Fin.init_update_castSucc, Function.update_of_ne (Fin.castSucc_lt_last j).ne',
        h, Fin.init]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [onQubit_mulVec]
      refine Finset.sum_eq_zero fun s _ => ?_
      simp [app, Function.update_of_ne (Fin.castSucc_lt_last j).ne', h]
  · rw [onQubit_mulVec]
    simp [app, Fin.init_update_last]

lemma sum_snoc {m : ℕ} (g : St (m + 1) → ℂ) :
    ∑ x, g x = ∑ t : Fin 2, ∑ y : St m, g (Fin.snoc y t) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin 2) _ _ (fun _ => rfl)).symm

end BaconThesis.ExchangeUniv.SolD5

open BaconThesis.ExchangeUniv BaconThesis.ExchangeUniv.SolD5 in
theorem solution (m : ℕ) (J : ℝ) (hJ : 0 ≤ J) (Tp : (Fin m → Fin 2) → ℂ)
    (hz : collS m 2 *ᵥ Tp = ((J + 1 / 2 : ℝ) : ℂ) • Tp)
    (hup : (collS m 0 + Complex.I • collS m 1) *ᵥ Tp = 0)
    (hnorm : star Tp ⬝ᵥ Tp = 1) (α β : ℂ) :
    let Tm : (Fin m → Fin 2) → ℂ :=
      (((Real.sqrt (2 * J + 1))⁻¹ : ℝ) : ℂ) • ((collS m 0 - Complex.I • collS m 1) *ᵥ Tp)
    let ψ : (Fin (m + 1) → Fin 2) → ℂ := fun x =>
      if x (Fin.last m) = 1 then α * Tp (Fin.init x) else β * Tm (Fin.init x)
    ((collS (m + 1) 0 + Complex.I • collS (m + 1) 1) *ᵥ ψ = 0 ↔
        α + (Real.sqrt (2 * J + 1) : ℂ) * β = 0) ∧
    ((collS (m + 1) 0 + Complex.I • collS (m + 1) 1) *ᵥ ψ = 0 ∧ star ψ ⬝ᵥ ψ = 1 ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧
        α = c * (-(Real.sqrt ((2 * J + 1) / (2 * J + 2)) : ℂ)) ∧
        β = c * ((1 / Real.sqrt (2 * J + 2) : ℝ) : ℂ)) := by
  intro Tm ψ
  set B := Real.sqrt (2 * J + 1) with hBdef
  set C := Real.sqrt (2 * J + 2) with hCdef
  have hB : 0 < B := Real.sqrt_pos.mpr (by linarith)
  have hC : 0 < C := Real.sqrt_pos.mpr (by linarith)
  have hB2 : B ^ 2 = 2 * J + 1 := Real.sq_sqrt (by linarith)
  have hC2 : C ^ 2 = 2 * J + 2 := Real.sq_sqrt (by linarith)
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hCc : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  rw [Sp_eq] at hup ⊢
  rw [Sz_eq] at hz
  have hTm : Tm = ((B⁻¹ : ℝ) : ℂ) • (coll m sm *ᵥ Tp) := by
    simp only [Tm, Sm_eq]
    rfl
  -- ladder facts
  have hPM : coll m sp *ᵥ (coll m sm *ᵥ Tp) = ((B ^ 2 : ℝ) : ℂ) • Tp := by
    have e : coll m sp * coll m sm = coll m sm * coll m sp + (2 : ℂ) • coll m sz := by
      rw [← comm_pm]; abel
    rw [Matrix.mulVec_mulVec, e, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hup,
      Matrix.mulVec_zero, zero_add, Matrix.smul_mulVec, hz, smul_smul, hB2]
    congr 1
    push_cast
    ring
  have hSpTm : coll m sp *ᵥ Tm = (B : ℂ) • Tp := by
    rw [hTm, Matrix.mulVec_smul, hPM, smul_smul]
    congr 1
    push_cast
    field_simp
  have hTmn : star Tm ⬝ᵥ Tm = 1 := by
    have h1 : star (coll m sm *ᵥ Tp) ⬝ᵥ (coll m sm *ᵥ Tp) = ((B ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, sm_star, hPM,
        dotProduct_smul, hnorm, smul_eq_mul, mul_one]
    rw [hTm, star_smul, smul_dotProduct, dotProduct_smul, h1]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast
    field_simp
  -- the state and its raising
  have hψ : ψ = α • app Tp 1 + β • app Tm 0 := by
    funext x
    simp only [ψ, app, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases Fin.exists_fin_two.mp ⟨x (Fin.last m), rfl⟩ with h | h <;> simp [h]
  have hSψ : coll (m + 1) sp *ᵥ ψ = (α + (B : ℂ) * β) • app Tp 0 := by
    rw [hψ, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coll_last, hup, hSpTm, app]
    rcases Fin.exists_fin_two.mp ⟨x (Fin.last m), rfl⟩ with h | h <;> simp [h, sp] <;> ring
  have happ : app Tp 0 ≠ 0 := by
    intro h0
    have : Tp = 0 := by
      funext y
      have := congrFun h0 (Fin.snoc y 0)
      simpa [app, Fin.init_snoc, Fin.snoc_last] using this
    rw [this] at hnorm
    simp at hnorm
  have part1 : coll (m + 1) sp *ᵥ ψ = 0 ↔ α + (B : ℂ) * β = 0 := by
    rw [hSψ]
    constructor
    · intro h
      exact (smul_eq_zero.mp h).resolve_right happ
    · intro h
      rw [h, zero_smul]
  have hnψ : star ψ ⬝ᵥ ψ = star α * α + star β * β := by
    simp only [dotProduct, Pi.star_apply]
    rw [sum_snoc, Fin.sum_univ_two]
    simp only [ψ, Fin.snoc_last, Fin.init_snoc, show (0 : Fin 2) ≠ 1 by decide,
      if_false, if_true, star_mul']
    have e1 := hTmn
    have e2 := hnorm
    simp only [dotProduct, Pi.star_apply] at e1 e2
    have : ∀ (g : St m → ℂ) (a : ℂ), ∑ y, star a * star (g y) * (a * g y) =
        star a * a * ∑ y, star (g y) * g y := by
      intro g a
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [this, this, e1, e2]
    ring
  have hBC : Real.sqrt ((2 * J + 1) / (2 * J + 2)) = B / C := Real.sqrt_div (by linarith) _
  have hCB : C ^ 2 = B ^ 2 + 1 := by rw [hB2, hC2]; ring
  have hnsq : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
    intro z
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  refine ⟨part1, ?_⟩
  rw [part1, hnψ, hBC]
  constructor
  · rintro ⟨h1, h2⟩
    have hα : α = -((B : ℂ) * β) := by linear_combination h1
    rw [hα] at h2
    have h3 : ((C ^ 2 * Complex.normSq β : ℝ) : ℂ) = 1 := by
      rw [← h2, hCB]
      push_cast
      rw [← hnsq]
      simp only [star_neg, star_mul', Complex.star_def, Complex.conj_ofReal]
      ring
    have h4 : C ^ 2 * Complex.normSq β = 1 := by exact_mod_cast h3
    refine ⟨β * C, ?_, ?_, ?_⟩
    · have : ‖β * (C : ℂ)‖ ^ 2 = 1 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_ofReal]
        linear_combination h4
      have hn := norm_nonneg (β * (C : ℂ))
      nlinarith
    · rw [hα]
      push_cast
      field_simp
    · push_cast
      field_simp
  · rintro ⟨c, hc, hα, hβ⟩
    have hcn : Complex.normSq c = 1 := by rw [Complex.normSq_eq_norm_sq, hc]; norm_num
    refine ⟨?_, ?_⟩
    · rw [hα, hβ]
      push_cast
      field_simp
      ring
    · rw [hα, hβ]
      simp only [star_mul', star_neg, Complex.star_def, Complex.conj_ofReal]
      have hcc : (starRingEnd ℂ) c * c = 1 := by
        have := hnsq c
        rw [hcn] at this
        simpa using this
      push_cast
      field_simp
      have hCB' : (C : ℂ) ^ 2 = (B : ℂ) ^ 2 + 1 := by exact_mod_cast hCB
      linear_combination ((B : ℂ) ^ 2 + 1) * hcc - hCB'
