-- Prove2me | solution 1 for ConjGrad.Termination.cg_residuals_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:23:51.016811+00:00
-- url     : https://prove2.me/submissions/d8e8696e-9e6a-4059-bf93-198f582c7efd

import Definitions.Def_ConjGrad_Termination_cgIter
import Definitions.Def_ConjGrad_Termination_IsCDRun
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
open Matrix
namespace CGProof
open ConjGrad.Termination
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k x₀ : Fin n → ℝ)
set_option quotPrecheck false
local notation "r" => fun i => (cgIter A k x₀ i).r
local notation "p" => fun i => (cgIter A k x₀ i).p
local notation "a" => fun i => cgA A (cgIter A k x₀ i)
local notation "b" => fun i => ((r (i+1)) ⬝ᵥ (r (i+1))) / ((r i) ⬝ᵥ (r i))
private lemma r_step (i : ℕ) : r (i+1) = r i - a i • (A *ᵥ p i) := rfl
private lemma p_step (i : ℕ) : p (i+1) = r (i+1) + b i • p i := rfl
private lemma r_zero_p (i : ℕ) (h : r i = 0) : p i = 0 := by
  cases i with
  | zero => exact h
  | succ i => rw [p_step, h]; simp [h]
private lemma rr_ne {v : Fin n → ℝ} (h : v ≠ 0) : v ⬝ᵥ v ≠ 0 := by
  intro he
  apply h
  exact (dotProduct_self_eq_zero.mp (by simpa using he))
private lemma asymm (hA : A.PosDef) (u v : Fin n → ℝ) :
    u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
  have ht : A.transpose = A := by simpa using hA.isHermitian.eq
  simpa [ht] using (Matrix.dotProduct_transpose_mulVec A u v)
private lemma pa_pos (hA : A.PosDef) {v : Fin n → ℝ} (h : v ≠ 0) :
    0 < v ⬝ᵥ (A *ᵥ v) := by simpa using hA.dotProduct_mulVec_pos h

private theorem invariant (hA : A.PosDef) (i : ℕ) :
    (∀ j < i, r i ⬝ᵥ r j = 0) ∧
    (∀ j < i, p i ⬝ᵥ (A *ᵥ p j) = 0) ∧
    (∀ j ≤ i, p i ⬝ᵥ r j = r i ⬝ᵥ r i) ∧
    (∀ j < i, p j ⬝ᵥ r i = 0) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simp [cgIter] <;> ring
    | succ i =>
      have hi := ih i (by omega)
      by_cases hz : r i = 0
      · have hp := r_zero_p A k x₀ i hz
        have hn : r (i+1) = 0 := by rw [r_step, hz, hp]; simp
        have hpn := r_zero_p A k x₀ (i+1) hn
        simp [hn, hpn]
      have hrr := rr_ne hz
      have hp : p i ≠ 0 := by
        intro he; have hh := hi.2.2.1 i le_rfl
        rw [he, zero_dotProduct] at hh
        exact hrr hh.symm
      have hpa := ne_of_gt (pa_pos A hA hp)
      have ha : a i ≠ 0 := div_ne_zero hrr hpa
      have hro : ∀ j ≤ i, r (i+1) ⬝ᵥ p j = 0 := by
        intro j hj
        rw [r_step, sub_dotProduct, smul_dotProduct]
        by_cases he : j = i
        · subst j
          rw [dotProduct_comm (r i) (p i), hi.2.2.1 i le_rfl,
            dotProduct_comm (A *ᵥ p i) (p i)]
          dsimp [cgA]; field_simp <;> ring
        · have hj' : j < i := by omega
          rw [dotProduct_comm (r i) (p j), hi.2.2.2 j hj',
            dotProduct_comm (A *ᵥ p i) (p j), asymm A hA (p j) (p i),
            hi.2.1 j hj']; ring
      have hrrn : ∀ j ≤ i, r (i+1) ⬝ᵥ r j = 0 := by
        intro j hj
        cases j with
        | zero => exact hro 0 (by omega)
        | succ j =>
          have hrel := p_step A k x₀ j
          have he := congrArg (fun v => r (i+1) ⬝ᵥ v) hrel
          simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at he
          rw [hro (j+1) hj, hro j (by omega)] at he
          linarith
      have hcross : r (i+1) ⬝ᵥ (A *ᵥ p i) + b i * (p i ⬝ᵥ (A *ᵥ p i)) = 0 := by
        have he := congrArg (fun v => r (i+1) ⬝ᵥ v) (r_step A k x₀ i)
        simp only [dotProduct_sub, dotProduct_smul, hrrn i le_rfl] at he
        dsimp [cgA] at he ⊢
        field_simp at he ⊢
        nlinarith [he]
      have hconj : ∀ j ≤ i, p (i+1) ⬝ᵥ (A *ᵥ p j) = 0 := by
        intro j hj
        rw [p_step, add_dotProduct, smul_dotProduct, smul_eq_mul]
        by_cases he : j = i
        · subst j; exact hcross
        have hj' : j < i := by omega
        rw [hi.2.1 j hj', mul_zero, add_zero]
        by_cases hzj : r j = 0
        · rw [r_zero_p A k x₀ j hzj]; simp
        have hji := ih j (by omega)
        have hrrj := rr_ne hzj
        have hpj : p j ≠ 0 := by
          intro he; have hh := hji.2.2.1 j le_rfl
          rw [he, zero_dotProduct] at hh
          exact hrrj hh.symm
        have haj : a j ≠ 0 := div_ne_zero hrrj (ne_of_gt (pa_pos A hA hpj))
        have he := congrArg (fun v => r (i+1) ⬝ᵥ v) (r_step A k x₀ j)
        simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul] at he
        rw [hrrn j hj, hrrn (j+1) (by omega)] at he
        exact (mul_eq_zero.mp (by linarith : a j * (r (i+1) ⬝ᵥ (A *ᵥ p j)) = 0)).resolve_left haj
      refine ⟨fun j hj => hrrn j (by omega), fun j hj => hconj j (by omega), ?_, ?_⟩
      · intro j hj
        rw [p_step, add_dotProduct, smul_dotProduct, smul_eq_mul]
        by_cases he : j = i+1
        · subst j; rw [dotProduct_comm (p i) (r (i+1)), hro i le_rfl]; ring
        · rw [hrrn j (by omega), hi.2.2.1 j (by omega)]
          dsimp; field_simp <;> ring
      · intro j hj
        rw [dotProduct_comm]; exact hro j (by omega)
private theorem rr_orth (hA : A.PosDef) (i j : ℕ) (hij : i ≠ j) :
    r i ⬝ᵥ r j = 0 := by
  rcases lt_or_gt_of_ne hij with hij | hij
  · rw [dotProduct_comm]; exact (invariant A k x₀ hA j).1 i hij
  · exact (invariant A k x₀ hA i).1 j hij
private theorem pp_conj (hA : A.PosDef) (i j : ℕ) (hij : i ≠ j) :
    p i ⬝ᵥ (A *ᵥ p j) = 0 := by
  rcases lt_or_gt_of_ne hij with hij | hij
  · rw [asymm A hA]; exact (invariant A k x₀ hA j).2.1 i hij
  · exact (invariant A k x₀ hA i).2.1 j hij
private theorem residual (i : ℕ) : r i = k - A *ᵥ (cgIter A k x₀ i).x := by
  induction i with
  | zero => rfl
  | succ i hi =>
    rw [r_step, hi]
    change _ = k - A *ᵥ ((cgIter A k x₀ i).x + a i • p i)
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]; abel
private theorem rpA_self (hA : A.PosDef) (i : ℕ) :
    r i ⬝ᵥ (A *ᵥ p i) = p i ⬝ᵥ (A *ᵥ p i) := by
  cases i with
  | zero => rfl
  | succ i =>
    have he := congrArg (fun v => v ⬝ᵥ (A *ᵥ p (i+1))) (p_step A k x₀ i)
    rw [add_dotProduct, smul_dotProduct, pp_conj A k x₀ hA i (i+1) (by omega)] at he
    simpa using he.symm
private theorem rpA_other (hA : A.PosDef) (i j : ℕ) (hij : i ≠ j)
    (hij1 : i ≠ j+1) : r i ⬝ᵥ (A *ᵥ p j) = 0 := by
  cases i with
  | zero => exact pp_conj A k x₀ hA 0 j hij
  | succ i =>
    have he := congrArg (fun v => v ⬝ᵥ (A *ᵥ p j)) (p_step A k x₀ i)
    rw [add_dotProduct, smul_dotProduct, pp_conj A k x₀ hA (i+1) j hij,
      pp_conj A k x₀ hA i j (by omega)] at he
    simpa using he.symm

private theorem exists_zero (hA : A.PosDef) : ∃ m ≤ n, r m = 0 := by
  classical
  by_contra! hz
  have hli : LinearIndependent ℝ (fun i : Fin (n+1) => r i) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hd := congrArg (fun v => v ⬝ᵥ r i) hc
    simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] at hd
    have hs : (∑ j : Fin (n+1), c j * (r j ⬝ᵥ r i)) = c i * (r i ⬝ᵥ r i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [rr_orth A k x₀ hA j i (fun he => hji (Fin.ext he)), mul_zero]
      · simp
    rw [hs] at hd
    exact (mul_eq_zero.mp hd).resolve_right (rr_ne (hz i (by omega)))
  have hd := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one] at hd
  omega
private theorem terminates (hA : A.PosDef) (h : Fin n → ℝ) (hh : A *ᵥ h = k) :
    ∃ m ≤ n, (cgIter A k x₀ m).x = h := by
  obtain ⟨m, hm, hz⟩ := exists_zero A k x₀ hA
  refine ⟨m, hm, ?_⟩
  have hAx : A *ᵥ ((cgIter A k x₀ m).x - h) = 0 := by
    rw [Matrix.mulVec_sub, hh]
    have ht := residual A k x₀ m
    rw [hz] at ht
    exact sub_eq_zero.mpr (sub_eq_zero.mp ht.symm).symm
  have hx : (cgIter A k x₀ m).x - h = 0 := by
    by_contra hn
    have hp := pa_pos A hA hn
    rw [hAx, dotProduct_zero] at hp
    exact lt_irrefl _ hp
  exact sub_eq_zero.mp hx

private theorem direction_inner (hA : A.PosDef) (i j : ℕ) (hij : i ≤ j) :
    p i ⬝ᵥ p j = (r j ⬝ᵥ r j) * (p i ⬝ᵥ p i) / (r i ⬝ᵥ r i) := by
  by_cases hz : r i = 0
  · rw [r_zero_p A k x₀ i hz]; simp
  have hrr := rr_ne hz
  induction j, hij using Nat.le_induction with
  | base => field_simp
  | succ j hj ih =>
    by_cases hzj : r j = 0
    · have hpj := r_zero_p A k x₀ j hzj
      have hrn : r (j+1) = 0 := by rw [r_step, hpj, hzj]; simp
      rw [r_zero_p A k x₀ (j+1) hrn, hrn]; simp
    have hrrj := rr_ne hzj
    rw [p_step, dotProduct_add, dotProduct_smul, smul_eq_mul,
      (invariant A k x₀ hA (j+1)).2.2.2 i (by omega), ih]
    dsimp; field_simp <;> ring
private theorem zero_stable (i : ℕ) (hi : r i = 0) (j : ℕ) (hij : i ≤ j) :
    r j = 0 ∧ (cgIter A k x₀ j).x = (cgIter A k x₀ i).x := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨hi, rfl⟩
  | succ j hj ih =>
    have hp := r_zero_p A k x₀ j ih.1
    constructor
    · rw [r_step, ih.1, hp]; simp
    · change (cgIter A k x₀ j).x + a j • p j = _
      rw [hp]; simpa using ih.2

end CGProof

open ConjGrad.Termination
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) :
    ∀ i j, i ≠ j → (cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ j).r = 0 := by
  exact CGProof.rr_orth A k x₀ hA
