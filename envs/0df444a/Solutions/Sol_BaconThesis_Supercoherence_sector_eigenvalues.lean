-- Prove2me | solution 1 for BaconThesis.Supercoherence.sector_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T22:58:39.024609+00:00
-- url     : https://prove2.me/submissions/2de87014-771e-4929-83b3-b5382c17cc67

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
import Definitions.Def_BaconThesis_Supercoherence_sectorSpectrum

open QMaxCutSDP.Rounding Matrix

namespace BaconThesis.Supercoherence.SolSE

open BaconThesis.Supercoherence

/-! ### Pauli-string calculus -/

lemma ps_mul {n : ℕ} (s t u : Fin n → Fin 4) (c : Fin n → ℂ)
    (h : ∀ i, pauli (s i) * pauli (t i) = c i • pauli (u i)) :
    pauliString s * pauliString t = (∏ i, c i) • pauliString u := by
  ext x y
  simp only [Matrix.mul_apply, pauliString, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.prod_mul_distrib]
  have key : ∀ i, pauli (s i) (x i) (y i) * 0 + ∑ z : Fin 2, pauli (s i) (x i) z * pauli (t i) z (y i)
      = c i * pauli (u i) (x i) (y i) := by
    intro i
    have := congrFun (congrFun (h i) (x i)) (y i)
    simpa [Matrix.mul_apply] using this
  simp only [mul_zero, zero_add] at key
  simp_rw [← key]
  rw [Finset.prod_univ_sum]
  simp [Finset.prod_mul_distrib]

/-- Action of a single Pauli: each row has one nonzero entry. -/
def fl (a : Fin 4) (r : Fin 2) : Fin 2 := if a = 0 ∨ a = 3 then r else 1 - r

def ph (a : Fin 4) (r : Fin 2) : ℂ :=
  if a = 0 ∨ a = 1 then 1
  else if a = 2 then (if r = 0 then -Complex.I else Complex.I)
  else (if r = 0 then 1 else -1)

lemma pauli_eq (a : Fin 4) (r c : Fin 2) : pauli a r c = if c = fl a r then ph a r else 0 := by
  fin_cases a <;> fin_cases r <;> fin_cases c <;> simp [pauli, fl, ph]

lemma mulVec_ps {n : ℕ} (s : Fin n → Fin 4) (v : State n) :
    pauliString s *ᵥ v = fun x => (∏ i, ph (s i) (x i)) * v (fun i => fl (s i) (x i)) := by
  ext x
  simp only [Matrix.mulVec, dotProduct, pauliString, pauli_eq]
  simp_rw [Finset.prod_ite_zero, Finset.mem_univ, true_implies, ← funext_iff, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ]
  simp


lemma ps_one {n : ℕ} : pauliString (fun _ : Fin n => (0 : Fin 4)) = 1 := by
  ext x y
  simp only [pauliString, pauli_eq, fl, ph]
  simp only [true_or, if_true, Finset.prod_ite_zero, Finset.mem_univ, true_implies,
    Finset.prod_const_one, Matrix.one_apply]
  simp only [← funext_iff, eq_comm]


/-! ### The operators -/

abbrev XA : Operator 4 := pauliString ![1, 1, 0, 0]
abbrev ZA : Operator 4 := pauliString ![0, 3, 3, 0]

lemma XX : XA * XA = 1 := by
  rw [ps_mul _ _ (fun _ => 0) (fun _ => 1) (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli])), ps_one]; simp

lemma ZZ : ZA * ZA = 1 := by
  rw [ps_mul _ _ (fun _ => 0) (fun _ => 1) (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli])), ps_one]; simp

lemma S1S1 : S1 * S1 = 1 := by
  rw [S1, ps_mul _ _ (fun _ => 0) (fun _ => 1) (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli])), ps_one]; simp

lemma S2S2 : S2 * S2 = 1 := by
  rw [S2, ps_mul _ _ (fun _ => 0) (fun _ => 1) (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli])), ps_one]; simp

lemma XZ : XA * ZA = -(ZA * XA) := by
  rw [ps_mul _ _ ![1, 2, 3, 0] ![1, -Complex.I, 1, 1] (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli])),
    ps_mul _ _ ![1, 2, 3, 0] ![1, Complex.I, 1, 1] (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli]))]
  simp [Fin.prod_univ_four]

lemma S1X : S1 * XA = XA * S1 := by
  rw [S1, ps_mul _ _ ![0, 0, 1, 1] (fun _ => 1) (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli])),
    ps_mul _ _ ![0, 0, 1, 1] (fun _ => 1) (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli]))]

lemma S2X : S2 * XA = XA * S2 := by
  rw [S2, ps_mul _ _ ![2, 2, 3, 3] ![Complex.I, Complex.I, 1, 1] (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli])),
    ps_mul _ _ ![2, 2, 3, 3] ![-Complex.I, -Complex.I, 1, 1] (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli]))]
  simp [Fin.prod_univ_four]

lemma S1Z : S1 * ZA = ZA * S1 := by
  rw [S1, ps_mul _ _ ![1, 2, 2, 1] ![1, -Complex.I, -Complex.I, 1] (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli])),
    ps_mul _ _ ![1, 2, 2, 1] ![1, Complex.I, Complex.I, 1] (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli]))]
  simp [Fin.prod_univ_four]

lemma S2Z : S2 * ZA = ZA * S2 := by
  rw [S2, ps_mul _ _ ![3, 0, 0, 3] (fun _ => 1) (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli])),
    ps_mul _ _ ![3, 0, 0, 3] (fun _ => 1) (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli]))]

lemma S1S2 : S1 * S2 = S2 * S1 := by
  rw [S1, S2, ps_mul _ _ (fun _ => 2) (fun _ => -Complex.I) (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli])),
    ps_mul _ _ (fun _ => 2) (fun _ => Complex.I) (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli]))]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show ((-Complex.I) ^ 4 : ℂ) = Complex.I ^ 4 by ring]

lemma hH : codeHamiltonian = XA + XA * S1 + ZA + ZA * S2 := by
  rw [S1, S2, ps_mul _ _ ![0, 0, 1, 1] (fun _ => 1) (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli])),
    ps_mul _ _ ![3, 0, 0, 3] (fun _ => 1) (by (intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [pauli]))]
  simp [codeHamiltonian]


/-! ### Concrete vectors -/

def bv (c : ℕ → ℂ) : State 4 :=
  fun x => c (8 * (x 0 : ℕ) + 4 * (x 1 : ℕ) + 2 * (x 2 : ℕ) + (x 3 : ℕ))

lemma forall_bits {P : (Fin 4 → Fin 2) → Prop} (h : ∀ a b c d : Fin 2, P ![a, b, c, d]) :
    ∀ x, P x := by
  intro x
  have : x = ![x 0, x 1, x 2, x 3] := by funext i; fin_cases i <;> rfl
  rw [this]; apply h


def L0 : State 4 := bv fun n => if n = 0 ∨ n = 15 then 1 else 0
def M0 : State 4 := bv fun n => if n = 1 ∨ n = 14 then 1 else 0
def N0 : State 4 := bv fun n => if n = 0 then 1 else if n = 15 then -1 else 0
def K0 : State 4 := bv fun n => if n = 1 then 1 else if n = 14 then -1 else 0

lemma S1L : S1 *ᵥ L0 = L0 := by rw [S1, L0]; (
    rw [mulVec_ps]
    funext x
    revert x
    apply forall_bits
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [bv, fl, ph, Fin.prod_univ_four])
lemma S2L : S2 *ᵥ L0 = L0 := by rw [S2, L0]; (
    rw [mulVec_ps]
    funext x
    revert x
    apply forall_bits
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [bv, fl, ph, Fin.prod_univ_four])
lemma ZL : ZA *ᵥ L0 = L0 := by rw [L0]; (
    rw [mulVec_ps]
    funext x
    revert x
    apply forall_bits
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [bv, fl, ph, Fin.prod_univ_four])
lemma S1M : S1 *ᵥ M0 = M0 := by rw [S1, M0]; (
    rw [mulVec_ps]
    funext x
    revert x
    apply forall_bits
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [bv, fl, ph, Fin.prod_univ_four])
lemma S2M : S2 *ᵥ M0 = (-1 : ℂ) • M0 := by rw [S2, M0]; (
    rw [mulVec_ps]
    funext x
    revert x
    apply forall_bits
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [bv, fl, ph, Fin.prod_univ_four])
lemma S1N : S1 *ᵥ N0 = (-1 : ℂ) • N0 := by rw [S1, N0]; (
    rw [mulVec_ps]
    funext x
    revert x
    apply forall_bits
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [bv, fl, ph, Fin.prod_univ_four])
lemma S2N : S2 *ᵥ N0 = N0 := by rw [S2, N0]; (
    rw [mulVec_ps]
    funext x
    revert x
    apply forall_bits
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [bv, fl, ph, Fin.prod_univ_four])
lemma ZN : ZA *ᵥ N0 = N0 := by rw [N0]; (
    rw [mulVec_ps]
    funext x
    revert x
    apply forall_bits
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [bv, fl, ph, Fin.prod_univ_four])
lemma S1K : S1 *ᵥ K0 = (-1 : ℂ) • K0 := by rw [S1, K0]; (
    rw [mulVec_ps]
    funext x
    revert x
    apply forall_bits
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [bv, fl, ph, Fin.prod_univ_four])
lemma S2K : S2 *ᵥ K0 = (-1 : ℂ) • K0 := by rw [S2, K0]; (
    rw [mulVec_ps]
    funext x
    revert x
    apply forall_bits
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [bv, fl, ph, Fin.prod_univ_four])

lemma XL_at : (XA *ᵥ L0) ![1, 1, 0, 0] = 1 := by rw [mulVec_ps]; simp [L0, bv, fl, ph, Fin.prod_univ_four]
lemma L_at : L0 ![1, 1, 0, 0] = 0 := by simp [L0, bv]
lemma XM_at : (XA *ᵥ M0) ![1, 1, 0, 1] = 1 := by rw [mulVec_ps]; simp [M0, bv, fl, ph, Fin.prod_univ_four]
lemma M_at : M0 ![1, 1, 0, 1] = 0 := by simp [M0, bv]
lemma XN_at : (XA *ᵥ N0) ![1, 1, 0, 0] = 1 := by rw [mulVec_ps]; simp [N0, bv, fl, ph, Fin.prod_univ_four]
lemma N_at : N0 ![0, 0, 0, 0] = 1 := by simp [N0, bv]
lemma K_at : K0 ![0, 0, 0, 1] = 1 := by simp [K0, bv]


/-! ### Sector algebra -/

lemma comm_vec {A B : Operator 4} (h : A * B = B * A) (v : State 4) (c : ℂ)
    (hv : A *ᵥ v = c • v) : A *ᵥ (B *ᵥ v) = c • (B *ᵥ v) := by
  rw [mulVec_mulVec, h, ← mulVec_mulVec, hv, mulVec_smul]

lemma inv_vec {A : Operator 4} (h : A * A = 1) (v : State 4) : A *ᵥ (A *ᵥ v) = v := by
  rw [mulVec_mulVec, h, one_mulVec]

lemma ZX_vec (v : State 4) : ZA *ᵥ (XA *ᵥ v) = -(XA *ᵥ (ZA *ᵥ v)) := by
  rw [mulVec_mulVec, mulVec_mulVec, XZ, neg_mulVec, neg_neg]

lemma H_vec {v : State 4} {s1 s2 : ℂ} (h1 : S1 *ᵥ v = s1 • v) (h2 : S2 *ᵥ v = s2 • v) :
    codeHamiltonian *ᵥ v = (1 + s1) • (XA *ᵥ v) + (1 + s2) • (ZA *ᵥ v) := by
  rw [hH]
  simp only [add_mulVec, ← mulVec_mulVec, h1, h2, mulVec_smul]
  module

lemma ne_zero_of_at {v : State 4} (x : Fin 4 → Fin 2) (h : v x ≠ 0) : v ≠ 0 := by
  rintro rfl; exact h rfl

lemma eq_of_smul {v : State 4} (hv : v ≠ 0) {a b : ℂ} (h : a • v = b • v) : a = b := by
  by_contra hab
  apply hv
  have : (a - b) • v = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hab)

lemma mem11 (l : ℂ) (hl : l * l = 2) : 2 * l ∈ sectorSpectrum 1 1 := by
  set v := (1 + l) • L0 + XA *ᵥ L0
  have hS1 : S1 *ᵥ v = (1 : ℂ) • v := by
    simp only [v, mulVec_add, mulVec_smul, S1L, comm_vec S1X L0 1 (by rw [S1L, one_smul]),
      one_smul]
  have hS2 : S2 *ᵥ v = (1 : ℂ) • v := by
    simp only [v, mulVec_add, mulVec_smul, S2L, comm_vec S2X L0 1 (by rw [S2L, one_smul]),
      one_smul]
  refine ⟨v, ne_zero_of_at ![1, 1, 0, 0] ?_, hS1, hS2, ?_⟩
  · simp [v, XL_at, L_at]
  · rw [H_vec hS1 hS2]
    simp only [v, mulVec_add, mulVec_smul, inv_vec XX, ZL, ZX_vec]
    linear_combination (norm := module) (2 : ℂ) • ((hl.symm) • L0)

lemma mem1m (e : ℂ) (he : e * e = 1) : 2 * e ∈ sectorSpectrum 1 (-1) := by
  set v := M0 + e • (XA *ᵥ M0)
  have hS1 : S1 *ᵥ v = (1 : ℂ) • v := by
    simp only [v, mulVec_add, mulVec_smul, S1M, comm_vec S1X M0 1 (by rw [S1M, one_smul]),
      one_smul]
  have hS2 : S2 *ᵥ v = (-1 : ℂ) • v := by
    simp only [v, mulVec_add, mulVec_smul, S2M, comm_vec S2X M0 (-1) S2M]
    module
  refine ⟨v, ne_zero_of_at ![1, 1, 0, 1] ?_, hS1, hS2, ?_⟩
  · simp only [v, Pi.add_apply, Pi.smul_apply, XM_at, M_at, smul_eq_mul, mul_one, zero_add]
    rintro rfl; simp at he
  · rw [H_vec hS1 hS2]
    simp only [v, mulVec_add, mulVec_smul, inv_vec XX]
    linear_combination (norm := module) (-2 : ℂ) • (he • (XA *ᵥ M0))

lemma memm1_pos : (2 : ℂ) ∈ sectorSpectrum (-1) 1 := by
  refine ⟨N0, ne_zero_of_at ![0, 0, 0, 0] (by simp [N_at]), S1N, by rw [S2N, one_smul], ?_⟩
  rw [H_vec S1N (by rw [S2N, one_smul]), ZN]
  module

lemma memm1_neg : (-2 : ℂ) ∈ sectorSpectrum (-1) 1 := by
  have h1 : S1 *ᵥ (XA *ᵥ N0) = (-1 : ℂ) • (XA *ᵥ N0) := comm_vec S1X N0 (-1) S1N
  have h2 : S2 *ᵥ (XA *ᵥ N0) = (1 : ℂ) • (XA *ᵥ N0) :=
    comm_vec S2X N0 1 (by rw [S2N, one_smul])
  refine ⟨XA *ᵥ N0, ne_zero_of_at ![1, 1, 0, 0] (by simp [XN_at]), h1, h2, ?_⟩
  rw [H_vec h1 h2, ZX_vec, ZN]
  module

lemma memmm : (0 : ℂ) ∈ sectorSpectrum (-1) (-1) := by
  refine ⟨K0, ne_zero_of_at ![0, 0, 0, 1] (by simp [K_at]), S1K, S2K, ?_⟩
  rw [H_vec S1K S2K]
  module

lemma sub11 {μ : ℂ} (h : μ ∈ sectorSpectrum 1 1) : μ * μ = 8 := by
  obtain ⟨v, hv, h1, h2, hHv⟩ := h
  rw [H_vec h1 h2] at hHv
  have hw : XA *ᵥ (XA *ᵥ v + ZA *ᵥ v) + ZA *ᵥ (XA *ᵥ v + ZA *ᵥ v) = (2 : ℂ) • v := by
    simp only [mulVec_add, inv_vec XX, inv_vec ZZ, ZX_vec]
    module
  have hHv' : (2 : ℂ) • (XA *ᵥ v + ZA *ᵥ v) = μ • v := by rw [← hHv]; module
  have e1 : XA *ᵥ (μ • v) + ZA *ᵥ (μ • v) = μ • (XA *ᵥ v + ZA *ᵥ v) := by
    simp only [mulVec_smul, smul_add]
  have e2 : XA *ᵥ ((2 : ℂ) • (XA *ᵥ v + ZA *ᵥ v)) + ZA *ᵥ ((2 : ℂ) • (XA *ᵥ v + ZA *ᵥ v)) =
      (4 : ℂ) • v := by
    rw [mulVec_smul, mulVec_smul, ← smul_add, hw, smul_smul]; norm_num
  have e3 : μ • (XA *ᵥ v + ZA *ᵥ v) = (4 : ℂ) • v := by rw [← e1, ← hHv', e2]
  have : (μ * μ) • v = (8 : ℂ) • v := by
    rw [← smul_smul, ← hHv', smul_comm, e3, smul_smul]; norm_num
  exact eq_of_smul hv this

lemma sub_one {A : Operator 4} (hA : A * A = 1) {μ : ℂ} {v : State 4} (hv : v ≠ 0)
    (hHv : (2 : ℂ) • (A *ᵥ v) = μ • v) : μ * μ = 4 := by
  have e3 : μ • (A *ᵥ v) = (2 : ℂ) • v := by
    have := congrArg (A *ᵥ ·) hHv
    simp only [mulVec_smul, inv_vec hA] at this
    exact this.symm
  have : (μ * μ) • v = (4 : ℂ) • v := by
    rw [← smul_smul, ← hHv, smul_comm, e3, smul_smul]; norm_num
  exact eq_of_smul hv this

lemma sub1m {μ : ℂ} (h : μ ∈ sectorSpectrum 1 (-1)) : μ * μ = 4 := by
  obtain ⟨v, hv, h1, h2, hHv⟩ := h
  rw [H_vec h1 h2] at hHv
  exact sub_one XX hv (by rw [← hHv]; module)

lemma subm1 {μ : ℂ} (h : μ ∈ sectorSpectrum (-1) 1) : μ * μ = 4 := by
  obtain ⟨v, hv, h1, h2, hHv⟩ := h
  rw [H_vec h1 h2] at hHv
  exact sub_one ZZ hv (by rw [← hHv]; module)

lemma submm {μ : ℂ} (h : μ ∈ sectorSpectrum (-1) (-1)) : μ = 0 := by
  obtain ⟨v, hv, h1, h2, hHv⟩ := h
  rw [H_vec h1 h2] at hHv
  exact (eq_of_smul hv (show μ • v = (0 : ℂ) • v by rw [← hHv]; module))

lemma sq2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma sector_eq :
    sectorSpectrum 1 1 = {((2 * Real.sqrt 2 : ℝ) : ℂ), ((-(2 * Real.sqrt 2) : ℝ) : ℂ)} ∧
      sectorSpectrum 1 (-1) = {2, -2} ∧ sectorSpectrum (-1) 1 = {2, -2} ∧
      sectorSpectrum (-1) (-1) = {0} := by
  have pm2 : ∀ μ : ℂ, μ * μ = 4 → μ = 2 ∨ μ = -2 := fun μ h => by
    have : (μ - 2) * (μ + 2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext μ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have h8 := sub11 h
      have : (μ - ((2 * Real.sqrt 2 : ℝ) : ℂ)) * (μ - ((-(2 * Real.sqrt 2) : ℝ) : ℂ)) = 0 := by
        push_cast; linear_combination h8 - 4 * sq2
      rcases mul_eq_zero.mp this with h | h
      · left; linear_combination h
      · right; linear_combination h
    · rintro (rfl | rfl)
      · have := mem11 _ sq2; push_cast; exact this
      · have := mem11 (-((Real.sqrt 2 : ℝ) : ℂ)) (by rw [neg_mul_neg, sq2])
        push_cast; convert this using 1; ring
  · ext μ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    refine ⟨fun h => pm2 μ (sub1m h), ?_⟩
    rintro (rfl | rfl)
    · simpa using mem1m 1 (by norm_num)
    · simpa using mem1m (-1) (by norm_num)
  · ext μ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨fun h => pm2 μ (subm1 h), by rintro (rfl | rfl); exacts [memm1_pos, memm1_neg]⟩
  · ext μ
    simp only [Set.mem_singleton_iff]
    exact ⟨submm, by rintro rfl; exact memmm⟩

end BaconThesis.Supercoherence.SolSE

open BaconThesis.Supercoherence in
theorem solution :
    sectorSpectrum 1 1 = {((2 * Real.sqrt 2 : ℝ) : ℂ), ((-(2 * Real.sqrt 2) : ℝ) : ℂ)} ∧
      sectorSpectrum 1 (-1) = {2, -2} ∧ sectorSpectrum (-1) 1 = {2, -2} ∧
      sectorSpectrum (-1) (-1) = {0} :=
  BaconThesis.Supercoherence.SolSE.sector_eq
