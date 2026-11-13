-- Prove2me | solution 1 for BaconThesis.Supercoherence.codeHamiltonian_supercoherent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T09:05:20.370898+00:00
-- url     : https://prove2.me/submissions/68fc4843-7ca6-4691-bfdd-212c20626d3a

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
import Definitions.Def_BaconThesis_Supercoherence_codeHamiltonian
import Definitions.Def_BaconThesis_Supercoherence_groundSpace
import Definitions.Def_BaconThesis_Supercoherence_IsGroundEnergy
import Definitions.Def_BaconThesis_Supercoherence_IsSupercoherent

set_option autoImplicit false

open scoped ComplexOrder

open QMaxCutSDP.Rounding Matrix BaconThesis.Supercoherence

namespace BCS502

def fl : Fin 2 → Fin 2 := ![1, 0]
def sg : Fin 2 → ℂ := ![1, -1]
def pσ (a : Fin 4) (u : Fin 2) : Fin 2 := if a = 1 ∨ a = 2 then fl u else u
def pc (a : Fin 4) (u : Fin 2) : ℂ :=
  if a = 0 then 1 else if a = 1 then 1 else if a = 2 then ![-Complex.I, Complex.I] u else sg u
def cm (a b : Fin 4) : ℂ := if a = 0 ∨ b = 0 ∨ a = b then 1 else -1

lemma fl0 : fl 0 = 1 := rfl
lemma fl1 : fl 1 = 0 := rfl
lemma sg0 : sg 0 = 1 := rfl
lemma sg1 : sg 1 = -1 := rfl

lemma pauli_eq (a : Fin 4) (u w : Fin 2) :
    pauli a u w = if w = pσ a u then pc a u else 0 := by
  fin_cases a <;> fin_cases u <;> fin_cases w <;> simp [pauli, pσ, pc, fl, sg]

lemma pauli_star (a : Fin 4) (u w : Fin 2) : star (pauli a w u) = pauli a u w := by
  fin_cases a <;> fin_cases u <;> fin_cases w <;> simp [pauli]

lemma pσ_pσ_self (a : Fin 4) (u : Fin 2) : pσ a (pσ a u) = u := by
  fin_cases a <;> fin_cases u <;> simp [pσ, fl]

lemma pc_self (a : Fin 4) (u : Fin 2) : pc a u * pc a (pσ a u) = 1 := by
  fin_cases a <;> fin_cases u <;> simp [pc, pσ, fl, sg]

lemma pσ_comm (a b : Fin 4) (u : Fin 2) : pσ b (pσ a u) = pσ a (pσ b u) := by
  fin_cases a <;> fin_cases b <;> fin_cases u <;> simp [pσ, fl]

lemma pc_comm (a b : Fin 4) (u : Fin 2) :
    pc a u * pc b (pσ a u) = cm a b * (pc b u * pc a (pσ b u)) := by
  fin_cases a <;> fin_cases b <;> fin_cases u <;> simp [pc, pσ, fl, sg, cm]

lemma pauliString_apply {n : ℕ} (s : Fin n → Fin 4) (x y : Fin n → Fin 2) :
    pauliString s x y = if y = (fun i => pσ (s i) (x i)) then ∏ i, pc (s i) (x i) else 0 := by
  simp only [pauliString, pauli_eq]
  by_cases h : y = (fun i => pσ (s i) (x i))
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ pσ (s i) (x i) := by
      by_contra hc; exact h (funext fun i => not_not.mp fun hi => hc ⟨i, hi⟩)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma pauliString_mulVec {n : ℕ} (s : Fin n → Fin 4) (v : (Fin n → Fin 2) → ℂ)
    (x : Fin n → Fin 2) :
    (pauliString s *ᵥ v) x = (∏ i, pc (s i) (x i)) * v (fun i => pσ (s i) (x i)) := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single (fun i => pσ (s i) (x i))]
  · rw [pauliString_apply, if_pos rfl]
  · intro y _ hy; rw [pauliString_apply, if_neg hy, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma pauliString_mul_apply {n : ℕ} (s t : Fin n → Fin 4) (x y : Fin n → Fin 2) :
    (pauliString s * pauliString t) x y =
      if y = (fun i => pσ (t i) (pσ (s i) (x i))) then
        ∏ i, (pc (s i) (x i) * pc (t i) (pσ (s i) (x i))) else 0 := by
  rw [mul_apply, Finset.sum_eq_single (fun i => pσ (s i) (x i))]
  · rw [pauliString_apply s x, if_pos rfl, pauliString_apply t, Finset.prod_mul_distrib, mul_ite,
      mul_zero]
  · intro j _ hj; rw [pauliString_apply s x j, if_neg hj, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma pauliString_mul_self {n : ℕ} (s : Fin n → Fin 4) :
    pauliString s * pauliString s = (1 : Operator n) := by
  ext x y
  rw [pauliString_mul_apply, one_apply]
  simp only [pσ_pσ_self, pc_self, Finset.prod_const_one]
  by_cases h : x = y
  · subst h; simp
  · have h' : ¬ (y = fun i => x i) := fun e => h (funext fun i => (congrFun e i).symm)
    rw [if_neg h', if_neg h]

lemma pauliString_mul_comm {n : ℕ} (s t : Fin n → Fin 4) :
    pauliString s * pauliString t = (∏ i, cm (s i) (t i)) • (pauliString t * pauliString s) := by
  ext x y
  rw [Matrix.smul_apply, pauliString_mul_apply, pauliString_mul_apply]
  have hσ : (fun i => pσ (t i) (pσ (s i) (x i))) = (fun i => pσ (s i) (pσ (t i) (x i))) :=
    funext fun i => pσ_comm _ _ _
  rw [hσ, Finset.prod_congr rfl (fun i _ => pc_comm (s i) (t i) (x i))]
  split_ifs <;> simp [Finset.prod_mul_distrib, smul_eq_mul]

lemma pauliString_herm {n : ℕ} (s : Fin n → Fin 4) :
    (pauliString s : Operator n)ᴴ = pauliString s := by
  ext x y
  simp only [conjTranspose_apply, pauliString, star_prod, pauli_star]

lemma eta4 (x : Fin 4 → Fin 2) : x = ![x 0, x 1, x 2, x 3] := by
  funext i; fin_cases i <;> rfl

lemma forall4 {P : (Fin 4 → Fin 2) → Prop} (h : ∀ a b c d, P ![a, b, c, d]) : ∀ x, P x :=
  fun x => by rw [eta4 x]; exact h _ _ _ _

lemma sum16 (f : (Fin 4 → Fin 2) → ℂ) :
    ∑ x, f x = ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2, f ![a, b, c, d] := by
  let e : (Fin 2 × Fin 2 × Fin 2 × Fin 2) ≃ (Fin 4 → Fin 2) :=
    { toFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
      invFun := fun x => (x 0, x 1, x 2, x 3)
      left_inv := fun p => rfl
      right_inv := fun x => (eta4 x).symm }
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

lemma act {s : Fin 4 → Fin 4} (v : (Fin 4 → Fin 2) → ℂ) (a b c d : Fin 2) :
    (pauliString s *ᵥ v) ![a, b, c, d] =
      (pc (s 0) a * pc (s 1) b * pc (s 2) c * pc (s 3) d) *
        v ![pσ (s 0) a, pσ (s 1) b, pσ (s 2) c, pσ (s 3) d] := by
  rw [pauliString_mulVec, Fin.prod_univ_four]
  congr 2
  funext i; fin_cases i <;> rfl

noncomputable def SA : Operator 4 := pauliString ![1, 1, 0, 0]
noncomputable def SB : Operator 4 := pauliString ![0, 0, 1, 1]
noncomputable def SC : Operator 4 := pauliString ![0, 3, 3, 0]
noncomputable def SD : Operator 4 := pauliString ![3, 0, 0, 3]

lemma hcode : codeHamiltonian = SA + SB + SC + SD := rfl

lemma SA_act (v : (Fin 4 → Fin 2) → ℂ) (a b c d : Fin 2) :
    (SA *ᵥ v) ![a, b, c, d] = v ![fl a, fl b, c, d] := by
  rw [SA, act]; simp [pc, pσ]

lemma SB_act (v : (Fin 4 → Fin 2) → ℂ) (a b c d : Fin 2) :
    (SB *ᵥ v) ![a, b, c, d] = v ![a, b, fl c, fl d] := by
  rw [SB, act]; simp [pc, pσ]

lemma SC_act (v : (Fin 4 → Fin 2) → ℂ) (a b c d : Fin 2) :
    (SC *ᵥ v) ![a, b, c, d] = sg b * sg c * v ![a, b, c, d] := by
  rw [SC, act]; simp [pc, pσ]

lemma SD_act (v : (Fin 4 → Fin 2) → ℂ) (a b c d : Fin 2) :
    (SD *ᵥ v) ![a, b, c, d] = sg a * sg d * v ![a, b, c, d] := by
  rw [SD, act]; simp [pc, pσ]

lemma H_act (v : (Fin 4 → Fin 2) → ℂ) (a b c d : Fin 2) :
    (codeHamiltonian *ᵥ v) ![a, b, c, d] = v ![fl a, fl b, c, d] + v ![a, b, fl c, fl d] +
      sg b * sg c * v ![a, b, c, d] + sg a * sg d * v ![a, b, c, d] := by
  rw [hcode]; simp only [add_mulVec, Pi.add_apply, SA_act, SB_act, SC_act, SD_act]

noncomputable def sq2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

lemma sq2_mul : sq2 * sq2 = 2 := by
  unfold sq2; rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma sq2_mul' : 2 * sq2 * sq2 = 4 := by
  rw [mul_assoc, sq2_mul]; norm_num

lemma sq2_star : star sq2 = sq2 := by unfold sq2; simp

lemma sq2_conj : (starRingEnd ℂ) sq2 = sq2 := by unfold sq2; simp

lemma sq2_ne : sq2 ≠ 0 := by unfold sq2; simp

lemma hE : (((-(2 * Real.sqrt 2)) : ℝ) : ℂ) = -(2 * sq2) := by unfold sq2; push_cast; ring

noncomputable def N1 : Operator 4 := sq2 • (1 : Operator 4) + SA + SC
noncomputable def N2 : Operator 4 := sq2 • (1 : Operator 4) + SB + SD

lemma N1_herm : N1ᴴ = N1 := by
  simp [N1, conjTranspose_add, conjTranspose_smul, sq2_star, SA, SC, pauliString_herm]

lemma N2_herm : N2ᴴ = N2 := by
  simp [N2, conjTranspose_add, conjTranspose_smul, sq2_star, SB, SD, pauliString_herm]

lemma hAC : SA * SC = -(SC * SA) := by
  have h := pauliString_mul_comm (![1, 1, 0, 0] : Fin 4 → Fin 4) ![0, 3, 3, 0]
  have hp : (∏ i, cm ((![1, 1, 0, 0] : Fin 4 → Fin 4) i) ((![0, 3, 3, 0] : Fin 4 → Fin 4) i))
      = -1 := by simp [Fin.prod_univ_four, cm]
  rw [SA, SC, h, hp, neg_one_smul]

lemma hBD : SB * SD = -(SD * SB) := by
  have h := pauliString_mul_comm (![0, 0, 1, 1] : Fin 4 → Fin 4) ![3, 0, 0, 3]
  have hp : (∏ i, cm ((![0, 0, 1, 1] : Fin 4 → Fin 4) i) ((![3, 0, 0, 3] : Fin 4 → Fin 4) i))
      = -1 := by simp [Fin.prod_univ_four, cm]
  rw [SB, SD, h, hp, neg_one_smul]

lemma N1_sq : N1 * N1 = (2 * sq2) • N1 := by
  have hAA : SA * SA = 1 := pauliString_mul_self _
  have hCC : SC * SC = 1 := pauliString_mul_self _
  simp only [N1, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hAA, hCC,
    hAC, smul_smul, sq2_mul, sq2_mul', smul_add]
  module

lemma N2_sq : N2 * N2 = (2 * sq2) • N2 := by
  have hBB : SB * SB = 1 := pauliString_mul_self _
  have hDD : SD * SD = 1 := pauliString_mul_self _
  simp only [N2, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hBB, hDD,
    hBD, smul_smul, sq2_mul, sq2_mul', smul_add]
  module

lemma hH : codeHamiltonian = N1 + N2 - (2 * sq2) • (1 : Operator 4) := by
  rw [hcode]; simp only [N1, N2]; module

lemma nsq (N : Operator 4) (hN : Nᴴ = N) (hsq : N * N = (2 * sq2) • N)
    (v : (Fin 4 → Fin 2) → ℂ) :
    star (N *ᵥ v) ⬝ᵥ (N *ᵥ v) = 2 * sq2 * (star v ⬝ᵥ (N *ᵥ v)) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hN, hsq, smul_mulVec, dotProduct_smul,
    smul_eq_mul]

lemma quad (v : (Fin 4 → Fin 2) → ℂ) :
    2 * sq2 * (star v ⬝ᵥ (codeHamiltonian *ᵥ v)) + 2 * sq2 * (2 * sq2) * (star v ⬝ᵥ v) =
      star (N1 *ᵥ v) ⬝ᵥ (N1 *ᵥ v) + star (N2 *ᵥ v) ⬝ᵥ (N2 *ᵥ v) := by
  rw [nsq N1 N1_herm N1_sq, nsq N2 N2_herm N2_sq, hH]
  simp only [sub_mulVec, add_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  ring

lemma cnonneg {z : ℂ} (h : 0 ≤ z) : 0 ≤ z.re ∧ z.im = 0 := by
  obtain ⟨h1, h2⟩ := Complex.le_def.mp h
  exact ⟨by simpa using h1, by simpa using h2.symm⟩

lemma mem_gs {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (E : ℝ) (v : ι → ℂ) :
    v ∈ groundSpace H E ↔ H *ᵥ v = (E : ℂ) • v := by
  unfold groundSpace
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]

lemma lower (μ : ℂ) (v : (Fin 4 → Fin 2) → ℂ) (hv0 : v ≠ 0)
    (hv : codeHamiltonian *ᵥ v = μ • v) : -(2 * Real.sqrt 2) ≤ μ.re := by
  have q := quad v
  rw [hv, dotProduct_smul, smul_eq_mul] at q
  obtain ⟨n1r, n1i⟩ := cnonneg (dotProduct_star_self_nonneg (N1 *ᵥ v))
  obtain ⟨n2r, n2i⟩ := cnonneg (dotProduct_star_self_nonneg (N2 *ᵥ v))
  obtain ⟨pr, pim⟩ := cnonneg (dotProduct_star_self_nonneg v)
  have hP0 : star v ⬝ᵥ v ≠ 0 := fun h => hv0 (dotProduct_star_self_eq_zero.mp h)
  have ppos : 0 < (star v ⬝ᵥ v).re :=
    lt_of_le_of_ne pr (fun h => hP0 (Complex.ext h.symm pim))
  have hre := congrArg Complex.re q
  simp [sq2, Complex.mul_re, Complex.mul_im, pim] at hre
  have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have key : 0 ≤ (2 * Real.sqrt 2 * (star v ⬝ᵥ v).re) * (μ.re + 2 * Real.sqrt 2) := by
    nlinarith
  have := (mul_nonneg_iff_of_pos_left (by positivity)).mp key
  linarith

lemma gs_N (v : (Fin 4 → Fin 2) → ℂ)
    (hv : v ∈ groundSpace codeHamiltonian (-(2 * Real.sqrt 2))) :
    N1 *ᵥ v = 0 ∧ N2 *ᵥ v = 0 := by
  rw [mem_gs, hE] at hv
  have q := quad v
  rw [hv, dotProduct_smul, smul_eq_mul] at q
  have hsum : star (N1 *ᵥ v) ⬝ᵥ (N1 *ᵥ v) + star (N2 *ᵥ v) ⬝ᵥ (N2 *ᵥ v) = 0 := by
    linear_combination (-1 : ℂ) * q
  obtain ⟨n1r, n1i⟩ := cnonneg (dotProduct_star_self_nonneg (N1 *ᵥ v))
  obtain ⟨n2r, n2i⟩ := cnonneg (dotProduct_star_self_nonneg (N2 *ᵥ v))
  have hre := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.zero_re] at hre
  have e1 : star (N1 *ᵥ v) ⬝ᵥ (N1 *ᵥ v) = 0 :=
    Complex.ext (by simp only [Complex.zero_re]; linarith) (by simp only [Complex.zero_im]; exact n1i)
  have e2 : star (N2 *ᵥ v) ⬝ᵥ (N2 *ᵥ v) = 0 :=
    Complex.ext (by simp only [Complex.zero_re]; linarith) (by simp only [Complex.zero_im]; exact n2i)
  exact ⟨dotProduct_star_self_eq_zero.mp e1, dotProduct_star_self_eq_zero.mp e2⟩

lemma N1_act (v : (Fin 4 → Fin 2) → ℂ) (a b c d : Fin 2) :
    (N1 *ᵥ v) ![a, b, c, d] =
      sq2 * v ![a, b, c, d] + v ![fl a, fl b, c, d] + sg b * sg c * v ![a, b, c, d] := by
  simp only [N1, add_mulVec, smul_mulVec, one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    SA_act, SC_act]

lemma N2_act (v : (Fin 4 → Fin 2) → ℂ) (a b c d : Fin 2) :
    (N2 *ᵥ v) ![a, b, c, d] =
      sq2 * v ![a, b, c, d] + v ![a, b, fl c, fl d] + sg a * sg d * v ![a, b, c, d] := by
  simp only [N2, add_mulVec, smul_mulVec, one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    SB_act, SD_act]

noncomputable def g1 (x : Fin 4 → Fin 2) : ℂ :=
  if x 0 = x 1 ∧ x 2 = x 3 then (if x 1 = x 2 then 1 else -(1 + sq2)) else 0

noncomputable def g2 (x : Fin 4 → Fin 2) : ℂ :=
  if x 0 ≠ x 1 ∧ x 2 ≠ x 3 then (if x 0 = x 2 then 1 else 1 - sq2) else 0

set_option maxHeartbeats 1000000 in
lemma g1_mem : g1 ∈ groundSpace codeHamiltonian (-(2 * Real.sqrt 2)) := by
  rw [mem_gs, hE]
  funext x; revert x
  apply forall4
  intro a b c d
  rw [H_act, Pi.smul_apply, smul_eq_mul]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [g1, fl, sg] <;>
    first | ring1 | linear_combination (-2 : ℂ) * sq2_mul | linear_combination (2 : ℂ) * sq2_mul

set_option maxHeartbeats 1000000 in
lemma g2_mem : g2 ∈ groundSpace codeHamiltonian (-(2 * Real.sqrt 2)) := by
  rw [mem_gs, hE]
  funext x; revert x
  apply forall4
  intro a b c d
  rw [H_act, Pi.smul_apply, smul_eq_mul]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [g2, fl, sg] <;>
    first | ring1 | linear_combination (-2 : ℂ) * sq2_mul | linear_combination (2 : ℂ) * sq2_mul

set_option maxHeartbeats 1000000 in
lemma gs_zero (w : (Fin 4 → Fin 2) → ℂ)
    (hw : w ∈ groundSpace codeHamiltonian (-(2 * Real.sqrt 2)))
    (h0 : w ![0, 0, 0, 0] = 0) (h5 : w ![0, 1, 0, 1] = 0) : w = 0 := by
  obtain ⟨hN1, hN2⟩ := gs_N w hw
  have E : ∀ a b c d : Fin 2,
      sq2 * w ![a, b, c, d] + w ![fl a, fl b, c, d] + sg b * sg c * w ![a, b, c, d] = 0 := by
    intro a b c d; rw [← N1_act, hN1]; rfl
  have F : ∀ a b c d : Fin 2,
      sq2 * w ![a, b, c, d] + w ![a, b, fl c, fl d] + sg a * sg d * w ![a, b, c, d] = 0 := by
    intro a b c d; rw [← N2_act, hN2]; rfl
  have E0000 := E 0 0 0 0
  have F0000 := F 0 0 0 0
  have F1100 := F 1 1 0 0
  have E0101 := E 0 1 0 1
  have F0101 := F 0 1 0 1
  have F1001 := F 1 0 0 1
  have E1000 := E 1 0 0 0
  have F0100 := F 0 1 0 0
  have F1000 := F 1 0 0 0
  have E1011 := E 1 0 1 1
  have E0001 := E 0 0 0 1
  have F1101 := F 1 1 0 1
  have F0001 := F 0 0 0 1
  have E0010 := E 0 0 1 0
  simp only [fl0, fl1, sg0, sg1] at E0000 F0000 F1100 E0101 F0101 F1001 E1000 F0100 F1000 E1011 E0001 F1101 F0001 E0010
  have z1100 : w ![1, 1, 0, 0] = 0 := by linear_combination E0000 - (sq2 + 1) * h0
  have z0011 : w ![0, 0, 1, 1] = 0 := by linear_combination F0000 - (sq2 + 1) * h0
  have z1111 : w ![1, 1, 1, 1] = 0 := by linear_combination F1100 - (sq2 - 1) * z1100
  have z1001 : w ![1, 0, 0, 1] = 0 := by linear_combination E0101 - (sq2 - 1) * h5
  have z0110 : w ![0, 1, 1, 0] = 0 := by linear_combination F0101 - (sq2 - 1) * h5
  have z1010 : w ![1, 0, 1, 0] = 0 := by linear_combination F1001 - (sq2 + 1) * z1001
  have d4 : 4 * sq2 * w ![1, 0, 0, 0] = 0 := by
    linear_combination (sq2 + 1) * E1000 - F0100 - (sq2 - 1) * F1000 + E1011
  have z1000 : w ![1, 0, 0, 0] = 0 :=
    (mul_eq_zero.mp d4).resolve_left (mul_ne_zero (by norm_num) sq2_ne)
  have z0100 : w ![0, 1, 0, 0] = 0 := by linear_combination E1000 - (sq2 + 1) * z1000
  have z1011 : w ![1, 0, 1, 1] = 0 := by linear_combination F1000 - (sq2 - 1) * z1000
  have z0111 : w ![0, 1, 1, 1] = 0 := by linear_combination F0100 - (sq2 + 1) * z0100
  have d4' : 4 * sq2 * w ![0, 0, 0, 1] = 0 := by
    linear_combination (sq2 + 1) * E0001 - F1101 - (sq2 - 1) * F0001 + E0010
  have z0001 : w ![0, 0, 0, 1] = 0 :=
    (mul_eq_zero.mp d4').resolve_left (mul_ne_zero (by norm_num) sq2_ne)
  have z1101 : w ![1, 1, 0, 1] = 0 := by linear_combination E0001 - (sq2 + 1) * z0001
  have z0010 : w ![0, 0, 1, 0] = 0 := by linear_combination F0001 - (sq2 - 1) * z0001
  have z1110 : w ![1, 1, 1, 0] = 0 := by linear_combination F1101 - (sq2 + 1) * z1101
  funext x; revert x
  apply forall4
  intro a b c d
  show w ![a, b, c, d] = 0
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    assumption

lemma gs_eq (v : (Fin 4 → Fin 2) → ℂ)
    (hv : v ∈ groundSpace codeHamiltonian (-(2 * Real.sqrt 2))) :
    v = v ![0, 0, 0, 0] • g1 + v ![0, 1, 0, 1] • g2 := by
  have hw : v - (v ![0, 0, 0, 0] • g1 + v ![0, 1, 0, 1] • g2) ∈
      groundSpace codeHamiltonian (-(2 * Real.sqrt 2)) :=
    sub_mem hv (add_mem (Submodule.smul_mem _ _ g1_mem) (Submodule.smul_mem _ _ g2_mem))
  have := gs_zero _ hw (by simp [g1, g2]) (by simp [g1, g2])
  exact sub_eq_zero.mp this

lemma gs_span : groundSpace codeHamiltonian (-(2 * Real.sqrt 2)) =
    Submodule.span ℂ (Set.range ![g1, g2]) := by
  apply le_antisymm
  · intro v hv
    rw [gs_eq v hv]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact g1_mem
    · exact g2_mem

lemma g_li : LinearIndependent ℂ ![g1, g2] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h1 := congrFun h ![0, 0, 0, 0]
  have h2 := congrFun h ![0, 1, 0, 1]
  simp [g1, g2] at h1 h2
  exact ⟨h1, h2⟩

lemma finrank_gs : Module.finrank ℂ (groundSpace codeHamiltonian (-(2 * Real.sqrt 2))) = 2 := by
  rw [gs_span, finrank_span_eq_card g_li]
  simp

lemma onQ_mulVec {n : ℕ} (k : Fin n) (O : Matrix (Fin 2) (Fin 2) ℂ) (v : (Fin n → Fin 2) → ℂ)
    (x : Fin n → Fin 2) :
    (onQubit k O *ᵥ v) x =
      O (x k) 0 * v (Function.update x k 0) + O (x k) 1 * v (Function.update x k 1) := by
  simp only [mulVec, dotProduct, onQubit]
  have key : ∀ y : Fin n → Fin 2,
      (if ∀ j, j ≠ k → x j = y j then O (x k) (y k) else 0) * v y =
        ∑ b : Fin 2, if y = Function.update x k b then O (x k) b * v y else 0 := by
    intro y
    by_cases h : ∀ j, j ≠ k → x j = y j
    · have hy : y = Function.update x k (y k) := by
        funext j
        by_cases hj : j = k
        · subst hj; simp
        · simp [Function.update_apply, hj, h j hj]
      rw [if_pos h, Finset.sum_eq_single (y k)]
      · rw [if_pos hy]
      · intro b _ hb
        rw [if_neg]
        intro hc; apply hb; rw [hc]; simp
      · intro hk; exact absurd (Finset.mem_univ _) hk
    · rw [if_neg h, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      intro hc; apply h; intro j hj; rw [hc]; simp [Function.update_apply, hj]
  rw [Finset.sum_congr rfl (fun y _ => key y), Finset.sum_comm]
  simp [Fin.sum_univ_two]

set_option maxHeartbeats 4000000 in
lemma supercoh (k : Fin 4) (O : Matrix (Fin 2) (Fin 2) ℂ) (hO : O.trace = 0)
    (ψ : (Fin 4 → Fin 2) → ℂ) (hψ : ψ ∈ groundSpace codeHamiltonian (-(2 * Real.sqrt 2)))
    (φ : (Fin 4 → Fin 2) → ℂ) (hφ : φ ∈ groundSpace codeHamiltonian (-(2 * Real.sqrt 2))) :
    star φ ⬝ᵥ (onQubit k O *ᵥ ψ) = 0 := by
  have h11 : O 1 1 = -O 0 0 := by
    rw [Matrix.trace_fin_two] at hO; linear_combination hO
  rw [gs_eq ψ hψ, gs_eq φ hφ]
  generalize ψ ![0, 0, 0, 0] = p1
  generalize ψ ![0, 1, 0, 1] = p2
  generalize φ ![0, 0, 0, 0] = q1
  generalize φ ![0, 1, 0, 1] = q2
  rw [dotProduct, sum16]
  fin_cases k <;>
    simp [Fin.sum_univ_two, onQ_mulVec, g1, g2, h11, Function.update_apply, sq2_star,
      sq2_conj] <;> ring

end BCS502

open QMaxCutSDP.Rounding Matrix BaconThesis.Supercoherence in
theorem solution :
    IsGroundEnergy codeHamiltonian (-(2 * Real.sqrt 2)) ∧
      Module.finrank ℂ (groundSpace codeHamiltonian (-(2 * Real.sqrt 2))) = 2 ∧
      IsSupercoherent codeHamiltonian := by
  have hGE : IsGroundEnergy codeHamiltonian (-(2 * Real.sqrt 2)) := by
    refine ⟨?_, fun μ v hv0 hv => BCS502.lower μ v hv0 hv⟩
    rw [Submodule.ne_bot_iff]
    refine ⟨BCS502.g1, BCS502.g1_mem, fun h => ?_⟩
    have := congrFun h ![0, 0, 0, 0]
    simp [BCS502.g1] at this
  have herm : codeHamiltonian.IsHermitian := by
    rw [BCS502.hcode]
    have h : ∀ s : Fin 4 → Fin 4, (pauliString s : Operator 4).IsHermitian :=
      fun s => BCS502.pauliString_herm s
    exact (((h _).add (h _)).add (h _)).add (h _)
  refine ⟨hGE, BCS502.finrank_gs, herm, -(2 * Real.sqrt 2), hGE, BCS502.finrank_gs.ge, ?_⟩
  intro k O hO ψ hψ φ hφ
  exact BCS502.supercoh k O hO ψ hψ φ hφ
