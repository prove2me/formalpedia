-- Prove2me | solution 1 for EntanglingOps.BinaryPhase.eq_12
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:03:16.413989+00:00
-- url     : https://prove2.me/submissions/bc953744-4399-488b-b8a0-071c7c39575d

import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

open Matrix
open scoped Kronecker ComplexOrder
open EntanglingOps.BinaryPhase

noncomputable def gX : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := sx ⊗ₖ sx
noncomputable def gH : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  !![1, 1; 1, -1] ⊗ₖ !![1, 1; 1, -1]
noncomputable def gd : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then 1 else -1

lemma gH_mul : gH * ((1/4 : ℂ) • gH) = 1 := by
  ext ⟨a, b⟩ ⟨c, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [gH, Matrix.mul_apply, Fintype.sum_prod_type] <;> norm_num

lemma gH_inv : gH⁻¹ = (1/4 : ℂ) • gH := (Matrix.inv_eq_right_inv gH_mul)

lemma gX_eq : gX = gH * diagonal gd * gH⁻¹ := by
  rw [gH_inv]
  ext ⟨a, b⟩ ⟨c, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [gX, sx, pauli, gH, gd, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.diagonal] <;> norm_num

lemma gate_eq (α : ℝ) : gate α =
    (Real.cos α : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) -
      (Complex.I * Real.sin α) • (sx ⊗ₖ sx) := by
  have hU : IsUnit gH := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact Matrix.isUnit_det_of_right_inverse gH_mul
  have h1 : (-(Complex.I * (α : ℂ))) • (sx ⊗ₖ sx) =
      gH * diagonal ((-(Complex.I * (α : ℂ))) • gd) * gH⁻¹ := by
    have := gX_eq
    simp only [gX] at this
    rw [this, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  unfold gate
  rw [h1, Matrix.exp_conj _ _ hU, Matrix.exp_diagonal, gH_inv]
  ext ⟨a, b⟩ ⟨c, e⟩
  have hc : ∀ t : ℂ, NormedSpace.exp t = Complex.exp t := fun t => by
    rw [Complex.exp_eq_exp_ℂ]
  have e1 : Complex.exp (-(Complex.I * α)) = Real.cos α - Complex.I * Real.sin α := by
    rw [show -(Complex.I * α) = ((-α : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
    push_cast; simp [Complex.cos_neg, Complex.sin_neg]; ring
  have e2 : Complex.exp (Complex.I * α) = Real.cos α + Complex.I * Real.sin α := by
    rw [show (Complex.I * α) = ((α : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
    push_cast; ring
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [sx, pauli, gH, gd, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.diagonal, Pi.exp_def, hc, e1, e2, Matrix.one_apply] <;> ring_nf

lemma bellVec_eq (i : Fin 2 × Fin 2) (x : Fin 2 × Fin 2) :
    bellVec i x = pauli i x.2 x.1 * ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
  simp only [bellVec, phiPlus]
  rw [Finset.sum_eq_single x.1]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma hs2 : ((1 / Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 1/2 := by
  rw [← Complex.ofReal_pow, div_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma resource_eq (β : ℝ) (r1 a2 r2 b2 : Fin 2) :
    resource β ((r1, a2), (r2, b2)) = (1/2 : ℂ) * ((Real.cos β : ℂ) *
      (1 : Matrix (Fin 2) (Fin 2) ℂ) r1 a2 * (1 : Matrix (Fin 2) (Fin 2) ℂ) r2 b2 -
      Complex.I * Real.sin β * sx r1 a2 * sx r2 b2) := by
  have h := hs2
  simp only [resource, phiPlus, psiPlus]
  generalize ((1 / Real.sqrt 2 : ℝ) : ℂ) = s at h ⊢
  generalize (Real.cos β : ℂ) = c
  generalize (Real.sin β : ℂ) = sn
  fin_cases r1 <;> fin_cases a2 <;> fin_cases r2 <;> fin_cases b2 <;>
    simp [sx, pauli, Matrix.one_apply] <;> ring_nf <;> simp only [h] <;> ring_nf

lemma inner_eq (β : ℝ) (i j : Fin 2 × Fin 2) :
    (Matrix.of fun (r c : Fin 2 × Fin 2) =>
      ∑ a₂ : Fin 2, ∑ b₂ : Fin 2,
        star (bellVec i (a₂, c.1)) * star (bellVec j (b₂, c.2)) * resource β ((r.1, a₂), (r.2, b₂))) =
    (1/4 : ℂ) • ((Real.cos β : ℂ) • ((pauli i)ᴴ ⊗ₖ (pauli j)ᴴ) -
      (Complex.I * Real.sin β) • ((sx * (pauli i)ᴴ) ⊗ₖ (sx * (pauli j)ᴴ))) := by
  have h := hs2
  have hst : star ((1 / Real.sqrt 2 : ℝ) : ℂ) = ((1 / Real.sqrt 2 : ℝ) : ℂ) := Complex.conj_ofReal _
  ext ⟨r1, r2⟩ ⟨c1, c2⟩
  simp only [Matrix.of_apply, bellVec_eq, resource_eq, star_mul', hst]
  generalize ((1 / Real.sqrt 2 : ℝ) : ℂ) = s at h ⊢
  generalize (Real.cos β : ℂ) = c
  generalize (Real.sin β : ℂ) = sn
  generalize pauli i = P
  generalize pauli j = Q
  fin_cases r1 <;> fin_cases r2 <;>
  simp [Fin.sum_univ_two, Matrix.mul_apply, Matrix.conjTranspose_apply, sx, pauli, Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMul, dotProduct] <;>
  ring_nf <;> simp only [h] <;> ring_nf

lemma pauli_unit (i : Fin 2 × Fin 2) : pauli i * (pauli i)ᴴ = 1 := by
  obtain ⟨a, b⟩ := i
  fin_cases a <;> fin_cases b <;> ext x y <;> fin_cases x <;> fin_cases y <;>
    simp [pauli, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

lemma pauli_sx (i : Fin 2 × Fin 2) :
    pauli i * (sx * (pauli i)ᴴ) = (if i.1 = 0 then (1 : ℂ) else -1) • sx := by
  obtain ⟨a, b⟩ := i
  fin_cases a <;> fin_cases b <;> ext x y <;> fin_cases x <;> fin_cases y <;>
    simp [pauli, sx, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

lemma step_eq (β : ℝ) (i j : Fin 2 × Fin 2) :
    stepKraus β i j = (1/4 : ℂ) • gate (if i.1 = j.1 then β else -β) := by
  unfold stepKraus
  rw [inner_eq, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, pauli_unit, pauli_unit, pauli_sx,
    pauli_sx, Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul,
    gate_eq]
  congr 1
  obtain ⟨i1, i2⟩ := i
  obtain ⟨j1, j2⟩ := j
  fin_cases i1 <;> fin_cases j1 <;> simp [smul_smul] <;> module

lemma sxsx_sq : (sx ⊗ₖ sx) * (sx ⊗ₖ sx) = 1 := by
  rw [← Matrix.mul_kronecker_mul]
  have : sx * sx = 1 := by
    ext x y; fin_cases x <;> fin_cases y <;> simp [sx, pauli, Matrix.mul_apply, Fin.sum_univ_two]
  rw [this, Matrix.one_kronecker_one]

lemma gate_mul (a b : ℝ) : gate a * gate b = gate (a + b) := by
  simp only [gate_eq]
  rw [sub_mul, mul_sub, mul_sub, smul_mul_smul, smul_mul_smul, smul_mul_smul, smul_mul_smul,
    sxsx_sq]
  simp only [Matrix.mul_one, Matrix.one_mul]
  simp only [Real.cos_add, Real.sin_add]
  push_cast
  match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring

lemma gate_zero : gate 0 = 1 := by simp [gate_eq]

lemma gate_conjT (a : ℝ) : (gate a)ᴴ = gate (-a) := by
  have hx : (sx ⊗ₖ sx)ᴴ = sx ⊗ₖ sx := by
    ext x y; simp [sx, pauli, Matrix.conjTranspose_apply]
    obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
    fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;> simp
  rw [gate_eq, gate_eq, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, hx, Matrix.conjTranspose_one]
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I, Real.cos_neg,
    Real.sin_neg, Complex.ofReal_neg]
  module

lemma gate_unitary (a : ℝ) : (gate a)ᴴ * gate a = 1 := by
  rw [gate_conjT, gate_mul, neg_add_cancel, gate_zero]

lemma gate_pow (a : ℝ) (n : ℕ) : gate a ^ n = gate (n * a) := by
  induction n with
  | zero => simp [gate_zero]
  | succ n ih => rw [pow_succ, ih, gate_mul]; push_cast; ring_nf

lemma trace_gate_conj (c : ℂ) (a : ℝ) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix.trace ((c • gate a) * ρ * (c • gate a)ᴴ) = (c * star c) * Matrix.trace ρ := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_mul_cycle, gate_unitary, Matrix.one_mul,
    smul_smul, smul_eq_mul, mul_comm (star c) c]

lemma branch_fail (N : ℕ) : ∀ (l : List Outcome), (∀ o ∈ l, ¬ succeeds o) → ∀ m : ℕ,
    ∃ c : ℂ, Complex.normSq c = (1/16 : ℝ) ^ l.length ∧
      branchKrausFrom N m l = c • gate (-((2:ℝ) ^ m * ((2:ℝ) ^ l.length - 1)) * alphaN N) := by
  intro l
  induction l with
  | nil => intro _ m; exact ⟨1, by simp, by simp [branchKrausFrom, gate_zero]⟩
  | cons o l ih =>
    intro h m
    obtain ⟨c, hc, he⟩ := ih (fun o' ho' => h o' (List.mem_cons_of_mem _ ho')) (m + 1)
    have hno : ¬ o.1.1 = o.2.1 := h o List.mem_cons_self
    refine ⟨c * (1/4), ?_, ?_⟩
    · rw [Complex.normSq_mul, hc, List.length_cons, pow_succ]
      rw [Complex.normSq_apply]; norm_num
    · rw [branchKrausFrom, he, step_eq, if_neg hno, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        gate_mul, List.length_cons]
      congr 2
      push_cast
      ring

lemma mem_failing {k : ℕ} {l : List Outcome} (hl : l ∈ failing k) :
    l.length = k ∧ ∀ o ∈ l, ¬ succeeds o := by
  simp only [failing, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  obtain ⟨f, hf, rfl⟩ := hl
  refine ⟨List.length_ofFn, fun o ho => ?_⟩
  rw [List.mem_ofFn] at ho
  obtain ⟨s, rfl⟩ := ho
  exact hf s

lemma failing_kraus (N k : ℕ) (l : List Outcome) (hl : l ∈ failing k) :
    ∃ c : ℂ, Complex.normSq c = (1/16 : ℝ) ^ k ∧
      branchKraus N l = c • gate (-((2:ℝ) ^ k - 1) * alphaN N) := by
  obtain ⟨hlen, hf⟩ := mem_failing hl
  obtain ⟨c, hc, he⟩ := branch_fail N l hf 0
  refine ⟨c, hlen ▸ hc, ?_⟩
  rw [branchKraus, he, hlen]
  congr 2; ring

lemma gate_neg_pi_add (x : ℝ) : gate (-Real.pi + x) = -gate x := by
  rw [← gate_mul]
  have : gate (-Real.pi) = -1 := by
    rw [gate_eq]; simp
  rw [this, neg_one_mul]

lemma gate_pow_fail (N k : ℕ) :
    gate (-alphaN N) ^ (2 ^ k - 1) = gate (-((2:ℝ) ^ k - 1) * alphaN N) := by
  rw [gate_pow]
  congr 1
  rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]
  push_cast; ring

lemma gate_full (N : ℕ) : gate (-((2:ℝ) ^ N - 1) * alphaN N) = -gate (alphaN N) := by
  rw [← gate_neg_pi_add]
  congr 1
  unfold alphaN
  field_simp
  ring

lemma card_succeeds : (Finset.univ.filter succeeds).card = 8 := by decide

lemma card_failing (k : ℕ) : (failing k).card = 8 ^ k := by
  unfold failing
  rw [Finset.card_image_of_injective _ List.ofFn_injective]
  have : (Finset.univ.filter fun f : Fin k → Outcome => ∀ s, ¬ succeeds (f s)) =
      Fintype.piFinset (fun _ : Fin k => Finset.univ.filter fun o : Outcome => ¬ succeeds o) := by
    ext f; simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset]
  have h8 : (Finset.univ.filter fun o : Outcome => ¬ succeeds o).card = 8 := by decide
  simp [h8]

lemma weight_fail (N k : ℕ) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hρ : ρ.trace = 1)
    (l : List Outcome) (hl : l ∈ failing k) :
    (Matrix.trace (branchKraus N l * ρ * (branchKraus N l)ᴴ)).re = (1/16 : ℝ) ^ k := by
  obtain ⟨c, hc, he⟩ := failing_kraus N k l hl
  rw [he, trace_gate_conj, hρ, mul_one, Complex.star_def, Complex.mul_conj, Complex.ofReal_re, hc]

lemma reach_eq (N k : ℕ) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hρ : ρ.trace = 1) :
    reachProb N ρ k = (1/2 : ℝ) ^ (k - 1) := by
  unfold reachProb
  rw [Finset.sum_congr rfl (fun l hl => weight_fail N (k-1) ρ hρ l hl), Finset.sum_const,
    card_failing, nsmul_eq_mul]
  push_cast
  rw [← mul_pow]; norm_num

lemma geom_half (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, (1/2 : ℝ) ^ (k - 1) = 2 - 2 * (1/2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.add_sub_cancel, pow_succ]
    ring

lemma reflect_sum (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (1 / 2 : ℝ) ^ (k - 1) * entEntropy (resource (alphaN (N - k + 1))) =
      alphaN N * fN N := by
  unfold fN
  rw [← mul_assoc, Finset.mul_sum]
  refine Finset.sum_nbij' (fun k => N + 1 - k) (fun j => N + 1 - j) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    have e1 : N - k + 1 = N + 1 - k := by omega
    rw [e1]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have e2 : (2:ℝ) ^ N = 2 ^ (N + 1 - k) * 2 ^ (k - 1) := by
      rw [← pow_add]; congr 1; omega
    unfold alphaN
    rw [e2]
    field_simp
    rw [_root_.one_div_pow]
    field_simp
theorem solution (N : ℕ) (hN : 1 ≤ N) :
    (∀ ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, ρ.PosSemidef → ρ.trace = 1 →
      (∀ k ∈ Finset.Icc 1 N, reachProb N ρ k = (1 / 2 : ℝ) ^ (k - 1)) ∧
      avgEnt N ρ = ∑ k ∈ Finset.Icc 1 N,
        (1 / 2 : ℝ) ^ (k - 1) * entEntropy (resource (alphaN (N - k + 1))) ∧
      avgComm N ρ = 2 - (1 / 2 : ℝ) ^ ((N : ℤ) - 2)) ∧
    ∑ k ∈ Finset.Icc 1 N, (1 / 2 : ℝ) ^ (k - 1) * entEntropy (resource (alphaN (N - k + 1))) =
      alphaN N * fN N := by
  refine ⟨fun ρ _ hρ => ⟨fun k _ => reach_eq N k ρ hρ, ?_, ?_⟩, reflect_sum N⟩
  · unfold avgEnt
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_Icc] at hk
    rw [reach_eq N k ρ hρ]
    congr 3
    unfold alphaN
    have e2 : (2:ℝ) ^ N = 2 ^ (N - k + 1) * 2 ^ (k - 1) := by
      rw [← pow_add]; congr 1; omega
    rw [e2]; field_simp
  · unfold avgComm
    rw [Finset.sum_congr rfl (fun k _ => reach_eq N k ρ hρ), geom_half]
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have : ((n + 1 : ℕ) : ℤ) - 2 = (n : ℤ) - 1 := by push_cast; ring
    rw [this, zpow_sub₀ (by norm_num), zpow_natCast, zpow_one]
    ring
