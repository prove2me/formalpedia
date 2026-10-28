-- Prove2me | solution 1 for EntanglingOps.BinaryPhase.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:10:26.71322+00:00
-- url     : https://prove2.me/submissions/dd3aa177-61a3-408e-80ba-e28c10af6dc7

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

lemma conj_vecMulVec {ι κ : Type} [Fintype ι] [Fintype κ] (M : Matrix κ ι ℂ) (u : ι → ℂ) :
    M * vecMulVec u (star u) * Mᴴ = vecMulVec (M *ᵥ u) (star (M *ᵥ u)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]

lemma reindex_vecMulVec {ι κ : Type} (e : ι ≃ κ) (u : ι → ℂ) :
    reindex e e (vecMulVec u (star u)) = vecMulVec (u ∘ e.symm) (star (u ∘ e.symm)) := by
  ext i j; simp [vecMulVec]

lemma projPair_eq (d : ℕ) : reindex (regroup d) (regroup d) (projPhi d ⊗ₖ projPhi d) =
    vecMulVec (fun p : (Fin d × Fin d) × (Fin d × Fin d) => phiVec d (p.1.1, p.2.1) * phiVec d (p.1.2, p.2.2))
      (star (fun p : (Fin d × Fin d) × (Fin d × Fin d) => phiVec d (p.1.1, p.2.1) * phiVec d (p.1.2, p.2.2))) := by
  ext ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩ ⟨⟨c1, e1⟩, ⟨c2, e2⟩⟩
  simp [projPhi, vecMulVec, regroup, Matrix.kroneckerMap_apply]
  ring

lemma phiVec_two : phiVec 2 = phiPlus := by
  ext p; simp [phiVec, phiPlus]

lemma resource_gate (α : ℝ) (x : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :
    resource α x = ∑ y : Fin 2 × Fin 2,
        gate α (x.1.1, x.2.1) y * phiPlus (y.1, x.1.2) * phiPlus (y.2, x.2.2) := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := x
  rw [gate_eq]
  simp only [resource, phiPlus, psiPlus]
  generalize ((1 / Real.sqrt 2 : ℝ) : ℂ) = s
  generalize (Real.cos α : ℂ) = c
  generalize (Real.sin α : ℂ) = sn
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [Fintype.sum_prod_type, sx, pauli, Matrix.one_apply] <;> ring

lemma choi_gate (α : ℝ) :
    choiOp (fun _ : Unit => gate α) = vecMulVec (resource α) (star (resource α)) := by
  unfold choiOp
  rw [Fintype.sum_unique, projPair_eq, conj_vecMulVec, reindex_vecMulVec]
  have key : ∀ V, V = resource α →
      vecMulVec V (star V) = vecMulVec (resource α) (star (resource α)) := by
    rintro V rfl; rfl
  apply key
  ext ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
  rw [resource_gate]
  simp [regroup, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, phiVec_two]
  ring

theorem solution :
    (∀ (α : ℝ) (x : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)),
      resource α x = ∑ y : Fin 2 × Fin 2,
        gate α (x.1.1, x.2.1) y * phiPlus (y.1, x.1.2) * phiPlus (y.2, x.2.2)) ∧
    (∀ α : ℝ, choiOp (fun _ : Unit => gate α) = vecMulVec (resource α) (star (resource α))) :=
  ⟨resource_gate, choi_gate⟩
