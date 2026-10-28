-- Prove2me | solution 1 for EntanglingOps.BinaryPhase.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:32:49.472998+00:00
-- url     : https://prove2.me/submissions/7043b809-ad41-498e-90a0-a6ef4d556e01

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy
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
section EV
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma aeval_mulVec_eigen (A : Matrix n n ℂ) (v : n → ℂ) (μ : ℝ)
    (hv : A.mulVec v = (μ : ℂ) • v) (q : Polynomial ℝ) :
    (Polynomial.aeval A q).mulVec v = ((q.eval μ : ℝ) : ℂ) • v := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    simp [map_add, Matrix.add_mulVec, hp, hq, add_smul]
  | monomial m c =>
    have hpow : ∀ m : ℕ, (A ^ m).mulVec v = ((μ ^ m : ℝ) : ℂ) • v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih, smul_smul]
        push_cast; ring_nf
    simp only [Polynomial.aeval_monomial, Polynomial.eval_monomial]
    have : (algebraMap ℝ (Matrix n n ℂ) c * A ^ m).mulVec v = ((c * μ ^ m : ℝ) : ℂ) • v := by
      rw [← Matrix.mulVec_mulVec, hpow]
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec, ← Complex.coe_smul c, smul_smul]
      push_cast; rfl
    exact this

lemma cfc_mulVec_eigen (A : Matrix n n ℂ) (hA : A.IsHermitian) (v : n → ℂ) (μ : ℝ)
    (hv : A.mulVec v = (μ : ℂ) • v) (f : ℝ → ℝ) :
    (cfc f A).mulVec v = ((f μ : ℝ) : ℂ) • v := by
  classical
  have hsa : IsSelfAdjoint A := hA
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  let σ : Finset ℝ := insert μ hfin.toFinset
  let q : Polynomial ℝ := Lagrange.interpolate σ id f
  have hq : ∀ x ∈ σ, q.eval x = f x := by
    intro x hx
    exact Lagrange.eval_interpolate_at_node f Function.injective_id.injOn hx
  have h1 : cfc f A = cfc (fun x => q.eval x) A := by
    apply cfc_congr
    intro x hx
    exact (hq x (Finset.mem_insert_of_mem (hfin.mem_toFinset.2 hx))).symm
  rw [h1, cfc_polynomial q A hsa, aeval_mulVec_eigen A v μ hv q,
    hq μ (Finset.mem_insert_self _ _)]
end EV

lemma trace_cfc_basis {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (V W : Matrix n n ℂ) (hWV : W * V = 1) (hVW : V * W = 1) (μ : n → ℝ)
    (hv : ∀ j, A *ᵥ (fun i => V i j) = (μ j : ℂ) • (fun i => V i j)) (f : ℝ → ℝ) :
    Matrix.trace (cfc f A) = ∑ j, ((f (μ j) : ℝ) : ℂ) := by
  have hcol : cfc f A * V = V * diagonal (fun j => ((f (μ j) : ℝ) : ℂ)) := by
    ext i j
    have := congrFun (cfc_mulVec_eigen A hA (fun i => V i j) (μ j) (hv j) f) i
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply, this, mul_comm]
  calc Matrix.trace (cfc f A) = Matrix.trace (cfc f A * V * W) := by rw [Matrix.mul_assoc, hVW, Matrix.mul_one]
    _ = Matrix.trace (V * diagonal (fun j => ((f (μ j) : ℝ) : ℂ)) * W) := by rw [hcol]
    _ = Matrix.trace (W * V * diagonal (fun j => ((f (μ j) : ℝ) : ℂ))) := by
      rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = ∑ j, ((f (μ j) : ℝ) : ℂ) := by rw [hWV, Matrix.one_mul, Matrix.trace_diagonal]

noncomputable def ee : Fin 2 × Fin 2 → ℂ := fun x => if x.1 = x.2 then 1 else 0
noncomputable def oo : Fin 2 × Fin 2 → ℂ := fun x => if x.1 = x.2 then 0 else 1

noncomputable def rhoA (c2 s2 : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun x y => (1/2 : ℂ) * ((c2 : ℂ) * ee x * ee y + (s2 : ℂ) * oo x * oo y)

lemma rhoA_eq (α : ℝ) : WildeQIT.partialTraceRight (vecMulVec (resource α) (star (resource α))) =
    rhoA (Real.cos α ^ 2) (Real.sin α ^ 2) := by
  have h := hs2
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  simp only [WildeQIT.partialTraceRight, Matrix.of_apply, vecMulVec_apply, Pi.star_apply,
    resource, phiPlus, psiPlus, rhoA, ee, oo]
  simp only [star_sub, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_pow, apply_ite (starRingEnd ℂ), map_zero]
  generalize ((1 / Real.sqrt 2 : ℝ) : ℂ) = s at h ⊢
  generalize (Real.cos α : ℂ) = c
  generalize (Real.sin α : ℂ) = sn
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [Fintype.sum_prod_type] <;>
    ring_nf <;> (try simp only [h, Complex.I_sq, show s ^ 4 = (s^2)^2 by ring]) <;> (try ring_nf) <;> done

noncomputable def sg : Fin 2 × Fin 2 → ℂ := fun x => if x.1 = 0 then 1 else -1

noncomputable def bV : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun x j => (if j.1 = 0 then 1 else sg x) * (if j.2 = 0 then ee x else oo x)

lemma bV_inv1 : ((1/2 : ℂ) • bVᵀ) * bV = 1 := by
  ext ⟨a, b⟩ ⟨c, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [bV, sg, ee, oo, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply] <;> norm_num

lemma bV_inv2 : bV * ((1/2 : ℂ) • bVᵀ) = 1 := by
  ext ⟨a, b⟩ ⟨c, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [bV, sg, ee, oo, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply] <;> norm_num

noncomputable def muv (c2 s2 : ℝ) : Fin 2 × Fin 2 → ℝ := fun j => if j.1 = 0 then (if j.2 = 0 then c2 else s2) else 0

lemma rhoA_eig (c2 s2 : ℝ) (j : Fin 2 × Fin 2) :
    rhoA c2 s2 *ᵥ (fun i => bV i j) = ((muv c2 s2 j : ℝ) : ℂ) • (fun i => bV i j) := by
  funext ⟨a, b⟩
  obtain ⟨j1, j2⟩ := j
  fin_cases j1 <;> fin_cases j2 <;> fin_cases a <;> fin_cases b <;>
    simp [rhoA, bV, sg, ee, oo, muv, Matrix.mulVec, dotProduct, Fintype.sum_prod_type] <;> ring

lemma rhoA_herm (c2 s2 : ℝ) : (rhoA c2 s2).IsHermitian := by
  ext ⟨a, b⟩ ⟨c, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [rhoA, ee, oo, Matrix.conjTranspose_apply, Complex.conj_ofReal]

lemma vn_rhoA (c2 s2 : ℝ) :
    QAlgorithms.vnEntropy (rhoA c2 s2) = -(c2 * Real.logb 2 c2) - s2 * Real.logb 2 s2 := by
  unfold QAlgorithms.vnEntropy
  rw [trace_cfc_basis (rhoA c2 s2) (rhoA_herm c2 s2) bV ((1/2 : ℂ) • bVᵀ) bV_inv1 bV_inv2
    (muv c2 s2) (rhoA_eig c2 s2)]
  simp [Fintype.sum_prod_type, muv]
  ring

lemma ent_resource (α : ℝ) :
    entEntropy (resource α) = WildeQIT.binaryEntropy (Real.cos α ^ 2) := by
  unfold entEntropy WildeQIT.binaryEntropy
  rw [rhoA_eq, vn_rhoA]
  have : 1 - Real.cos α ^ 2 = Real.sin α ^ 2 := by rw [← Real.sin_sq_add_cos_sq α]; ring
  rw [this]

theorem solution :
    (∀ α : ℝ, entEntropy (resource α) = WildeQIT.binaryEntropy (Real.cos α ^ 2)) ∧
    entEntropy (resource (alphaN 2)) = 1 ∧
    entEntropy (resource (alphaN 1)) = 0 ∧
    gate (Real.pi / 2) = (-Complex.I) • (sx ⊗ₖ sx) := by
  refine ⟨ent_resource, ?_, ?_, ?_⟩
  · rw [ent_resource]
    have : alphaN 2 = Real.pi / 4 := by unfold alphaN; norm_num
    rw [this, Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
    unfold WildeQIT.binaryEntropy
    norm_num
    rw [one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
    ring
  · rw [ent_resource]
    have : alphaN 1 = Real.pi / 2 := by unfold alphaN; norm_num
    rw [this, Real.cos_pi_div_two]
    unfold WildeQIT.binaryEntropy
    simp
  · rw [gate_eq]
    simp
