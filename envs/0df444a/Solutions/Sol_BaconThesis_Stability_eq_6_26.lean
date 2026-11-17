-- Prove2me | solution 1 for BaconThesis.Stability.eq_6_26
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T10:13:45.298304+00:00
-- url     : https://prove2.me/submissions/a2d55eff-fd77-4986-97cc-5ec821396db3

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_Stability_IsBlockForm
import Definitions.Def_BaconThesis_Stability_encode
import Definitions.Def_BaconThesis_Stability_rate

open scoped Kronecker Matrix
open Asymptotics Topology

namespace BaconThesis.Stability.Sol626

open BaconThesis.Stability

section calculus

variable {T : Type} [Fintype T] [DecidableEq T]

/-- The generator `X ↦ -i [H, X]` of the Heisenberg-picture evolution. -/
def gen (H X : Matrix T T ℂ) : Matrix T T ℂ := (-Complex.I) • (H * X - X * H)

open scoped Matrix.Norms.Operator in
private lemma hasDerivAt_evol (H R : Matrix T T ℂ) (hH : H.IsHermitian) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H) * R *
        (NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H))ᴴ)
      (NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H) * gen H R *
        (NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H))ᴴ) t := by
  have e1 : ∀ s : ℝ, NormedSpace.exp ((-(Complex.I * (s : ℂ))) • H) =
      NormedSpace.exp (s • ((-Complex.I) • H)) := by
    intro s
    congr 1
    rw [← Complex.coe_smul, smul_smul]
    congr 1
    ring
  have e2 : ∀ s : ℝ, (NormedSpace.exp ((-(Complex.I * (s : ℂ))) • H))ᴴ =
      NormedSpace.exp (s • (Complex.I • H)) := by
    intro s
    have hs : star (-(Complex.I * (s : ℂ))) = (s : ℂ) * Complex.I := by simp [mul_comm]
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH.eq, hs, ← Complex.coe_smul,
      smul_smul]
  simp_rw [e2, e1]
  have h1 := hasDerivAt_exp_smul_const ((-Complex.I) • H) t
  have h2 := hasDerivAt_exp_smul_const' (Complex.I • H) t
  refine ((h1.mul_const R).mul h2).congr_deriv ?_
  change NormedSpace.exp (t • -Complex.I • H) * (-Complex.I • H) * R *
      NormedSpace.exp (t • Complex.I • H) +
    NormedSpace.exp (t • -Complex.I • H) * R * (Complex.I • H * NormedSpace.exp (t • Complex.I • H)) =
    NormedSpace.exp (t • -Complex.I • H) * (-Complex.I • (H * R - R * H)) *
      NormedSpace.exp (t • Complex.I • H)
  generalize NormedSpace.exp (t • -Complex.I • H) = U
  generalize NormedSpace.exp (t • Complex.I • H) = V
  simp only [smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul, smul_sub, mul_assoc]
  module

open scoped Matrix.Norms.Operator in
private lemma iteratedDeriv_evol (L : Matrix T T ℂ →ₗ[ℂ] ℂ) (H : Matrix T T ℂ)
    (hH : H.IsHermitian) (p : ℕ) : ∀ R : Matrix T T ℂ,
    iteratedDeriv p (fun t : ℝ => L (NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H) * R *
        (NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H))ᴴ)) =
      fun t : ℝ => L (NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H) * (gen H)^[p] R *
        (NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H))ᴴ) := by
  induction p with
  | zero => intro R; simp
  | succ p ih =>
    intro R
    rw [iteratedDeriv_succ']
    have hd : deriv (fun t : ℝ => L (NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H) * R *
        (NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H))ᴴ)) =
        fun t : ℝ => L (NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H) * gen H R *
        (NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H))ᴴ) := by
      funext t
      let Lc : Matrix T T ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (L.restrictScalars ℝ)
      exact (Lc.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_evol H R hH t)).deriv
    rw [hd, ih (gen H R)]
    rfl

end calculus

section algebra

variable {T : Type} [Fintype T]

private lemma trace_mul_gen (Q H X : Matrix T T ℂ) (hQH : Q * H = H * Q) :
    (Q * gen H X).trace = 0 := by
  simp only [gen, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub, Matrix.trace_sub]
  rw [← Matrix.mul_assoc, hQH, Matrix.mul_assoc, Matrix.trace_mul_comm H, Matrix.mul_assoc]
  simp

private lemma gen_add_smul (H V X : Matrix T T ℂ) (c : ℂ) :
    gen (H + c • V) X = gen H X + c • gen V X := by
  simp only [gen, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  module

private lemma gen_add (H X Y : Matrix T T ℂ) : gen H (X + Y) = gen H X + gen H Y := by
  simp only [gen, Matrix.mul_add, Matrix.add_mul]
  module

private lemma gen_smul (H X : Matrix T T ℂ) (c : ℂ) : gen H (c • X) = c • gen H X := by
  simp only [gen, Matrix.mul_smul, Matrix.smul_mul]
  module

/-- The `p`-th iterate of the perturbed generator, expanded to second order in `ε`. -/
private lemma expansion (Q H V R : Matrix T T ℂ) (hQH : Q * H = H * Q) (hQR : Q * R = R)
    (hRQ : R * Q = R) (p : ℕ) :
    ∃ (A B : Matrix T T ℂ) (C : ℝ → Matrix T T ℂ), Continuous C ∧
      (∀ ε : ℝ, (gen (H + (ε : ℂ) • V))^[p] R = A + (ε : ℂ) • B + ((ε : ℂ) ^ 2) • C ε) ∧
      Q * A = A ∧ A * Q = A ∧ (Q * B).trace = 0 ∧ (p ≠ 0 → (Q * A).trace = 0) := by
  induction p with
  | zero => exact ⟨R, 0, fun _ => 0, continuous_const, fun ε => by simp, hQR, hRQ, by simp, by simp⟩
  | succ p ih =>
    obtain ⟨A, B, C, hC, hF, hQA, hAQ, -, -⟩ := ih
    refine ⟨gen H A, gen H B + gen V A,
      fun ε => gen H (C ε) + gen V B + (ε : ℂ) • gen V (C ε), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hc : Continuous fun ε : ℝ => (ε : ℂ) := Complex.continuous_ofReal
      unfold gen
      fun_prop
    · intro ε
      rw [Function.iterate_succ_apply', hF ε, gen_add_smul]
      simp only [gen_add, gen_smul]
      module
    · simp only [gen, Matrix.mul_smul, Matrix.mul_sub]
      rw [← Matrix.mul_assoc, hQH, Matrix.mul_assoc, hQA, ← Matrix.mul_assoc, hQA]
    · simp only [gen, Matrix.smul_mul, Matrix.sub_mul]
      rw [Matrix.mul_assoc, hAQ, Matrix.mul_assoc A H Q, ← hQH, ← Matrix.mul_assoc, hAQ]
    · rw [Matrix.mul_add, Matrix.trace_add, trace_mul_gen Q H B hQH, zero_add]
      simp only [gen, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub, Matrix.trace_sub]
      rw [Matrix.trace_mul_comm Q, Matrix.mul_assoc, hAQ, ← Matrix.mul_assoc, hQA,
        Matrix.trace_mul_comm V]
      simp
    · intro _
      exact trace_mul_gen Q H A hQH

end algebra

section blocks

variable {𝒥 E : Type} [Fintype 𝒥] [DecidableEq 𝒥] [Fintype E] [DecidableEq E] {n d : 𝒥 → ℕ}

local notation "Idx" => (Σ K : 𝒥, Fin (n K) × Fin (d K))

omit [Fintype 𝒥] in
private lemma encode_apply_same (J : 𝒥) (σ : Matrix (Fin (n J)) (Fin (n J)) ℂ)
    (ρ : Matrix (Fin (d J)) (Fin (d J)) ℂ) (x y : Fin (n J) × Fin (d J)) :
    encode n d J σ ρ ⟨J, x⟩ ⟨J, y⟩ = σ x.1 y.1 * ρ x.2 y.2 := by
  simp [encode, Matrix.blockDiagonal'_apply_eq]

omit [Fintype 𝒥] in
private lemma encode_apply_left (J : 𝒥) (σ : Matrix (Fin (n J)) (Fin (n J)) ℂ)
    (ρ : Matrix (Fin (d J)) (Fin (d J)) ℂ) {K : 𝒥} (h : K ≠ J) (x : Fin (n K) × Fin (d K))
    (y : Idx) : encode n d J σ ρ ⟨K, x⟩ y = 0 := by
  obtain ⟨K', y⟩ := y
  by_cases h' : K = K'
  · subst h'
    simp [encode, Matrix.blockDiagonal'_apply_eq, Pi.single_eq_of_ne h]
  · simp [encode, Matrix.blockDiagonal'_apply_ne _ _ _ h']

omit [Fintype 𝒥] in
private lemma encode_apply_right (J : 𝒥) (σ : Matrix (Fin (n J)) (Fin (n J)) ℂ)
    (ρ : Matrix (Fin (d J)) (Fin (d J)) ℂ) {K : 𝒥} (h : K ≠ J) (x : Idx)
    (y : Fin (n K) × Fin (d K)) : encode n d J σ ρ x ⟨K, y⟩ = 0 := by
  obtain ⟨K', x⟩ := x
  by_cases h' : K' = K
  · subst h'
    simp [encode, Matrix.blockDiagonal'_apply_eq, Pi.single_eq_of_ne h]
  · simp [encode, Matrix.blockDiagonal'_apply_ne _ _ _ h']

private lemma encode_mul_encode (J : 𝒥) (σ σ' : Matrix (Fin (n J)) (Fin (n J)) ℂ)
    (ρ ρ' : Matrix (Fin (d J)) (Fin (d J)) ℂ) :
    encode n d J σ ρ * encode n d J σ' ρ' = encode n d J (σ * σ') (ρ * ρ') := by
  unfold encode
  rw [← Matrix.blockDiagonal'_mul]
  congr 1
  funext K
  by_cases h : K = J
  · subst h; simp [Matrix.mul_kronecker_mul]
  · simp [Pi.single_eq_of_ne h]

private lemma encode_one_comm_blockOp (J : 𝒥) (σ : Matrix (Fin (n J)) (Fin (n J)) ℂ)
    (X : ∀ K, Matrix (Fin (d K)) (Fin (d K)) ℂ) :
    encode n d J σ 1 * blockOp n d X = blockOp n d X * encode n d J σ 1 := by
  unfold encode blockOp
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext K
  by_cases h : K = J
  · subst h; simp [← Matrix.mul_kronecker_mul]
  · simp [Pi.single_eq_of_ne h]

omit [DecidableEq 𝒥] in
private lemma trace_kron_one_mul (P : Matrix Idx Idx ℂ) (X : Matrix (Idx × E) (Idx × E) ℂ) :
    ((P ⊗ₖ (1 : Matrix E E ℂ)) * X).trace = (P * WildeQIT.partialTraceRight X).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, WildeQIT.partialTraceRight, Matrix.of_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  refine Finset.sum_congr rfl fun e _ => ?_
  simp

private lemma trace_upsilon (J : 𝒥) (j : Fin (n J) → ℂ) (ρd : Matrix (Fin (d J)) (Fin (d J)) ℂ)
    (Y : Matrix Idx Idx ℂ) :
    (upsilon n d J (encode n d J (Matrix.vecMulVec j (star j)) ρd) * upsilon n d J Y).trace =
      ρd.trace * (encode n d J (Matrix.vecMulVec j (star j)) 1 * Y).trace := by
  have hl : ∀ l l', upsilon n d J (encode n d J (Matrix.vecMulVec j (star j)) ρd) l l' =
      j l * star (j l') * ρd.trace := by
    intro l l'
    simp [upsilon, WildeQIT.partialTraceRight, encode_apply_same, Matrix.vecMulVec_apply,
      Matrix.trace, Finset.mul_sum]
  have inner : ∀ l m, ∑ s', encode n d J (Matrix.vecMulVec j (star j)) 1 ⟨J, (l, m)⟩ s' *
      Y s' ⟨J, (l, m)⟩ = ∑ l', j l * star (j l') * Y ⟨J, (l', m)⟩ ⟨J, (l, m)⟩ := by
    intro l m
    rw [Fintype.sum_sigma, Finset.sum_eq_single J]
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun l' _ => ?_
      simp [encode_apply_same, Matrix.vecMulVec_apply, Matrix.one_apply]
    · intro K _ hK
      simp [encode_apply_right _ _ _ hK]
    · simp
  have hr : (encode n d J (Matrix.vecMulVec j (star j)) 1 * Y).trace =
      ∑ l, ∑ l', j l * star (j l') * ∑ m, Y ⟨J, (l', m)⟩ ⟨J, (l, m)⟩ := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    rw [Fintype.sum_sigma, Finset.sum_eq_single J]
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [inner]
      rw [Finset.sum_comm]
      simp [Finset.mul_sum]
    · intro K _ hK
      simp [encode_apply_left _ _ _ hK]
    · simp
  rw [hr]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, hl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  simp only [upsilon, WildeQIT.partialTraceRight, Matrix.of_apply, Matrix.submatrix_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.mul_sum]
  ring

end blocks

end BaconThesis.Stability.Sol626

open BaconThesis.Stability BaconThesis.Stability.Sol626

theorem solution {𝒥 E ι : Type} [Fintype 𝒥] [DecidableEq 𝒥] [Fintype E] [DecidableEq E]
    [Fintype ι] (n d : 𝒥 → ℕ)
    (S : ι → Matrix (Σ K : 𝒥, Fin (n K) × Fin (d K)) (Σ K : 𝒥, Fin (n K) × Fin (d K)) ℂ)
    (B : ι → Matrix E E ℂ) (hS : ∀ α, IsBlockForm n d (S α))
    (hH : (∑ α, S α ⊗ₖ B α).IsHermitian)
    (HI : Matrix ((Σ K : 𝒥, Fin (n K) × Fin (d K)) × E) ((Σ K : 𝒥, Fin (n K) × Fin (d K)) × E) ℂ)
    (hHI : HI.IsHermitian)
    (J : 𝒥) (j : Fin (n J) → ℂ) (hj : star j ⬝ᵥ j = 1)
    (ρd : Matrix (Fin (d J)) (Fin (d J)) ℂ) (hρd : WildeQIT.IsDensityOperator ρd)
    (ρE : Matrix E E ℂ) (hρE : WildeQIT.IsDensityOperator ρE)
    (p : ℕ) (hp : 1 ≤ p) :
    (fun ε : ℝ => rate n d ((∑ α, S α ⊗ₖ B α) + (ε : ℂ) • HI)
        (encode n d J (Matrix.vecMulVec j (star j)) ρd) ρE J p) =O[𝓝 0] (fun ε : ℝ => ε ^ 2) := by
  classical
  set H0 := ∑ α, S α ⊗ₖ B α with hH0
  set ρ0 := encode n d J (Matrix.vecMulVec j (star j)) ρd with hρ0
  set R := ρ0 ⊗ₖ ρE with hR
  set Q := encode n d J (Matrix.vecMulVec j (star j)) 1 ⊗ₖ (1 : Matrix E E ℂ) with hQ
  have hjj : Matrix.vecMulVec j (star j) * Matrix.vecMulVec j (star j) =
      Matrix.vecMulVec j (star j) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hj, one_smul]
  have hQH : Q * H0 = H0 * Q := by
    rw [hH0, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    obtain ⟨X, hX⟩ := hS α
    rw [hQ, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hX, encode_one_comm_blockOp,
      Matrix.one_mul, Matrix.mul_one]
  have hQR : Q * R = R := by
    rw [hQ, hR, hρ0, ← Matrix.mul_kronecker_mul, encode_mul_encode, hjj, Matrix.one_mul,
      Matrix.one_mul]
  have hRQ : R * Q = R := by
    rw [hQ, hR, hρ0, ← Matrix.mul_kronecker_mul, encode_mul_encode, hjj, Matrix.mul_one,
      Matrix.mul_one]
  obtain ⟨A, Bm, C, hC, hF, -, -, hB, hA⟩ := expansion Q H0 HI R hQH hQR hRQ p
  have hrate : ∀ ε : ℝ, rate n d (H0 + (ε : ℂ) • HI) ρ0 ρE J p =
      (ε : ℂ) ^ 2 * (Q * C ε).trace := by
    intro ε
    have hHε : (H0 + (ε : ℂ) • HI).IsHermitian := by
      refine hH.add ?_
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, hHI.eq]
      simp
    have key : (Matrix.of fun a b => iteratedDeriv p
        (fun t : ℝ => evolvedState (H0 + (ε : ℂ) • HI) ρ0 ρE t a b) 0) =
        WildeQIT.partialTraceRight ((gen (H0 + (ε : ℂ) • HI))^[p] R) := by
      ext a b
      let L : Matrix ((Σ K : 𝒥, Fin (n K) × Fin (d K)) × E)
          ((Σ K : 𝒥, Fin (n K) × Fin (d K)) × E) ℂ →ₗ[ℂ] ℂ :=
        { toFun := fun X => ∑ k, X (a, k) (b, k)
          map_add' := fun X Y => by simp [Finset.sum_add_distrib]
          map_smul' := fun c X => by simp [Finset.mul_sum] }
      have h := congrFun (iteratedDeriv_evol L _ hHε p R) 0
      simpa [evolvedState, WildeQIT.partialTraceRight, L] using h
    unfold rate
    rw [key, trace_upsilon, ← trace_kron_one_mul, hρd.2, one_mul, hF ε, Matrix.mul_add,
      Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.trace_smul, Matrix.trace_smul, hA (by omega), hB]
    simp [hQ]
  simp_rw [hrate]
  have hc : Continuous fun ε : ℝ => (Q * C ε).trace :=
    (continuous_const.matrix_mul hC).matrix_trace
  have h1 : (fun ε : ℝ => (Q * C ε).trace) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    (hc.tendsto 0).isBigO_one ℝ
  have h2 : (fun ε : ℝ => (ε : ℂ) ^ 2) =O[𝓝 0] (fun ε : ℝ => ε ^ 2) :=
    isBigO_of_le _ fun ε => by simp
  simpa using h2.mul h1
