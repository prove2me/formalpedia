-- Prove2me | solution 1 for FatkhullinPolyak.Discrete.gradient_method_slqr_linear_rate
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-18T07:34:53.057986+00:00
-- url     : https://prove2.me/submissions/88190647-3f83-4b87-8bf4-7fb6ea2e2d7e

-- Licensed under Apache 2.0. Complete state-feedback LQR gradient convergence theorem.
import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology


namespace LQRProof
open FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius

theorem frobNorm_eq_norm {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    frobNorm A = ‖A‖ := by
  rw [Matrix.frobenius_norm_def, frobNorm, Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]

theorem frobInner_self {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    frobInner A A = ‖A‖ ^ 2 := by
  rw [← frobNorm_eq_norm, frobNorm, Real.sq_sqrt]
  · simp only [frobInner, pow_two]
  · positivity

theorem frobInner_trace {p q : ℕ} (A B : Matrix (Fin p) (Fin q) ℝ) :
    frobInner A B = Matrix.trace (A.transpose * B) := by
  simp only [frobInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem frobInner_comm {p q : ℕ} (A B : Matrix (Fin p) (Fin q) ℝ) :
    frobInner A B = frobInner B A := by
  simp only [frobInner, mul_comm]

theorem frobInner_cauchy {p q : ℕ} (A B : Matrix (Fin p) (Fin q) ℝ) :
    |frobInner A B| ≤ ‖A‖ * ‖B‖ := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (Fin p × Fin q)))
    (f := fun ij => A ij.1 ij.2) (g := fun ij => B ij.1 ij.2)
  simp only [Fintype.sum_prod_type] at h
  have ha : (∑ i, ∑ j, A i j ^ 2) = ‖A‖ ^ 2 := by
    simpa only [frobInner, pow_two] using frobInner_self A
  have hb : (∑ i, ∑ j, B i j ^ 2) = ‖B‖ ^ 2 := by
    simpa only [frobInner, pow_two] using frobInner_self B
  rw [ha, hb] at h
  change frobInner A B ^ 2 ≤ ‖A‖ ^ 2 * ‖B‖ ^ 2 at h
  have hn : 0 ≤ ‖A‖ * ‖B‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [sq_abs (frobInner A B)]

end LQRProof


namespace LQRProof
open FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius MatrixOrder

theorem posDef_lower {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.PosDef) :
    ∃ r : ℝ, 0 < r ∧ (W - r • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  by_cases hn : n = 0
  · subst n
    refine ⟨1, zero_lt_one, ?_⟩
    have he : W - (1 : ℝ) • (1 : Matrix (Fin 0) (Fin 0) ℝ) = 0 := Subsingleton.elim _ _
    rw [he]
    exact Matrix.PosSemidef.zero
  · let : NeZero n := ⟨hn⟩
    obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff hW.isStrictlyPositive.isSelfAdjoint).2
      (fun z hz => hW.isStrictlyPositive.spectrum_pos hz)
    refine ⟨r, hr, ?_⟩
    simpa only [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] using hle

theorem trace_mul_nonneg {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ Matrix.trace (A * B) := by
  have h := (hA.hadamard hB).dotProduct_mulVec_nonneg (fun _ => 1)
  have hs : A.transpose = A := by
    simpa using hA.isHermitian.eq
  have hh : 0 ≤ frobInner A B := by
    simpa only [frobInner, dotProduct, Matrix.mulVec, star_trivial,
      Matrix.hadamard_apply, Pi.one_apply, one_mul, mul_one] using h
  rw [frobInner_trace, hs] at hh
  exact hh

theorem trace_mul_lower {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} {r : ℝ}
    (hA : A.PosSemidef) (hB : (B - r • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) :
    r * Matrix.trace A ≤ Matrix.trace (A * B) := by
  have h := trace_mul_nonneg hA hB
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul] at h
  linarith

end LQRProof


namespace LQRProof
open FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius MatrixOrder

theorem psd_norm_le_trace {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : ‖A‖ ≤ Matrix.trace A := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have he : A = B.transpose * B := by simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hB
  rw [he]
  calc
    ‖B.transpose * B‖ ≤ ‖B.transpose‖ * ‖B‖ := Matrix.frobenius_norm_mul _ _
    _ = ‖B‖ ^ 2 := by rw [Matrix.frobenius_norm_transpose]; ring
    _ = Matrix.trace (B.transpose * B) := by rw [← frobInner_self, frobInner_trace]

theorem trace_cost_controls_norm {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosDef) : ∃ r : ℝ, 0 < r ∧ ∀ X : Matrix (Fin n) (Fin n) ℝ,
      X.PosSemidef → r * ‖X‖ ≤ Matrix.trace (X * S) := by
  obtain ⟨r, hr, hbound⟩ := posDef_lower hS
  refine ⟨r, hr, fun X hX => ?_⟩
  exact (mul_le_mul_of_nonneg_left (psd_norm_le_trace hX) hr.le).trans
    (trace_mul_lower hX hbound)

theorem trace_transpose_coercive {m n : ℕ} {R : Matrix (Fin m) (Fin m) ℝ}
    {r : ℝ} (hR : (R - r • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef)
    (K : Matrix (Fin m) (Fin n) ℝ) :
    r * ‖K‖ ^ 2 ≤ Matrix.trace (K.transpose * R * K) := by
  have hh : (K * K.transpose).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose K
  have hb := trace_mul_lower hh hR
  rw [Matrix.trace_mul_comm K K.transpose, ← frobInner_trace, frobInner_self] at hb
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle] at hb
  exact hb

end LQRProof


namespace LQRProof
open FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius

theorem trace_lyapunov_duality {n : ℕ} (M X Y W S : Matrix (Fin n) (Fin n) ℝ)
    (hX : M.transpose * X + X * M + W = 0)
    (hY : M * Y + Y * M.transpose + S = 0) :
    Matrix.trace (X * S) = Matrix.trace (W * Y) := by
  have hx := congrArg (fun Z => Matrix.trace (Z * Y)) hX
  have hy := congrArg (fun Z => Matrix.trace (X * Z)) hY
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, Matrix.zero_mul,
    Matrix.mul_zero, Matrix.trace_zero] at hx hy
  have h1 : Matrix.trace (M.transpose * X * Y) = Matrix.trace (X * (Y * M.transpose)) := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm M.transpose (X * Y), Matrix.mul_assoc]
  have h2 : Matrix.trace (X * M * Y) = Matrix.trace (X * (M * Y)) := by
    rw [Matrix.mul_assoc]
  rw [h1, h2] at hx
  linarith

theorem trace_gradient_pair {n m : ℕ} (E : Matrix (Fin m) (Fin n) ℝ)
    (Y : Matrix (Fin n) (Fin n) ℝ) (H : Matrix (Fin m) (Fin n) ℝ)
    (hY : Y.transpose = Y) :
    Matrix.trace ((H.transpose * E + E.transpose * H) * Y) =
      frobInner ((2 : ℝ) • (E * Y)) H := by
  rw [Matrix.add_mul, Matrix.trace_add, frobInner_trace, Matrix.transpose_smul,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.transpose_mul, hY]
  have h1 : Matrix.trace (H.transpose * E * Y) = Matrix.trace (Y * E.transpose * H) := by
    rw [← Matrix.trace_transpose (H.transpose * E * Y)]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hY, Matrix.mul_assoc]
  have h2 : Matrix.trace (E.transpose * H * Y) = Matrix.trace (Y * E.transpose * H) :=
    Matrix.trace_mul_cycle _ _ _
  rw [h1, h2]
  ring

end LQRProof


noncomputable section
namespace LQRProof
open Matrix Polynomial

lemma polynomial_intertwine {n : ℕ} (P S Z : Matrix (Fin n) (Fin n) ℂ)
    (h : P * Z = Z * S) (p : ℂ[X]) :
    aeval P p * Z = Z * aeval S p := by
  induction p using Polynomial.induction_on with
  | C a => simp [Algebra.algebraMap_eq_smul_one]
  | add p q hp hq => simp only [map_add, add_mul, mul_add, hp, hq]
  | monomial k a ih =>
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X, mul_assoc, h,
        ← mul_assoc, ih, mul_assoc]
      simp only [map_mul, aeval_X]

lemma sylvester_zero {n : ℕ} (P S Z : Matrix (Fin n) (Fin n) ℂ)
    (hdis : Disjoint (spectrum ℂ P) (spectrum ℂ S)) (h : P * Z = Z * S) : Z = 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    exact Subsingleton.elim _ _
  have hd : 0 < P.charpoly.degree := by
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hu : IsUnit (aeval S P.charpoly) := by
    apply spectrum.isUnit_of_zero_notMem ℂ
    rw [spectrum.map_polynomial_aeval_of_degree_pos S P.charpoly hd]
    rintro ⟨z, hz, he⟩
    have hp : z ∈ spectrum ℂ P := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr he
    exact Set.disjoint_left.mp hdis hp hz
  have hz := polynomial_intertwine P S Z h P.charpoly
  rw [Matrix.aeval_self_charpoly, zero_mul] at hz
  apply hu.mul_right_cancel
  simpa only [zero_mul] using hz.symm

end LQRProof


noncomputable section
namespace LQRProof
open Matrix FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius

lemma hurwitz_transpose {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsHurwitz M) : IsHurwitz M.transpose := by
  intro z hz
  apply hM z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hz ⊢
  change Polynomial.IsRoot (M.map (algebraMap ℝ ℂ)).transpose.charpoly z at hz
  simpa only [Matrix.charpoly_transpose] using hz

lemma lyapunov_homogeneous_zero {n : ℕ} {M Z : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsHurwitz M) (hZ : M.transpose * Z + Z * M = 0) : Z = 0 := by
  classical
  let c : Matrix (Fin n) (Fin n) ℝ →+* Matrix (Fin n) (Fin n) ℂ :=
    (algebraMap ℝ ℂ).mapMatrix
  have hd : Disjoint (spectrum ℂ (c M).transpose) (spectrum ℂ (-c M)) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have hn : z.re < 0 := by
      apply hM z
      rwa [Matrix.mem_spectrum_iff_isRoot_charpoly,
        Matrix.charpoly_transpose, ← Matrix.mem_spectrum_iff_isRoot_charpoly] at hz
    have hp : (-z).re < 0 := by
      apply hM (-z)
      rw [← spectrum.neg_eq, Set.mem_neg] at hz'
      exact hz'
    simp only [Complex.neg_re] at hp
    linarith
  have he : (c M).transpose * c Z = c Z * (-c M) := by
    have hc := congrArg c hZ
    simp only [map_add, map_mul, map_zero] at hc
    change (c M).transpose * c Z + c Z * c M = 0 at hc
    rw [mul_neg]
    exact eq_neg_of_add_eq_zero_left hc
  have hz := sylvester_zero (c M).transpose (-c M) (c Z) hd he
  ext i j
  have hij := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) hz
  change ((Z i j : ℝ) : ℂ) = 0 at hij
  exact_mod_cast hij

def lyapunovLinear {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun Z := M.transpose * Z + Z * M
  map_add' U V := by simp only [mul_add, add_mul]; abel
  map_smul' a Z := by simp only [mul_smul_comm, smul_mul_assoc, smul_add, RingHom.id_apply]

lemma lyapunovLinear_injective {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsHurwitz M) : Function.Injective (lyapunovLinear M) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro Z hZ
  exact lyapunov_homogeneous_zero hM hZ

lemma lyapunov_existsUnique {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsHurwitz M) (W : Matrix (Fin n) (Fin n) ℝ) :
    ∃! X, M.transpose * X + X * M + W = 0 := by
  have hi := lyapunovLinear_injective hM
  obtain ⟨X, hX⟩ := (LinearMap.injective_iff_surjective.mp hi) (-W)
  refine ⟨X, ?_, ?_⟩
  · change lyapunovLinear M X + W = 0
    rw [hX, neg_add_cancel]
  · intro Y hY
    apply hi
    change M.transpose * Y + Y * M = lyapunovLinear M X
    rw [hX]
    exact eq_neg_of_add_eq_zero_left hY

lemma lyapSol_equation {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsHurwitz M) (W : Matrix (Fin n) (Fin n) ℝ) :
    M.transpose * lyapSol M W + lyapSol M W * M + W = 0 := by
  classical
  rw [lyapSol, dif_pos (lyapunov_existsUnique hM W)]
  exact (lyapunov_existsUnique hM W).choose_spec.1

lemma lyapSol_unique {n : ℕ} {M W X : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsHurwitz M) (hX : M.transpose * X + X * M + W = 0) :
    X = lyapSol M W := by
  exact (lyapunov_existsUnique hM W).unique hX (lyapSol_equation hM W)

lemma lyapSol_symmetric {n : ℕ} {M W : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsHurwitz M) (hW : W.transpose = W) :
    (lyapSol M W).transpose = lyapSol M W := by
  apply lyapSol_unique hM
  have hh := congrArg Matrix.transpose (lyapSol_equation hM W)
  simpa only [transpose_add, transpose_mul, transpose_transpose, transpose_zero,
    hW, add_comm] using hh

lemma lyapSol_add {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsHurwitz M) (W V : Matrix (Fin n) (Fin n) ℝ) :
    lyapSol M (W + V) = lyapSol M W + lyapSol M V := by
  symm
  apply lyapSol_unique hM
  have hW := lyapSol_equation hM W
  have hV := lyapSol_equation hM V
  simp only [mul_add, add_mul]
  calc
    _ = (M.transpose * lyapSol M W + lyapSol M W * M + W) +
        (M.transpose * lyapSol M V + lyapSol M V * M + V) := by abel
    _ = 0 := by rw [hW, hV, add_zero]

lemma lyapSol_smul {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsHurwitz M) (a : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) :
    lyapSol M (a • W) = a • lyapSol M W := by
  symm
  apply lyapSol_unique hM
  simpa only [mul_smul_comm, smul_mul_assoc, ← smul_add, smul_zero]
    using congrArg (a • ·) (lyapSol_equation hM W)

end LQRProof


noncomputable section
namespace LQRProof
open Matrix FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

local instance (n : ℕ) : TopologicalSpace (Mat n) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)).toUniformSpace.toTopologicalSpace

def lyapunovCLM {n : ℕ} (M : Mat n) : Mat n →L[ℝ] Mat n :=
  (lyapunovLinear M).toContinuousLinearMap

lemma lyapunovCLM_apply {n : ℕ} (M X : Mat n) :
    lyapunovCLM M X = M.transpose * X + X * M := rfl

def lyapunovParameter (n : ℕ) : Mat n →L[ℝ] (Mat n →L[ℝ] Mat n) :=
  LinearMap.toContinuousLinearMap
    { toFun := lyapunovCLM
      map_add' := fun M N => by
        ext X i j
        simp only [lyapunovCLM_apply, transpose_add, add_mul, mul_add,
          _root_.add_apply, Matrix.add_apply]
        ring
      map_smul' := fun a M => by
        ext X i j
        simp only [lyapunovCLM_apply, transpose_smul, smul_mul_assoc, mul_smul_comm,
          ← smul_add, _root_.smul_apply, RingHom.id_apply] }

lemma lyapunovCLM_invertible_of_injective {n : ℕ} {M : Mat n}
    (hi : Function.Injective (lyapunovLinear M)) : (lyapunovCLM M).IsInvertible := by
  let e := LinearEquiv.ofBijective (lyapunovLinear M)
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  exact ⟨e.toContinuousLinearEquiv, rfl⟩

lemma lyapunovCLM_invertible {n : ℕ} {M : Mat n} (hM : IsHurwitz M) :
    (lyapunovCLM M).IsInvertible :=
  lyapunovCLM_invertible_of_injective (lyapunovLinear_injective hM)

lemma unique_lyapunov_injective {n : ℕ} {M W : Mat n}
    (hu : ∃! X, M.transpose * X + X * M + W = 0) :
    Function.Injective (lyapunovLinear M) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro Z hZ
  obtain ⟨X, hX, hu⟩ := hu
  have hxz : M.transpose * (X + Z) + (X + Z) * M + W = 0 := by
    change M.transpose * Z + Z * M = 0 at hZ
    simp only [mul_add, add_mul]
    calc
      _ = (M.transpose * X + X * M + W) + (M.transpose * Z + Z * M) := by abel
      _ = 0 := by rw [hX, hZ, add_zero]
  have he := hu (X + Z) hxz
  exact add_left_cancel (he.trans (add_zero X).symm)

lemma lyapSol_eq_inverse {n : ℕ} (M W : Mat n) :
    lyapSol M W = (lyapunovCLM M).inverse (-W) := by
  classical
  by_cases hi : Function.Injective (lyapunovLinear M)
  · have hv := lyapunovCLM_invertible_of_injective hi
    have he : M.transpose * (lyapunovCLM M).inverse (-W) +
        (lyapunovCLM M).inverse (-W) * M + W = 0 := by
      change lyapunovCLM M ((lyapunovCLM M).inverse (-W)) + W = 0
      rw [hv.self_apply_inverse, neg_add_cancel]
    have hu : ∃! X, M.transpose * X + X * M + W = 0 := by
      refine ⟨_, he, ?_⟩
      intro X hX
      apply hi
      change M.transpose * X + X * M =
        M.transpose * (lyapunovCLM M).inverse (-W) + (lyapunovCLM M).inverse (-W) * M
      exact (eq_neg_of_add_eq_zero_left hX).trans (eq_neg_of_add_eq_zero_left he).symm
    rw [lyapSol, dif_pos hu]
    exact hu.unique hu.choose_spec.1 he
  · have hu : ¬ ∃! X, M.transpose * X + X * M + W = 0 :=
      fun h => hi (unique_lyapunov_injective h)
    have hv : ¬ (lyapunovCLM M).IsInvertible := fun h => hi h.injective
    rw [lyapSol, dif_neg hu, ContinuousLinearMap.inverse_of_not_isInvertible hv]
    rfl

lemma lyapSol_contDiffAt {n : ℕ} {M W : Mat n} (hM : IsHurwitz M) :
    ContDiffAt ℝ ⊤ (fun p : Mat n × Mat n => lyapSol p.1 p.2) (M,W) := by
  have h1 : ContDiffAt ℝ ⊤ (fun p : Mat n × Mat n =>
      (lyapunovCLM p.1).inverse) (M,W) :=
    (lyapunovCLM_invertible hM).contDiffAt_map_inverse.comp (M,W)
      ((lyapunovParameter n).contDiff.contDiffAt.comp (M,W) contDiffAt_fst)
  simpa only [lyapSol_eq_inverse] using h1.clm_apply contDiffAt_snd.neg

lemma lyapSol_continuousAt {n : ℕ} {M W : Mat n} (hM : IsHurwitz M) :
    ContinuousAt (fun p : Mat n × Mat n => lyapSol p.1 p.2) (M,W) :=
  (lyapSol_contDiffAt hM).continuousAt

end LQRProof


noncomputable section
namespace LQRProof
open FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius

local instance (p q : ℕ) : TopologicalSpace (Matrix (Fin p) (Fin q) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin p) (n := Fin q) (α := ℝ)).toUniformSpace.toTopologicalSpace

def matrixMulCLM (p q r : ℕ) : Matrix (Fin p) (Fin q) ℝ →L[ℝ]
    Matrix (Fin q) (Fin r) ℝ →L[ℝ] Matrix (Fin p) (Fin r) ℝ :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp
    (mulLinearMap (l := Fin p) (m := Fin q) (n := Fin r) ℝ)).toContinuousLinearMap

theorem matrixMulCLM_apply {p q r : ℕ} (A : Matrix (Fin p) (Fin q) ℝ)
    (B : Matrix (Fin q) (Fin r) ℝ) : matrixMulCLM p q r A B = A * B := rfl

def transposeCLM (p q : ℕ) : Matrix (Fin p) (Fin q) ℝ →L[ℝ]
    Matrix (Fin q) (Fin p) ℝ :=
  (Matrix.transposeLinearEquiv (Fin p) (Fin q) ℝ ℝ).toLinearMap.toContinuousLinearMap

theorem transposeCLM_apply {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    transposeCLM p q A = A.transpose := rfl

def traceCLM (n : ℕ) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin n) ℝ ℝ).toContinuousLinearMap

theorem hasDerivAt_matrix_mul {p q r : ℕ}
    {f : ℝ → Matrix (Fin p) (Fin q) ℝ} {g : ℝ → Matrix (Fin q) (Fin r) ℝ}
    {a : Matrix (Fin p) (Fin q) ℝ} {b : Matrix (Fin q) (Fin r) ℝ} {t : ℝ}
    (hf : HasDerivAt f a t) (hg : HasDerivAt g b t) :
    HasDerivAt (fun s => f s * g s) (a * g t + f t * b) t := by
  simpa only [Function.comp_def, matrixMulCLM_apply] using
    (((matrixMulCLM p q r).hasFDerivAt.comp_hasDerivAt t hf).clm_apply hg)

theorem hasDerivAt_transpose {p q : ℕ}
    {f : ℝ → Matrix (Fin p) (Fin q) ℝ} {a : Matrix (Fin p) (Fin q) ℝ} {t : ℝ}
    (hf : HasDerivAt f a t) : HasDerivAt (fun s => (f s).transpose) a.transpose t := by
  exact (transposeCLM p q).hasFDerivAt.comp_hasDerivAt t hf

theorem contDiffAt_matrix_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q r : ℕ} {f : E → Matrix (Fin p) (Fin q) ℝ}
    {g : E → Matrix (Fin q) (Fin r) ℝ} {x : E}
    (hf : ContDiffAt ℝ ⊤ f x) (hg : ContDiffAt ℝ ⊤ g x) :
    ContDiffAt ℝ ⊤ (fun z => f z * g z) x := by
  simpa only [Function.comp_def, matrixMulCLM_apply] using
    ((matrixMulCLM p q r).contDiff.contDiffAt.comp x hf).clm_apply hg

end LQRProof


noncomputable section
namespace LQRProof
open FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius

local instance (p q : ℕ) : TopologicalSpace (Matrix (Fin p) (Fin q) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin p) (n := Fin q) (α := ℝ)).toUniformSpace.toTopologicalSpace

theorem state_X_contDiffAt {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) {K : Matrix (Fin m) (Fin n) ℝ}
    (hK : K ∈ stabSet A B 1) : ContDiffAt ℝ ⊤ (lyapX A B 1 Q R) K := by
  have hm : ContDiffAt ℝ ⊤ (fun J : Matrix (Fin m) (Fin n) ℝ => A-B*J) K :=
    contDiffAt_const.sub (contDiffAt_matrix_mul contDiffAt_const contDiffAt_id)
  have ht : ContDiffAt ℝ ⊤ (fun J : Matrix (Fin m) (Fin n) ℝ => J.transpose) K :=
    (transposeCLM m n).contDiff.contDiffAt
  have hw : ContDiffAt ℝ ⊤ (fun J : Matrix (Fin m) (Fin n) ℝ => J.transpose*R*J+Q) K :=
    (contDiffAt_matrix_mul (contDiffAt_matrix_mul ht contDiffAt_const) contDiffAt_id).add
      contDiffAt_const
  have hh : IsHurwitz (A-B*K) := by simpa only [stabSet, Set.mem_ofPred_eq, Matrix.mul_one] using hK
  have hs := (lyapSol_contDiffAt (W := K.transpose*R*K+Q) hh).comp K (hm.prodMk hw)
  change ContDiffAt ℝ ⊤ (fun J => lyapX A B 1 Q R J) K
  simpa only [Function.comp_def, lyapX, Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one] using hs

theorem state_Y_contDiffAt {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    {K : Matrix (Fin m) (Fin n) ℝ} (hK : K ∈ stabSet A B 1) :
    ContDiffAt ℝ ⊤ (lyapY A B 1 S) K := by
  have hm : ContDiffAt ℝ ⊤ (fun J : Matrix (Fin m) (Fin n) ℝ => A-B*J) K :=
    contDiffAt_const.sub (contDiffAt_matrix_mul contDiffAt_const contDiffAt_id)
  have ht := (transposeCLM n n).contDiff.contDiffAt.comp K hm
  have hh : IsHurwitz (A-B*K) := by simpa only [stabSet, Set.mem_ofPred_eq, Matrix.mul_one] using hK
  have hs := (lyapSol_contDiffAt (W := S) (hurwitz_transpose hh)).comp K
    (ht.prodMk contDiffAt_const)
  change ContDiffAt ℝ ⊤ (fun J => lyapY A B 1 S J) K
  simpa only [Function.comp_def, lyapY, Matrix.mul_one, transposeCLM_apply] using hs

end LQRProof


noncomputable section
namespace LQRProof
open Matrix Filter Topology
open scoped Matrix.Norms.Frobenius

lemma posDef_of_unit_quadratic {n : ℕ} {A : Mat n} (hA : A.IsHermitian)
    (h : ∀ v : Fin n → ℝ, ‖v‖ = 1 → 0 < v ⬝ᵥ (A *ᵥ v)) : A.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hA
  intro v hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  have hh := h ((‖v‖⁻¹ : ℝ) • v) hw
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at hh
  simp only [star_trivial]
  by_contra hneg
  have hle : v ⬝ᵥ (A *ᵥ v) ≤ 0 := le_of_not_gt hneg
  have hi : 0 ≤ ‖v‖⁻¹ := inv_nonneg.mpr hn.le
  have hz := mul_nonpos_of_nonneg_of_nonpos hi (mul_nonpos_of_nonneg_of_nonpos hi hle)
  nlinarith


lemma continuous_quadratic {n : ℕ} :
    Continuous (fun p : Mat n × (Fin n → ℝ) => p.2 ⬝ᵥ (p.1 *ᵥ p.2)) := by
  unfold dotProduct Matrix.mulVec
  fun_prop

lemma eventually_posDef_of_continuousAt {n : ℕ} {α : Type*} [TopologicalSpace α]
    {F : α → Mat n} {a : α} (hc : ContinuousAt F a)
    (hs : ∀ b, (F b).IsHermitian) (hp : (F a).PosDef) :
    ∀ᶠ b in 𝓝 a, (F b).PosDef := by
  have he : ∀ᶠ b in 𝓝 a, ∀ v ∈ Metric.sphere (0 : Fin n → ℝ) 1,
      0 < v ⬝ᵥ (F b *ᵥ v) := by
    apply (isCompact_sphere (0 : Fin n → ℝ) 1).eventually_forall_of_forall_eventually
    intro v hv
    have hv' : v ≠ 0 := by
      have : ‖v‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hv
      intro h; simp [h] at this
    have hq : 0 < v ⬝ᵥ (F a *ᵥ v) := by
      simpa only [star_trivial] using hp.dotProduct_mulVec_pos hv'
    have hcont : ContinuousAt (fun p : α × (Fin n → ℝ) => p.2 ⬝ᵥ (F p.1 *ᵥ p.2)) (a,v) :=
      continuous_quadratic.continuousAt.comp ((hc.comp continuousAt_fst).prodMk continuousAt_snd)
    exact hcont.eventually (lt_mem_nhds hq)
  filter_upwards [he] with b hb
  apply posDef_of_unit_quadratic (hs b)
  intro v hv
  exact hb v (by simpa only [Metric.mem_sphere, dist_zero_right] using hv)

lemma isClosed_posSemidef_family {n : ℕ} {α : Type*} [TopologicalSpace α]
    {F : α → Mat n} (hc : Continuous F) (hs : ∀ b, (F b).IsHermitian) :
    IsClosed {b | (F b).PosSemidef} := by
  have he : {b | (F b).PosSemidef} =
      ⋂ v : Fin n → ℝ, {b | 0 ≤ v ⬝ᵥ (F b *ᵥ v)} := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h v
      simpa only [star_trivial] using h.dotProduct_mulVec_nonneg v
    · intro h
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hs b)
      simpa only [star_trivial] using h
  rw [he]
  apply isClosed_iInter
  intro v
  exact isClosed_le continuous_const
    (continuous_quadratic.comp (hc.prodMk continuous_const))

end LQRProof


noncomputable section
namespace LQRProof
open Matrix Polynomial FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius

def hurwitzPath {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :=
  (1-t) • M - t • (1 : Matrix (Fin n) (Fin n) ℝ)

lemma hurwitzPath_stable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsHurwitz M) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsHurwitz (hurwitzPath M t) := by
  classical
  by_cases hn : n = 0
  · subst n
    intro z hz
    simp only [spectrum.of_subsingleton, Set.mem_empty_iff_false] at hz
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  let : Nonempty (Fin n) := ⟨⟨0, hn'⟩⟩
  let A := M.map (algebraMap ℝ ℂ)
  let p : ℂ[X] := C ((1-t : ℝ) : ℂ) * X - C (t : ℂ)
  have he : (hurwitzPath M t).map (algebraMap ℝ ℂ) = aeval A p := by
    simp only [p, map_sub, map_mul, aeval_C, aeval_X,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    ext i j
    by_cases hij : i = j <;> simp [hurwitzPath, A, Matrix.smul_apply, hij]
  intro z hz
  rw [he, spectrum.map_polynomial_aeval_of_nonempty A p
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ A)] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hw' := hM w hw
  simp only [p, eval_sub, eval_mul, eval_C, eval_X, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · have : 0 < 1-t := sub_pos.mpr hlt
    have ht0 : 0 ≤ t := ht.1
    have hh := mul_neg_of_pos_of_neg this hw'
    linarith
  · norm_num

lemma hurwitzPath_continuous {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (hurwitzPath M) := by
  unfold hurwitzPath
  fun_prop

lemma hurwitzPath_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    hurwitzPath M 0 = M := by simp [hurwitzPath]

lemma hurwitzPath_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    hurwitzPath M 1 = -1 := by simp [hurwitzPath]

end LQRProof


noncomputable section
namespace LQRProof
open Matrix FatkhullinPolyak.Discrete Set Filter Topology
open scoped Matrix.Norms.Frobenius unitInterval

local instance (n : ℕ) : TopologicalSpace (Mat n) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)).toUniformSpace.toTopologicalSpace

lemma lyapunov_psd_posDef {n : ℕ} {M X W : Mat n}
    (hX : X.PosSemidef) (hW : W.PosDef)
    (he : M.transpose * X + X * M + W = 0) : X.PosDef := by
  apply hX.posDef_iff_isUnit.mpr
  apply Matrix.mulVec_injective_iff_isUnit.mp
  change Function.Injective X.mulVecLin
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change X *ᵥ v = 0 at hv
  by_contra hn
  have hp : 0 < v ⬝ᵥ (W *ᵥ v) := by
    simpa only [star_trivial] using hW.dotProduct_mulVec_pos hn
  have hs : X.transpose = X := by simpa using hX.isHermitian.eq
  have hz : v ⬝ᵥ (X *ᵥ (M *ᵥ v)) = 0 := by
    rw [← hs, Matrix.dotProduct_transpose_mulVec, hv, dotProduct_zero]
  have hh := congrArg (fun A : Mat n => v ⬝ᵥ (A *ᵥ v)) he
  simp only [add_mulVec, ← mulVec_mulVec, dotProduct_add, hv, mulVec_zero,
    dotProduct_zero, zero_mulVec, hz, zero_add] at hh
  linarith

lemma lyapSol_posDef {n : ℕ} {M W : Mat n}
    (hM : IsHurwitz M) (hW : W.PosDef) : (lyapSol M W).PosDef := by
  let F : I → Mat n := fun t => lyapSol (hurwitzPath M t) W
  have hc : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hp : ContinuousAt (fun u : I => (hurwitzPath M (u : ℝ), W)) t :=
      ((hurwitzPath_continuous M).continuousAt.comp continuous_subtype_val.continuousAt).prodMk continuousAt_const
    exact ContinuousAt.comp
      (g := fun p : Mat n × Mat n => lyapSol p.1 p.2)
      (f := fun u : I => (hurwitzPath M (u : ℝ), W))
      (lyapSol_continuousAt (hurwitzPath_stable hM t.property)) hp
  have hs : ∀ t, (F t).IsHermitian := by
    intro t
    have hw : W.transpose = W := by simpa using hW.isHermitian.eq
    have hh := lyapSol_symmetric (hurwitzPath_stable hM t.property) hw
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hh
  have he : ∀ t, (F t).PosDef ↔ (F t).PosSemidef := by
    intro t
    refine ⟨fun h => h.posSemidef, fun h => ?_⟩
    exact lyapunov_psd_posDef h hW (lyapSol_equation (hurwitzPath_stable hM t.property) W)
  have hclosed : IsClosed {t | (F t).PosDef} := by
    simpa only [he] using isClosed_posSemidef_family hc hs
  have hopen : IsOpen {t | (F t).PosDef} := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    exact eventually_posDef_of_continuousAt hc.continuousAt hs ht
  have h1 : (F 1).PosDef := by
    have heq : F 1 = (1/2 : ℝ) • W := by
      symm
      apply lyapSol_unique (hurwitzPath_stable hM (show (1:ℝ) ∈ Icc 0 1 by simp))
      simp only [hurwitzPath_one, transpose_neg, transpose_one, neg_mul, one_mul,
        mul_neg, mul_one]
      module
    rw [heq]
    exact hW.smul (by norm_num)
  have hall := (show IsClopen {t | (F t).PosDef} from ⟨hclosed,hopen⟩).eq_univ ⟨1,h1⟩
  have h0 : (0 : I) ∈ {t | (F t).PosDef} := by rw [hall]; trivial
  change (lyapSol (hurwitzPath M 0) W).PosDef at h0
  rwa [hurwitzPath_zero] at h0

lemma lyapSol_posSemidef {n : ℕ} {M W : Mat n}
    (hM : IsHurwitz M) (hW : W.PosSemidef) : (lyapSol M W).PosSemidef := by
  let F : ℝ → Mat n := fun ε => lyapSol M (W + ε • 1)
  have hc : ContinuousAt F (0 : ℝ) := by
    have hp : ContinuousAt (fun ε : ℝ => (M, W + ε • (1 : Mat n))) 0 := by fun_prop
    have hh := (lyapSol_continuousAt (M := M) (W := W) hM)
    have hh0 : ContinuousAt (fun p : Mat n × Mat n => lyapSol p.1 p.2)
        (M, W + (0 : ℝ) • (1 : Mat n)) := by simpa only [zero_smul, add_zero] using hh
    exact ContinuousAt.comp
      (g := fun p : Mat n × Mat n => lyapSol p.1 p.2)
      (f := fun ε : ℝ => (M, W + ε • (1 : Mat n))) hh0 hp
  have hs : ∀ ε, (F ε).IsHermitian := by
    intro ε
    have hw : (W + ε • (1 : Mat n)).transpose = W + ε • (1 : Mat n) := by
      have hh : W.transpose = W := by simpa using hW.isHermitian.eq
      simp only [transpose_add, transpose_smul, transpose_one, hh]
    have hh := lyapSol_symmetric hM hw
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hh
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (by simpa [F] using hs 0)
  intro v
  have ht : Tendsto (fun ε : ℝ => star v ⬝ᵥ (F ε *ᵥ v)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (star v ⬝ᵥ (lyapSol M W *ᵥ v))) := by
    have : ContinuousAt (fun ε : ℝ => star v ⬝ᵥ (F ε *ᵥ v)) 0 := by
      simpa only [star_trivial, Function.comp_def] using
        continuous_quadratic.continuousAt.comp (hc.prodMk (continuousAt_const (y := v)))
    have hh : Tendsto (fun ε : ℝ => star v ⬝ᵥ (F ε *ᵥ v))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (𝓝 (star v ⬝ᵥ (F 0 *ᵥ v))) := this.continuousWithinAt.tendsto
    simpa only [F, zero_smul, add_zero] using hh
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hpos : (W + ε • (1 : Mat n)).PosDef :=
    Matrix.PosDef.posSemidef_add hW ((Matrix.PosDef.one).smul hε)
  exact (lyapSol_posDef hM hpos).posSemidef.dotProduct_mulVec_nonneg v

end LQRProof


namespace LQRProof
open FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius

theorem state_forcing_posDef {n m : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef) (hR : R.PosDef)
    (K : Matrix (Fin m) (Fin n) ℝ) : (K.transpose*R*K+Q).PosDef := by
  have h : (K.transpose*R*K).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hR.posSemidef.conjTranspose_mul_mul_same K
  exact Matrix.PosDef.posSemidef_add h hQ

theorem state_X_posDef {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {Q : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef) (hR : R.PosDef)
    {K : Matrix (Fin m) (Fin n) ℝ} (hK : K ∈ stabSet A B 1) :
    (lyapX A B 1 Q R K).PosDef := by
  have hm : IsHurwitz (A-B*K) := by simpa only [stabSet, Set.mem_ofPred_eq, Matrix.mul_one] using hK
  simpa only [lyapX, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] using
    lyapSol_posDef hm (state_forcing_posDef hQ hR K)

theorem state_Y_posDef {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosDef) {K : Matrix (Fin m) (Fin n) ℝ} (hK : K ∈ stabSet A B 1) :
    (lyapY A B 1 S K).PosDef := by
  have hm : IsHurwitz (A-B*K) := by simpa only [stabSet, Set.mem_ofPred_eq, Matrix.mul_one] using hK
  simpa only [lyapY, Matrix.mul_one] using lyapSol_posDef (hurwitz_transpose hm) hS

theorem state_cost_nonneg {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {Q : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.PosDef) (hR : R.PosDef) (hS : S.PosDef)
    {K : Matrix (Fin m) (Fin n) ℝ} (hK : K ∈ stabSet A B 1) :
    0 ≤ lqrCost A B 1 Q R S K :=
  trace_mul_nonneg (state_X_posDef A B hQ hR hK).posSemidef hS.posSemidef

end LQRProof


noncomputable section
namespace LQRProof
open Matrix FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius

lemma lyapunov_quadratic_identity {n : ℕ} {M X W : Mat n}
    (hs : X.transpose = X) (he : M.transpose * X + X * M + W = 0)
    (v : Fin n → ℝ) :
    2 * ((M *ᵥ v) ⬝ᵥ (X *ᵥ v)) + v ⬝ᵥ (W *ᵥ v) = 0 := by
  have hh := congrArg (fun A : Mat n => v ⬝ᵥ (A *ᵥ v)) he
  simp only [add_mulVec, ← mulVec_mulVec, dotProduct_add, zero_mulVec, dotProduct_zero] at hh
  have h1 := Matrix.dotProduct_transpose_mulVec M v (X *ᵥ v)
  have h2 := Matrix.dotProduct_transpose_mulVec X v (M *ᵥ v)
  rw [hs] at h2
  rw [h1, h2, dotProduct_comm (X *ᵥ v) (M *ᵥ v)] at hh
  linarith

lemma hurwitz_of_lyapunov {n : ℕ} {M X W : Mat n}
    (hX : X.PosSemidef) (hW : W.PosDef)
    (he : M.transpose * X + X * M + W = 0) : IsHurwitz M := by
  classical
  intro z hz
  let A := M.map (algebraMap ℝ ℂ)
  have heig : Module.End.HasEigenvalue A.toLin' z := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    rwa [Matrix.spectrum_toLin']
  obtain ⟨v, hv, hv0⟩ : ∃ v : Fin n → ℂ, A *ᵥ v = z • v ∧ v ≠ 0 := by
    simpa only [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff,
      Matrix.toLin'_apply] using heig.exists_hasEigenvector
  let a : Fin n → ℝ := fun i => (v i).re
  let b : Fin n → ℝ := fun i => (v i).im
  have ha : M *ᵥ a = z.re • a - z.im • b := by
    ext i
    have hh := congrArg (fun w : Fin n → ℂ => (w i).re) hv
    change (∑ j, (M i j : ℂ) * v j).re = (z * v i).re at hh
    simpa only [a, b, mulVec, dotProduct, Complex.re_sum,
      Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Pi.sub_apply] using hh
  have hb : M *ᵥ b = z.im • a + z.re • b := by
    ext i
    have hh := congrArg (fun w : Fin n → ℂ => (w i).im) hv
    change (∑ j, (M i j : ℂ) * v j).im = (z * v i).im at hh
    simpa only [a, b, mulVec, dotProduct, Complex.im_sum,
      Pi.smul_apply, smul_eq_mul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Pi.add_apply, add_comm] using hh
  have hs : X.transpose = X := by simpa using hX.isHermitian.eq
  have hqa := lyapunov_quadratic_identity hs he a
  have hqb := lyapunov_quadratic_identity hs he b
  rw [ha] at hqa
  rw [hb] at hqb
  simp only [sub_dotProduct, add_dotProduct, smul_dotProduct, smul_eq_mul] at hqa hqb
  have hab : a ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ (X *ᵥ a) := by
    simpa only [hs] using Matrix.dotProduct_transpose_mulVec X a b
  have hxa : 0 ≤ a ⬝ᵥ (X *ᵥ a) := by simpa only [star_trivial] using hX.dotProduct_mulVec_nonneg a
  have hxb : 0 ≤ b ⬝ᵥ (X *ᵥ b) := by simpa only [star_trivial] using hX.dotProduct_mulVec_nonneg b
  have hwa : 0 ≤ a ⬝ᵥ (W *ᵥ a) := by simpa only [star_trivial] using hW.posSemidef.dotProduct_mulVec_nonneg a
  have hwb : 0 ≤ b ⬝ᵥ (W *ᵥ b) := by simpa only [star_trivial] using hW.posSemidef.dotProduct_mulVec_nonneg b
  have hpos : 0 < a ⬝ᵥ (W *ᵥ a) + b ⬝ᵥ (W *ᵥ b) := by
    by_cases ha0 : a = 0
    · have hb0 : b ≠ 0 := by
        intro hb0
        apply hv0
        ext i
        apply Complex.ext
        · exact congrFun ha0 i
        · exact congrFun hb0 i
      have hp : 0 < b ⬝ᵥ (W *ᵥ b) := by simpa only [star_trivial] using hW.dotProduct_mulVec_pos hb0
      linarith
    · have hp : 0 < a ⬝ᵥ (W *ᵥ a) := by simpa only [star_trivial] using hW.dotProduct_mulVec_pos ha0
      linarith
  by_contra hz0
  have hz0' : 0 ≤ z.re := le_of_not_gt hz0
  have hprod := mul_nonneg hz0' (add_nonneg hxa hxb)
  rw [hab] at hqb
  nlinarith

end LQRProof


noncomputable section
namespace LQRProof
open Matrix FatkhullinPolyak.Discrete Set Filter Topology
open scoped Matrix.Norms.Frobenius

lemma lyapSol_order {n : ℕ} {M W V : Mat n} (hM : IsHurwitz M)
    (hWV : (V-W).PosSemidef) : (lyapSol M V - lyapSol M W).PosSemidef := by
  have heq : lyapSol M V - lyapSol M W = lyapSol M (V-W) := by
    apply lyapSol_unique hM
    have hV := lyapSol_equation hM V
    have hW := lyapSol_equation hM W
    simp only [mul_sub, sub_mul]
    calc
      _ = (M.transpose * lyapSol M V + lyapSol M V * M + V) -
          (M.transpose * lyapSol M W + lyapSol M W * M + W) := by abel
      _ = 0 := by rw [hV,hW,sub_self]
  rw [heq]
  exact lyapSol_posSemidef hM hWV

lemma isOpen_hurwitz (n : ℕ) : IsOpen {M : Mat n | IsHurwitz M} := by
  apply isOpen_iff_mem_nhds.mpr
  intro M hM
  let X := lyapSol M (1 : Mat n)
  have hX : X.PosDef := lyapSol_posDef hM Matrix.PosDef.one
  let F : Mat n → Mat n := fun N => -(N.transpose * X + X * N)
  have hc : Continuous F := by unfold F; fun_prop
  have hs : ∀ N, (F N).IsHermitian := by
    intro N
    have hx : X.transpose = X := by simpa using hX.isHermitian.eq
    change (-(N.transpose * X + X * N)).IsHermitian
    rw [Matrix.IsHermitian]
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, transpose_neg,
      transpose_add, transpose_mul, transpose_transpose, hx, add_comm]
  have hm : F M = 1 := by
    have he := lyapSol_equation hM (1 : Mat n)
    change M.transpose * X + X * M + 1 = 0 at he
    exact neg_eq_iff_add_eq_zero.mpr he
  have hp : (F M).PosDef := by rw [hm]; exact Matrix.PosDef.one
  filter_upwards [eventually_posDef_of_continuousAt hc.continuousAt hs hp] with N hN
  exact hurwitz_of_lyapunov hX.posSemidef hN (by dsimp only [F]; abel)

end LQRProof


noncomputable section
namespace LQRProof
open Matrix FatkhullinPolyak.Discrete Filter Topology
open scoped Matrix.Norms.Frobenius

local instance (n : ℕ) : TopologicalSpace (Mat n) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)).toUniformSpace.toTopologicalSpace

lemma lyapSol_hasDerivAt_equation {n : ℕ} {M W : ℝ → Mat n}
    {dM dW : Mat n} {t : ℝ} (hM : IsHurwitz (M t))
    (hMd : HasDerivAt M dM t) (hWd : HasDerivAt W dW t) :
    ∃ dX : Mat n, HasDerivAt (fun s => lyapSol (M s) (W s)) dX t ∧
      (M t).transpose*dX+dX*M t+dM.transpose*lyapSol (M t) (W t)+
        lyapSol (M t) (W t)*dM+dW=0 := by
  let X : ℝ → Mat n := fun s => lyapSol (M s) (W s)
  have houter : DifferentiableAt ℝ
      (fun p : Mat n × Mat n => lyapSol p.1 p.2) (M t, W t) :=
    (lyapSol_contDiffAt hM).differentiableAt (by simp)
  have hx : DifferentiableAt ℝ X t := by
    simpa only [X, Function.comp_def] using
      houter.comp t (hMd.differentiableAt.prodMk hWd.differentiableAt)
  let dX := deriv X t
  have hdX : HasDerivAt X dX t := hx.hasDerivAt
  refine ⟨dX, hdX, ?_⟩
  have hd := ((hasDerivAt_matrix_mul (hasDerivAt_transpose hMd) hdX).add
    (hasDerivAt_matrix_mul hdX hMd)).add hWd
  have hev : (fun s => (M s).transpose * X s + X s * M s + W s) =ᶠ[𝓝 t]
      (fun _ => (0 : Mat n)) := by
    have hs := hMd.continuousAt.eventually ((isOpen_hurwitz n).mem_nhds hM)
    filter_upwards [hs] with s hs
    exact lyapSol_equation hs (W s)
  have hz := (hd.congr_of_eventuallyEq hev.symm).unique (hasDerivAt_const t (0 : Mat n))
  change dM.transpose * X t + (M t).transpose * dX +
    (dX * M t + X t * dM) + dW = 0 at hz
  dsimp only [X] at hz
  calc
    _ = dM.transpose * lyapSol (M t) (W t) + (M t).transpose * dX +
      (dX * M t + lyapSol (M t) (W t) * dM) + dW := by abel
    _ = 0 := hz

end LQRProof


noncomputable section
namespace LQRProof
open FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius

local instance (p q : ℕ) : TopologicalSpace (Matrix (Fin p) (Fin q) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin p) (n := Fin q) (α := ℝ)).toUniformSpace.toTopologicalSpace

theorem state_line_derivatives {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (K H : Matrix (Fin m) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => A-B*(K+t•H)) (-(B*H)) 0 ∧
    HasDerivAt (fun t : ℝ => (K+t•H).transpose*R*(K+t•H)+Q)
      (H.transpose*R*K+K.transpose*R*H) 0 := by
  let J : ℝ → Matrix (Fin m) (Fin n) ℝ := fun t => K+t•H
  have hJ : HasDerivAt J H (0 : ℝ) := by
    have h := (hasDerivAt_const (0 : ℝ) K).add
      ((hasDerivAt_id (0 : ℝ)).smul_const H)
    simp only [one_smul, zero_add, id_eq] at h
    convert h using 1 <;> rfl
  have hJ0 : J 0 = K := by simp [J]
  constructor
  · have h := (hasDerivAt_const (0 : ℝ) A).sub
      (hasDerivAt_matrix_mul (hasDerivAt_const (0 : ℝ) B) hJ)
    simp only [Matrix.zero_mul, zero_add, zero_sub] at h
    convert h using 1 <;> rfl
  · have h := (hasDerivAt_matrix_mul
      (hasDerivAt_matrix_mul (hasDerivAt_transpose hJ)
        (hasDerivAt_const (0 : ℝ) R)) hJ).add_const Q
    simp only [hJ0, Matrix.mul_zero, add_zero] at h
    convert h using 1

theorem state_X_line_derivative {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (K H : Matrix (Fin m) (Fin n) ℝ) (hK : K ∈ stabSet A B 1) :
    ∃ D, HasDerivAt (fun t : ℝ => lyapX A B 1 Q R (K+t•H)) D 0 ∧
      (A-B*K).transpose*D+D*(A-B*K)+
      (-(B*H)).transpose*lyapX A B 1 Q R K+
      lyapX A B 1 Q R K*(-(B*H))+(H.transpose*R*K+K.transpose*R*H)=0 := by
  obtain ⟨hM,hW⟩ := state_line_derivatives A B Q R K H
  have hm : IsHurwitz (A-B*(K+(0:ℝ)•H)) := by
    simpa only [zero_smul,add_zero,stabSet,Set.mem_ofPred_eq,Matrix.mul_one] using hK
  obtain ⟨D,hD,hEq⟩ := lyapSol_hasDerivAt_equation
    (M := fun t : ℝ => A-B*(K+t•H))
    (W := fun t : ℝ => (K+t•H).transpose*R*(K+t•H)+Q)
    (dM := -(B*H)) (dW := H.transpose*R*K+K.transpose*R*H)
    (t := (0 : ℝ)) hm hM hW
  refine ⟨D, ?_, ?_⟩
  · simpa only [lyapX,Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one] using hD
  · simpa only [zero_smul,add_zero,lyapX,Matrix.transpose_one,
      Matrix.one_mul,Matrix.mul_one] using hEq

theorem gradient_equation_normalize {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (K H : Matrix (Fin m) (Fin n) ℝ)
    (X D : Matrix (Fin n) (Fin n) ℝ) (hX : X.transpose=X) (hR : R.transpose=R)
    (he : (A-B*K).transpose*D+D*(A-B*K)+(-(B*H)).transpose*X+
      X*(-(B*H))+(H.transpose*R*K+K.transpose*R*H)=0) :
    (A-B*K).transpose*D+D*(A-B*K)+
      (H.transpose*(R*K-B.transpose*X)+(R*K-B.transpose*X).transpose*H)=0 := by
  simp only [Matrix.transpose_sub,Matrix.transpose_mul,Matrix.transpose_transpose,
    hX,hR,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
  simp only [Matrix.transpose_neg,Matrix.transpose_sub,Matrix.transpose_mul,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.neg_mul,Matrix.mul_neg,Matrix.mul_assoc] at he
  convert he using 1
  abel

theorem state_gradient_trace {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {Q S : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef) (hR : R.PosDef) (hS : S.PosDef)
    (K H : Matrix (Fin m) (Fin n) ℝ) (hK : K ∈ stabSet A B 1)
    (D : Matrix (Fin n) (Fin n) ℝ)
    (he : (A-B*K).transpose*D+D*(A-B*K)+(-(B*H)).transpose*lyapX A B 1 Q R K+
      lyapX A B 1 Q R K*(-(B*H))+(H.transpose*R*K+K.transpose*R*H)=0) :
    Matrix.trace (D*S) = frobInner (lqrGrad A B 1 Q R S K) H := by
  let X := lyapX A B 1 Q R K
  let Y := lyapY A B 1 S K
  let E := R*K-B.transpose*X
  have hXsym : X.transpose = X := by simpa using (state_X_posDef A B hQ hR hK).isHermitian.eq
  have hYsym : Y.transpose = Y := by simpa using (state_Y_posDef A B hS hK).isHermitian.eq
  have hRsym : R.transpose = R := by simpa using hR.isHermitian.eq
  have hXeq := gradient_equation_normalize A B R K H X D hXsym hRsym he
  have hm : IsHurwitz (A-B*K) := by
    simpa only [stabSet,Set.mem_ofPred_eq,Matrix.mul_one] using hK
  have hYeq : (A-B*K)*Y+Y*(A-B*K).transpose+S=0 := by
    have hh := lyapSol_equation (hurwitz_transpose hm) S
    simpa only [Y,lyapY,Matrix.mul_one,Matrix.transpose_transpose] using hh
  have ht := trace_lyapunov_duality (A-B*K) D Y (H.transpose*E+E.transpose*H) S hXeq hYeq
  rw [trace_gradient_pair E Y H hYsym] at ht
  simpa only [lqrGrad,Matrix.mul_one,Matrix.transpose_one,X,Y,E] using ht

theorem state_cost_line_derivative {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {Q S : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef) (hR : R.PosDef) (hS : S.PosDef)
    (K H : Matrix (Fin m) (Fin n) ℝ) (hK : K ∈ stabSet A B 1) :
    HasDerivAt (fun t : ℝ => lqrCost A B 1 Q R S (K+t•H))
      (frobInner (lqrGrad A B 1 Q R S K) H) 0 := by
  obtain ⟨D,hD,hEq⟩ := state_X_line_derivative A B Q R K H hK
  have hv := state_gradient_trace A B hQ hR hS K H hK D hEq
  have hc := (traceCLM n).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_matrix_mul hD (hasDerivAt_const (0 : ℝ) S))
  simpa only [Function.comp_def,traceCLM,LinearMap.coe_toContinuousLinearMap',
    Matrix.traceLinearMap_apply,Matrix.mul_zero,add_zero,hv,lqrCost] using hc

end LQRProof


noncomputable section
namespace LQRProof
open FatkhullinPolyak.Discrete Set Filter Topology
open scoped Matrix.Norms.Frobenius

local instance (p q : ℕ) : TopologicalSpace (Matrix (Fin p) (Fin q) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin p) (n := Fin q) (α := ℝ)).toUniformSpace.toTopologicalSpace

theorem state_cost_line_derivative_at {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {Q S : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef) (hR : R.PosDef) (hS : S.PosDef)
    (K H : Matrix (Fin m) (Fin n) ℝ) (t : ℝ) (hK : K+t•H ∈ stabSet A B 1) :
    HasDerivAt (fun s : ℝ => lqrCost A B 1 Q R S (K+s•H))
      (frobInner (lqrGrad A B 1 Q R S (K+t•H)) H) t := by
  have h := state_cost_line_derivative A B hQ hR hS (K+t•H) H hK
  have hz : HasDerivAt (fun s : ℝ => lqrCost A B 1 Q R S (K+t•H+s•H))
      (frobInner (lqrGrad A B 1 Q R S (K+t•H)) H) (t-t) := by
    simpa only [sub_self] using h
  have hh := hz.comp (h := fun s : ℝ => s-t) t ((hasDerivAt_id t).sub_const t)
  simp only [mul_one] at hh
  have he : (fun s : ℝ => lqrCost A B 1 Q R S (K+s•H)) =
      ((fun s : ℝ => lqrCost A B 1 Q R S (K+t•H+s•H)) ∘ fun s : ℝ => s-t) := by
    funext s
    congr 1
    dsimp only [Function.comp_def]
    module
  rw [he]
  convert hh using 1

theorem state_stable_line_eventually {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (J H : Matrix (Fin m) (Fin n) ℝ) (hJ : J ∈ stabSet A B 1) :
    ∀ᶠ t : ℝ in 𝓝 0, J+t•H ∈ stabSet A B 1 := by
  have hm : IsHurwitz (A-B*J) := by
    simpa only [stabSet,Set.mem_ofPred_eq,Matrix.mul_one] using hJ
  have hc : Continuous (fun t : ℝ => A-B*(J+t•H)) := by fun_prop
  have hp : A-B*(J+(0:ℝ)•H) ∈ {M : Mat n | IsHurwitz M} := by
    simpa only [zero_smul,add_zero,Set.mem_ofPred_eq] using hm
  have he := hc.continuousAt.eventually ((isOpen_hurwitz n).mem_nhds hp)
  simpa only [stabSet,Set.mem_ofPred_eq,Matrix.mul_one] using he

theorem state_optimum_gradient_zero {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {Q S : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef) (hR : R.PosDef) (hS : S.PosDef)
    (J : Matrix (Fin m) (Fin n) ℝ) (hJ : J ∈ stabSet A B 1)
    (hmin : ∀ K : Matrix (Fin m) (Fin n) ℝ, K ∈ stabSet A B 1 → lqrCost A B 1 Q R S J ≤ lqrCost A B 1 Q R S K) :
    lqrGrad A B 1 Q R S J = 0 := by
  let G := lqrGrad A B 1 Q R S J
  have he := state_stable_line_eventually A B J G hJ
  have hl : IsLocalMin (fun t : ℝ => lqrCost A B 1 Q R S (J+t•G)) 0 := by
    filter_upwards [he] with t ht
    simpa only [zero_smul,add_zero] using hmin (J+t•G) ht
  have hz := hl.hasDerivAt_eq_zero (state_cost_line_derivative A B hQ hR hS J G hJ)
  change frobInner G G = 0 at hz
  rw [frobInner_self] at hz
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

theorem state_optimum_equation {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {Q S : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef) (hR : R.PosDef) (hS : S.PosDef)
    (J : Matrix (Fin m) (Fin n) ℝ) (hJ : J ∈ stabSet A B 1)
    (hmin : ∀ K : Matrix (Fin m) (Fin n) ℝ, K ∈ stabSet A B 1 → lqrCost A B 1 Q R S J ≤ lqrCost A B 1 Q R S K) :
    R*J = B.transpose*lyapX A B 1 Q R J := by
  have hz := state_optimum_gradient_zero A B hQ hR hS J hJ hmin
  simp only [lqrGrad,Matrix.mul_one,Matrix.transpose_one] at hz
  have hE : (R*J-B.transpose*lyapX A B 1 Q R J)*lyapY A B 1 S J = 0 := by
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  have hu : IsUnit (lyapY A B 1 S J).det :=
    isUnit_iff_ne_zero.mpr (state_Y_posDef A B hS hJ).det_pos.ne'
  have hh := congrArg (fun Z => Z*(lyapY A B 1 S J)⁻¹) hE
  rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hu,Matrix.mul_one,Matrix.zero_mul] at hh
  exact sub_eq_zero.mp hh

end LQRProof


namespace LQRProof
open FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius

theorem abs_trace_mul_le {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ)
    (B : Matrix (Fin q) (Fin p) ℝ) : |Matrix.trace (A*B)| ≤ ‖A‖*‖B‖ := by
  have h := frobInner_cauchy A.transpose B
  simpa only [frobInner_trace, Matrix.transpose_transpose, Matrix.frobenius_norm_transpose] using h

theorem lyapunov_gain_bound {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {Q S : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosSemidef) (hR : R.PosDef)
    (hS : S.PosDef) (c : ℝ) : ∃ b : ℝ, 0 < b ∧
      ∀ (K : Matrix (Fin m) (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ),
      X.PosSemidef → Matrix.trace (X*S) ≤ c →
      (A-B*K).transpose*X+X*(A-B*K)+K.transpose*R*K+Q=0 → ‖K‖ ≤ b := by
  obtain ⟨s, hs, hsb⟩ := trace_cost_controls_norm hS
  obtain ⟨r, hr, hrb⟩ := posDef_lower hR
  let C := max 0 (c/s)
  have hC : 0 ≤ C := le_max_left _ _
  let d := 2*C*(‖A‖+‖B‖)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  refine ⟨1+d/r, by positivity, ?_⟩
  intro K X hX hcost he
  have hXC : ‖X‖ ≤ C := by
    have hh := (hsb X hX).trans hcost
    exact ((le_div_iff₀ hs).2 (by nlinarith)).trans (le_max_right _ _)
  have htrace := congrArg Matrix.trace he
  simp only [Matrix.trace_add, Matrix.trace_zero] at htrace
  have hquad := trace_transpose_coercive hrb K
  have hleft := abs_trace_mul_le (A-B*K).transpose X
  have hright := abs_trace_mul_le X (A-B*K)
  rw [Matrix.frobenius_norm_transpose] at hleft
  have hm : ‖A-B*K‖ ≤ ‖A‖+‖B‖*‖K‖ :=
    (norm_sub_le _ _).trans (add_le_add_right (Matrix.frobenius_norm_mul B K) ‖A‖)
  have hb : r*‖K‖^2 ≤ 2*C*(‖A‖+‖B‖*‖K‖) := by
    have hl := neg_abs_le (Matrix.trace ((A-B*K).transpose*X))
    have hrr := neg_abs_le (Matrix.trace (X*(A-B*K)))
    have ht := hQ.trace_nonneg
    have hmul := mul_le_mul hXC hm (norm_nonneg _) hC
    nlinarith
  by_cases hk : ‖K‖ ≤ 1
  · exact hk.trans (by have := div_nonneg hd hr.le; linarith)
  · have hk1 : 1 < ‖K‖ := lt_of_not_ge hk
    have hterm : 2*C*(‖A‖+‖B‖*‖K‖) ≤ d*‖K‖ := by
      dsimp [d]
      nlinarith [mul_nonneg hC (norm_nonneg A)]
    have hkk : r*‖K‖ ≤ d := by nlinarith
    have hh : ‖K‖ ≤ d/r := (le_div_iff₀ hr).2 (by nlinarith)
    linarith

end LQRProof


namespace LQRProof
open Matrix
open scoped Matrix.Norms.Frobenius

theorem isClosed_psd (n : ℕ) :
    IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} := by
  have he : {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} =
      {A : Matrix (Fin n) (Fin n) ℝ | A.transpose = A} ∩ ⋂ v : Fin n → ℝ, {A : Matrix (Fin n) (Fin n) ℝ | 0 ≤ v ⬝ᵥ (A *ᵥ v)} := by
    ext A
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨by simpa using h.isHermitian.eq, fun v => by simpa using h.dotProduct_mulVec_nonneg v⟩
    · rintro ⟨hs, h⟩
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      · simpa [Matrix.IsHermitian] using hs
      · simpa using h
  rw [he]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_id
  · apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const
      (continuous_quadratic.comp (continuous_id.prodMk continuous_const))

end LQRProof


namespace LQRProof
open FatkhullinPolyak.Discrete Set
open scoped Matrix.Norms.Frobenius

theorem state_sublevel_compact {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {Q S : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef) (hR : R.PosDef)
    (hS : S.PosDef) (c : ℝ) :
    IsCompact {K : Matrix (Fin m) (Fin n) ℝ | K ∈ stabSet A B 1 ∧ lqrCost A B 1 Q R S K ≤ c} := by
  let E : Set (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
    {p | p.2.PosSemidef ∧
      (A-B*p.1).transpose*p.2+p.2*(A-B*p.1)+(p.1.transpose*R*p.1+Q)=0 ∧
      Matrix.trace (p.2*S) ≤ c}
  have hpoly : Continuous (fun p : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
      (A-B*p.1).transpose*p.2+p.2*(A-B*p.1)+(p.1.transpose*R*p.1+Q)) := by fun_prop
  have hcost : Continuous (fun p : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
      Matrix.trace (p.2*S)) := by fun_prop
  have hc : IsClosed E :=
    ((isClosed_psd n).preimage continuous_snd).inter
      ((isClosed_eq hpoly continuous_const).inter (isClosed_le hcost continuous_const))
  obtain ⟨b, _hb, hbound⟩ := lyapunov_gain_bound A B hQ.posSemidef hR hS c
  obtain ⟨s, hs, hsb⟩ := trace_cost_controls_norm hS
  have hbounded : Bornology.IsBounded E := by
    apply (isBounded_iff_forall_norm_le).2
    refine ⟨max b (c/s), ?_⟩
    intro p hp
    have hx : ‖p.2‖ ≤ c/s := (le_div_iff₀ hs).2 (by
      have hh := (hsb p.2 hp.1).trans hp.2.2
      nlinarith)
    have hk : ‖p.1‖ ≤ b := hbound p.1 p.2 hp.1 hp.2.2 (by
      simpa only [add_assoc] using hp.2.1)
    exact max_le_max hk hx
  have hcompact : IsCompact E := Metric.isCompact_of_isClosed_isBounded hc hbounded
  have heq : Prod.fst '' E = {K : Matrix (Fin m) (Fin n) ℝ | K ∈ stabSet A B 1 ∧ lqrCost A B 1 Q R S K ≤ c} := by
    ext K
    constructor
    · rintro ⟨⟨J,X⟩, hp, rfl⟩
      have hm := hurwitz_of_lyapunov hp.1 (state_forcing_posDef hQ hR J) hp.2.1
      have hx := lyapSol_unique hm hp.2.1
      have he : lyapX A B 1 Q R J = X := by
        simpa only [lyapX, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] using hx.symm
      refine ⟨?_, ?_⟩
      · simpa only [stabSet, Set.mem_ofPred_eq, Matrix.mul_one] using hm
      · simpa only [lqrCost, he] using hp.2.2
    · rintro ⟨hK, hcost⟩
      refine ⟨(K,lyapX A B 1 Q R K), ?_, rfl⟩
      refine ⟨(state_X_posDef A B hQ hR hK).posSemidef, ?_, hcost⟩
      have hm : IsHurwitz (A-B*K) := by
        simpa only [stabSet, Set.mem_ofPred_eq, Matrix.mul_one] using hK
      simpa only [lyapX, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] using
        lyapSol_equation hm (K.transpose*R*K+Q)
  rw [← heq]
  exact hcompact.image continuous_fst

end LQRProof


namespace LQRProof
open Set

theorem first_exit_segment {E : Type*} [TopologicalSpace E] {S : Set E}
    (hS : IsClosed S) {r : ℝ → E} (hr : Continuous r)
    {a b : ℝ} (ha : 0 < a) (hstart : ∀ t ∈ Icc 0 a, r t ∈ S)
    (hb : 0 ≤ b) (hexit : r b ∉ S) :
    ∃ T : ℝ, 0 < T ∧ (∀ t ∈ Icc 0 T, r t ∈ S) ∧
      ∀ δ > 0, ∃ t ∈ Ioc T (T+δ), r t ∉ S := by
  let D : Set ℝ := {t | 0 ≤ t ∧ ∀ u ∈ Icc 0 t, r u ∈ S}
  have haD : a ∈ D := ⟨ha.le, hstart⟩
  have hne : D.Nonempty := ⟨a, haD⟩
  have hbounded : BddAbove D := by
    refine ⟨b, ?_⟩
    intro t ht
    by_contra h
    exact hexit (ht.2 b ⟨hb, (lt_of_not_ge h).le⟩)
  let T := sSup D
  have haT : a ≤ T := le_csSup hbounded haD
  have hT : 0 < T := ha.trans_le haT
  have hbefore : Ico 0 T ⊆ r ⁻¹' S := by
    intro u hu
    obtain ⟨t, ht, hut⟩ := exists_lt_of_lt_csSup hne hu.2
    exact ht.2 u ⟨hu.1, hut.le⟩
  have hclosed : IsClosed (r ⁻¹' S) := hS.preimage hr
  have hall : Icc 0 T ⊆ r ⁻¹' S := by
    rw [← closure_Ico hT.ne]
    exact closure_minimal hbefore hclosed
  refine ⟨T, hT, hall, ?_⟩
  intro δ hδ
  by_contra h
  have hone : ∀ t ∈ Ioc T (T+δ), r t ∈ S := by
    push Not at h
    exact h
  have hD : T+δ ∈ D := by
    refine ⟨by linarith, ?_⟩
    intro u hu
    by_cases huT : u ≤ T
    · exact hall ⟨hu.1, huT⟩
    · exact hone u ⟨lt_of_not_ge huT, hu.2⟩
  have hh : T+δ ≤ T := le_csSup hbounded hD
  linarith

end LQRProof


namespace LQRProof
open Set Filter Topology

theorem initial_strict_drop {f : ℝ → ℝ} {d : ℝ}
    (hf : HasDerivAt f d 0) (hd : d < 0) :
    ∃ a > 0, ∀ t ∈ Ioc 0 a, f t < f 0 := by
  have he := hf.tendsto_slope_zero_right.eventually (gt_mem_nhds hd)
  obtain ⟨a, ha, h⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp he
  refine ⟨a, ha, ?_⟩
  intro t ht
  have hh := h ht
  simp only [Set.mem_ofPred_eq, zero_add, smul_eq_mul] at hh
  have hi : 0 < t⁻¹ := inv_pos.mpr ht.1
  have : f t - f 0 < 0 := by nlinarith
  linarith

theorem quadratic_line_bound {f d : ℝ → ℝ} {T a L : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt f (d t) t)
    (hb : ∀ t ∈ Ioo 0 T, d t ≤ -a + L*t*a) :
    f T ≤ f 0 - T*(1-L*T/2)*a := by
  let F : ℝ → ℝ := fun t => f t + a*t - L*a/2*t^2
  have hc : ContinuousOn F (Icc 0 T) :=
    (hf.add (continuous_const.mul continuous_id).continuousOn).sub
      (continuous_const.mul (continuous_id.pow 2)).continuousOn
  have hD : ∀ t ∈ Ioo 0 T, HasDerivAt F (d t+a-L*a*t) t := by
    intro t ht
    convert ((hd t ht).add ((hasDerivAt_id t).const_mul a)).sub
      (((hasDerivAt_id t).pow 2).const_mul (L*a/2)) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have hm : AntitoneOn F (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hc
      (f' := fun t => d t+a-L*a*t)
    · intro t ht
      exact (hD t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      have hh := hb t (by simpa only [interior_Icc] using ht)
      nlinarith
  have hh := hm (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩)
    (show T ∈ Icc 0 T from ⟨hT,le_rfl⟩) hT
  dsimp only [F] at hh
  nlinarith

end LQRProof


namespace LQRProof
open Set Filter Topology

theorem ray_descent {f d : ℝ → ℝ} {U : Set ℝ} {a L : ℝ}
    (hU : IsOpen U) (h0 : 0 ∈ U) (ha : 0 < a) (hL : 0 < L)
    (hd : ∀ t ∈ U, HasDerivAt f (d t) t) (hd0 : d 0 = -a)
    (hclosed : IsClosed {t | t ∈ U ∧ f t ≤ f 0})
    (hbounded : Bornology.IsBounded {t | t ∈ U ∧ f t ≤ f 0})
    (hslope : ∀ t, 0 ≤ t → t ∈ U → f t ≤ f 0 → d t ≤ -a+L*t*a) :
    ∀ t ∈ Icc 0 (2/L), t ∈ U ∧ f t ≤ f 0-t*(1-L*t/2)*a := by
  let S : Set ℝ := {t | t ∈ U ∧ f t ≤ f 0}
  obtain ⟨a₁, ha₁, hdrop⟩ := initial_strict_drop (hd 0 h0) (by rw [hd0]; linarith)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  let b := min a₁ (ε/2)
  have hb : 0 < b := lt_min ha₁ (half_pos hε)
  have hstart : ∀ t ∈ Icc 0 b, t ∈ S := by
    intro t ht
    have htε : t < ε := lt_of_le_of_lt (ht.2.trans (min_le_right _ _)) (by linarith)
    have hmem : t ∈ Metric.ball 0 ε := by
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg ht.1] using htε
    refine ⟨hεU hmem, ?_⟩
    rcases eq_or_lt_of_le ht.1 with h | h
    · simp [← h]
    · exact (hdrop t ⟨h, ht.2.trans (min_le_left _ _)⟩).le
  obtain ⟨c, hc⟩ := hbounded.exists_norm_le
  have hout : max 0 c + 1 ∉ S := by
    intro h
    have hh := hc _ h
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)] at hh
    have hm := le_max_right (0:ℝ) c
    linarith
  obtain ⟨T, hT, hseg, hnext⟩ := first_exit_segment hclosed continuous_id hb hstart
    (show 0 ≤ max 0 c+1 by positivity) hout
  have hTeq : f T = f 0 := by
    have hTS := hseg T ⟨hT.le, le_rfl⟩
    apply le_antisymm hTS.2
    by_contra hn
    have hlt : f T < f 0 := lt_of_not_ge hn
    have he : ∀ᶠ t in 𝓝 T, t ∈ S := by
      filter_upwards [hU.mem_nhds hTS.1, (hd T hTS.1).continuousAt.eventually (gt_mem_nhds hlt)] with t ht hf
      exact ⟨ht, hf.le⟩
    obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhds_iff.mp he
    obtain ⟨t, ht, hout⟩ := hnext (δ/2) (half_pos hδ)
    apply hout
    apply hδS
    rw [Metric.mem_ball, Real.dist_eq, id_eq, abs_of_pos (sub_pos.mpr ht.1)]
    linarith [ht.2]
  have hquad : ∀ t ∈ Icc 0 T, f t ≤ f 0-t*(1-L*t/2)*a := by
    intro t ht
    apply quadratic_line_bound ht.1
    · intro u hu
      exact (hd u (hseg u ⟨hu.1, hu.2.trans ht.2⟩).1).continuousAt.continuousWithinAt
    · intro u hu
      exact hd u (hseg u ⟨hu.1.le, hu.2.le.trans ht.2⟩).1
    · intro u hu
      have hS := hseg u ⟨hu.1.le, hu.2.le.trans ht.2⟩
      exact hslope u hu.1.le hS.1 hS.2
  have hLT : 2/L ≤ T := by
    have hh := hquad T ⟨hT.le,le_rfl⟩
    rw [hTeq] at hh
    apply (div_le_iff₀ hL).2
    have hprod : 0 < T*a := mul_pos hT ha
    nlinarith
  intro t ht
  have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hLT⟩
  exact ⟨(hseg t htT).1, hquad t htT⟩

end LQRProof


namespace LQRProof
open FatkhullinPolyak.Discrete Set
open scoped Matrix.Norms.Frobenius

theorem bounded_ray_preimage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : Bornology.IsBounded S) (K G : E) (hG : G ≠ 0) :
    Bornology.IsBounded {t : ℝ | K-t•G ∈ S} := by
  obtain ⟨b,hb⟩ := hS.exists_norm_le
  apply Metric.isBounded_iff.mpr
  refine ⟨2*((‖K‖+max 0 b)/‖G‖),?_⟩
  intro s hs t ht
  have hn := norm_pos_iff.mpr hG
  have bound : ∀ r : ℝ, K-r•G ∈ S → ‖r‖ ≤ (‖K‖+max 0 b)/‖G‖ := by
    intro r hr
    have he : r•G=K-(K-r•G) := by abel
    have hh := norm_sub_le K (K-r•G)
    rw [← he,norm_smul] at hh
    exact (le_div_iff₀ hn).mpr (hh.trans (add_le_add_right ((hb _ hr).trans (le_max_right _ _)) _))
  have hh := norm_sub_le s t
  rw [Real.dist_eq]
  change ‖s-t‖ ≤ _
  linarith [bound s hs,bound t ht]

theorem frobInner_neg_right {p q : ℕ} (A B : Matrix (Fin p) (Fin q) ℝ) :
    frobInner A (-B) = -frobInner A B := by
  simp only [frobInner,Matrix.neg_apply,mul_neg,Finset.sum_neg_distrib]

theorem frobInner_sub_left {p q : ℕ} (A B C : Matrix (Fin p) (Fin q) ℝ) :
    frobInner (A-B) C = frobInner A C-frobInner B C := by
  simp only [frobInner,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

theorem gradient_ray_slope {p q : ℕ} (g G : Matrix (Fin p) (Fin q) ℝ)
    {L t : ℝ} (h : ‖g-G‖ ≤ L*t*‖G‖) :
    frobInner g (-G) ≤ -‖G‖^2+L*t*‖G‖^2 := by
  have hc := (le_abs_self (frobInner (g-G) (-G))).trans (frobInner_cauchy (g-G) (-G))
  rw [norm_neg] at hc
  have hm := mul_le_mul_of_nonneg_right h (norm_nonneg G)
  rw [frobInner_sub_left,frobInner_neg_right G G,frobInner_self] at hc
  nlinarith

end LQRProof


noncomputable section
namespace LQRProof
open FatkhullinPolyak.Discrete Set
open scoped Matrix.Norms.Frobenius

local instance (p q : ℕ) : TopologicalSpace (Matrix (Fin p) (Fin q) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin p) (n := Fin q) (α := ℝ)).toUniformSpace.toTopologicalSpace

theorem state_one_step {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {Q S : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef) (hR : R.PosDef) (hS : S.PosDef)
    (K₀ K : Matrix (Fin m) (Fin n) ℝ) (hK : K ∈ sublevel A B 1 Q R S K₀)
    {L : ℝ} (hL : 0<L)
    (hlip : ∀ U ∈ sublevel A B 1 Q R S K₀, ∀ V ∈ sublevel A B 1 Q R S K₀,
      ‖lqrGrad A B 1 Q R S U-lqrGrad A B 1 Q R S V‖ ≤ L*‖U-V‖)
    {t : ℝ} (ht : t ∈ Icc 0 (2/L)) :
    K-t•lqrGrad A B 1 Q R S K ∈ sublevel A B 1 Q R S K₀ ∧
    lqrCost A B 1 Q R S (K-t•lqrGrad A B 1 Q R S K) ≤
      lqrCost A B 1 Q R S K-t*(1-L*t/2)*‖lqrGrad A B 1 Q R S K‖^2 := by
  let G := lqrGrad A B 1 Q R S K
  by_cases hG : G=0
  · simpa only [show lqrGrad A B 1 Q R S K=0 from hG,smul_zero,sub_zero,norm_zero,
      zero_pow (by decide : 2≠0),mul_zero] using And.intro hK (le_refl (lqrCost A B 1 Q R S K))
  let r : ℝ → Matrix (Fin m) (Fin n) ℝ := fun u => K-u•G
  let f : ℝ → ℝ := fun u => lqrCost A B 1 Q R S (r u)
  let d : ℝ → ℝ := fun u => frobInner (lqrGrad A B 1 Q R S (r u)) (-G)
  let U : Set ℝ := {u | r u ∈ stabSet A B 1}
  have hr : Continuous r := by fun_prop
  have hU : IsOpen U := by
    have hc : Continuous (fun u : ℝ => A-B*r u) := by fun_prop
    have hh := (isOpen_hurwitz n).preimage hc
    simpa only [U,stabSet,Set.mem_ofPred_eq,Matrix.mul_one,Set.preimage_ofPred_eq] using hh
  have h0 : (0:ℝ)∈U := by simpa [U,r] using hK.1
  have hd : ∀ u ∈ U, HasDerivAt f (d u) u := by
    intro u hu
    have h := state_cost_line_derivative_at A B hQ hR hS K (-G) u
      (by simpa only [U,r,Set.mem_ofPred_eq,smul_neg,sub_eq_add_neg] using hu)
    simpa only [f,d,r,smul_neg,sub_eq_add_neg] using h
  have hd0 : d 0 = -‖G‖^2 := by simp only [d,r,zero_smul,sub_zero,G,frobInner_neg_right,frobInner_self]
  let C := {J : Matrix (Fin m) (Fin n) ℝ | J ∈ stabSet A B 1 ∧ lqrCost A B 1 Q R S J ≤ lqrCost A B 1 Q R S K}
  have hC : IsCompact C := state_sublevel_compact A B hQ hR hS _
  have he : {u | u ∈ U ∧ f u ≤ f 0} = r ⁻¹' C := by
    ext u
    simp only [U,f,C,r,zero_smul,sub_zero,mem_ofPred_eq,mem_preimage]
  have hclosed : IsClosed {u | u ∈ U ∧ f u ≤ f 0} := by rw [he]; exact hC.isClosed.preimage hr
  have hbounded : Bornology.IsBounded {u | u ∈ U ∧ f u ≤ f 0} := by
    rw [he]
    exact bounded_ray_preimage hC.isBounded K G hG
  have hslope : ∀ u, 0≤u → u∈U → f u≤f 0 → d u≤ -‖G‖^2+L*u*‖G‖^2 := by
    intro u hu huU huf
    have huC : r u ∈ sublevel A B 1 Q R S K₀ :=
      ⟨huU,(show lqrCost A B 1 Q R S (r u)≤lqrCost A B 1 Q R S K by simpa [f,r] using huf).trans hK.2⟩
    have hh := hlip (r u) huC K hK
    have hn : ‖r u-K‖=u*‖G‖ := by
      have hx : r u-K=-(u•G) := by dsimp [r]; abel
      rw [hx,norm_neg,norm_smul,Real.norm_of_nonneg hu]
    rw [hn] at hh
    exact gradient_ray_slope (lqrGrad A B 1 Q R S (r u)) G (by simpa only [G,mul_assoc] using hh)
  have h := ray_descent hU h0 (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hG)) hL hd hd0 hclosed hbounded hslope t ht
  have hcoef : 0 ≤ t*(1-L*t/2)*‖G‖^2 := by
    have hh := (le_div_iff₀ hL).mp ht.2
    exact mul_nonneg (mul_nonneg ht.1 (by nlinarith)) (sq_nonneg _)
  refine ⟨⟨h.1,?_⟩,?_⟩
  · have hh := h.2
    change lqrCost A B 1 Q R S (r t) ≤ _
    have hzero : f 0=lqrCost A B 1 Q R S K := by simp [f,r]
    rw [hzero] at hh
    exact (hh.trans (sub_le_self _ hcoef)).trans hK.2
  · simpa only [f,r,G,zero_smul,sub_zero] using h.2

end LQRProof


namespace LQRProof

open Filter Topology

lemma energy_antitone {E r : ℕ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hstep : ∀ k, E (k + 1) + a * (r k) ^ 2 ≤ E k) : Antitone E := by
  apply antitone_nat_of_succ_le
  intro k
  have := hstep k
  have := mul_nonneg ha (sq_nonneg (r k))
  linarith

lemma energy_limit {E r : ℕ → ℝ} {a m : ℝ} (ha : 0 ≤ a)
    (hstep : ∀ k, E (k + 1) + a * (r k) ^ 2 ≤ E k)
    (hlower : ∀ k, m ≤ E k) : ∃ e : ℝ, Tendsto E atTop (nhds e) := by
  refine ⟨⨅ k, E k, tendsto_atTop_ciInf (energy_antitone ha hstep) ?_⟩
  exact ⟨m, by rintro _ ⟨k, rfl⟩; exact hlower k⟩

lemma energy_block {E r : ℕ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hstep : ∀ k, E (k + 1) + a * (r k) ^ 2 ≤ E k)
    (m n : ℕ) (hb : ∀ i, m ≤ i → i < m + n → b ^ 2 ≤ (r i) ^ 2) :
    a * (n : ℝ) * b ^ 2 ≤ E m - E (m + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (fun i hmi hin => hb i hmi (by omega))
    have hlast := hstep (m + n)
    have hmul := mul_le_mul_of_nonneg_left (hb (m + n) (by omega) (by omega)) ha
    push_cast
    rw [show m + (n + 1) = m + n + 1 by omega]
    nlinarith

lemma residual_tendsto_zero {E r : ℕ → ℝ} {a e : ℝ} (ha : 0 < a)
    (hr : ∀ k, 0 ≤ r k)
    (hstep : ∀ k, E (k + 1) + a * (r k) ^ 2 ≤ E k)
    (hE : Tendsto E atTop (nhds e)) : Tendsto r atTop (nhds 0) := by
  have hEs : Tendsto (fun k => E (k + 1)) atTop (nhds e) :=
    hE.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun k => (E k - E (k + 1)) / a) atTop (nhds 0) := by
    simpa using (hE.sub hEs).div_const a
  have hsquare : Tendsto (fun k => (r k) ^ 2) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiff
    · exact fun k => sq_nonneg _
    · intro k
      apply (le_div_iff₀ ha).2
      nlinarith [hstep k]
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  simpa only [Function.comp_def, Real.sqrt_sq (hr _), Real.sqrt_zero] using hh

lemma minimum_square_bound {E r : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hstep : ∀ j, E (j + 1) + a * (r j)^2 ≤ E j)
    (hE : ∀ j, 0 ≤ E j) (k : ℕ) (hk : 1 ≤ k) :
    (Finset.range (k+1)).inf' Finset.nonempty_range_add_one (fun j => (r j)^2)
      ≤ E 0 / (a * k) := by
  let b := (Finset.range (k+1)).inf' Finset.nonempty_range_add_one (fun j => (r j)^2)
  have hb : 0 ≤ b := Finset.le_inf' _ _ (fun j _ => sq_nonneg _)
  have htel (n : ℕ) (hn : n ≤ k) : a * n * b ≤ E 0 - E n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := ih (by omega)
      have hbj : b ≤ (r n)^2 := Finset.inf'_le _ (Finset.mem_range.mpr (by omega))
      have hm := mul_le_mul_of_nonneg_left hbj ha.le
      have hs := hstep n
      push_cast
      nlinarith
  have h := htel k le_rfl
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  apply (le_div_iff₀ (mul_pos ha hk0)).2
  dsimp only [b] at h
  nlinarith [hE k]

lemma geometric_gap {d : ℕ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hstep : ∀ j, d (j+1) ≤ a * d j) (k : ℕ) : d k ≤ a^k * d 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc d (k+1) ≤ a * d k := hstep k
      _ ≤ a * (a^k * d 0) := mul_le_mul_of_nonneg_left ih ha
      _ = a^(k+1) * d 0 := by rw [pow_succ]; ring

end LQRProof


namespace LQRProof

theorem geometric_distance_bound {d g r : ℕ → ℝ} {a C b : ℝ}
    (ha : 0 < a) (hC : 0 < C) (hb : 0 < b)
    (hd : ∀ j, 0 ≤ d j) (hr : ∀ j, 0 ≤ r j)
    (hstep : ∀ j, d (j+1)+a*(g j)^2 ≤ d j)
    (hPL : ∀ j, d j ≤ C*(g j)^2) (hgrowth : ∀ j, b*(r j)^2 ≤ d j) :
    ∃ c ≥ 0, ∃ q, 0 ≤ q ∧ q < 1 ∧ ∀ j, r j ≤ c*q^j := by
  let α := min (a/C) (1/2)
  have hα : 0 < α := lt_min (div_pos ha hC) (by norm_num)
  have hαhalf : α ≤ 1/2 := min_le_right _ _
  have hαC : α*C ≤ a := (le_div_iff₀ hC).mp (min_le_left _ _)
  have hs : ∀ j, d (j+1) ≤ (1-α)*d j := by
    intro j
    have h1 := mul_le_mul_of_nonneg_left (hPL j) hα.le
    have h2 := mul_le_mul_of_nonneg_right hαC (sq_nonneg (g j))
    have h3 := hstep j
    nlinarith
  have hbase : 0 ≤ 1-α := by linarith
  have hgeom := geometric_gap hbase hs
  let c := Real.sqrt (d 0/b)
  let q := Real.sqrt (1-α)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hc2 : c^2 = d 0/b := Real.sq_sqrt (div_nonneg (hd 0) hb.le)
  have hq2 : q^2 = 1-α := Real.sq_sqrt hbase
  refine ⟨c,hc,q,hq,?_,?_⟩
  · have : q^2 < 1 := by rw [hq2]; linarith
    nlinarith
  · intro j
    have hpow : (q^j)^2 = (1-α)^j := by rw [← pow_mul, Nat.mul_comm j 2, pow_mul, hq2]
    have hr2 : (r j)^2 ≤ d 0/b*(1-α)^j := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hb).2
      have hh := (hgrowth j).trans (hgeom j)
      convert hh using 1 <;> ring
    apply (sq_le_sq₀ (hr j) (mul_nonneg hc (pow_nonneg hq j))).mp
    rw [mul_pow, hc2, hpow]
    exact hr2

end LQRProof


namespace LQRProof
open FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius

theorem state_iteration_descent {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {Q S : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef) (hR : R.PosDef) (hS : S.PosDef)
    (K₀ : Matrix (Fin m) (Fin n) ℝ) (hK₀ : K₀ ∈ stabSet A B 1)
    {L : ℝ} (hL : 0<L)
    (hlip : ∀ U ∈ sublevel A B 1 Q R S K₀, ∀ V ∈ sublevel A B 1 Q R S K₀,
      ‖lqrGrad A B 1 Q R S U-lqrGrad A B 1 Q R S V‖ ≤ L*‖U-V‖)
    (γ : ℕ → ℝ) (hγ : ∀ j, 0<γ j ∧ γ j≤2/L) :
    (∀ j, gradIter A B 1 Q R S K₀ γ j ∈ sublevel A B 1 Q R S K₀) ∧
    ∀ j, lqrCost A B 1 Q R S (gradIter A B 1 Q R S K₀ γ (j+1)) ≤
      lqrCost A B 1 Q R S (gradIter A B 1 Q R S K₀ γ j)-
        γ j*(1-L*γ j/2)*‖lqrGrad A B 1 Q R S (gradIter A B 1 Q R S K₀ γ j)‖^2 := by
  have hmem : ∀ j, gradIter A B 1 Q R S K₀ γ j ∈ sublevel A B 1 Q R S K₀ := by
    intro j
    induction j with
    | zero => exact ⟨hK₀,le_rfl⟩
    | succ j ih =>
      exact (state_one_step A B hQ hR hS K₀ _ ih hL hlip ⟨(hγ j).1.le,(hγ j).2⟩).1
  exact ⟨hmem,fun j => (state_one_step A B hQ hR hS K₀ _ (hmem j) hL hlip
    ⟨(hγ j).1.le,(hγ j).2⟩).2⟩

theorem step_coefficient_lower {L e₁ e₂ t : ℝ} (hL : 0<L) (h₁ : 0<e₁) (h₂ : 0<e₂)
    (ht : e₁≤t ∧ t≤2/L-e₂) : e₁*e₂*L/2 ≤ t*(1-L*t/2) := by
  have ht0 := h₁.trans_le ht.1
  have hh : L*(t+e₂)≤2 := by
    have hx : t+e₂≤2/L := by linarith
    have hx' := (le_div_iff₀ hL).mp hx
    nlinarith
  have hfactor : e₂*L/2 ≤ 1-L*t/2 := by nlinarith
  have hpos : 0≤e₂*L/2 := by positivity
  have hm := mul_le_mul ht.1 hfactor hpos ht0.le
  nlinarith

end LQRProof


namespace LQRProof
open FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius

theorem performance_equation {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (Q X Z : Matrix (Fin n) (Fin n) ℝ)
    (K J : Matrix (Fin m) (Fin n) ℝ)
    (hR : R.transpose = R) (hZ : Z.transpose = Z)
    (hopt : R * J = B.transpose * Z)
    (hX : (A-B*K).transpose * X + X*(A-B*K) + K.transpose*R*K+Q = 0)
    (hJ : (A-B*J).transpose * Z + Z*(A-B*J) + J.transpose*R*J+Q = 0) :
    (A-B*K).transpose*(X-Z)+(X-Z)*(A-B*K)+(K-J).transpose*R*(K-J)=0 := by
  have hoptT : J.transpose * R = Z * B := by
    have hh := congrArg Matrix.transpose hopt
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hR, hZ] using hh
  have he :
      (A-B*K).transpose*(X-Z)+(X-Z)*(A-B*K)+(K-J).transpose*R*(K-J) =
      ((A-B*K).transpose * X + X*(A-B*K) + K.transpose*R*K+Q) -
      ((A-B*J).transpose * Z + Z*(A-B*J) + J.transpose*R*J+Q) +
      (K-J).transpose*(B.transpose*Z-R*J)+(Z*B-J.transpose*R)*(K-J) := by
    simp only [Matrix.transpose_sub, Matrix.transpose_mul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  rw [he, hX, hJ, hopt, hoptT]
  simp

theorem square_completion {n m : ℕ}
    (R V : Matrix (Fin m) (Fin m) ℝ) (D E : Matrix (Fin m) (Fin n) ℝ)
    (_hR : R.transpose = R) (hV : V.transpose = V)
    (hRV : R*V=1) (hVR : V*R=1) :
    E.transpose*V*E-(D.transpose*E+E.transpose*D-D.transpose*R*D) =
      (D-V*E).transpose*R*(D-V*E) := by
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, hV]
  have h1 : (D.transpose * R) * (V * E) = D.transpose * E := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc R V E, hRV, Matrix.one_mul]
  have h2 : (E.transpose * V) * R = E.transpose := by
    rw [Matrix.mul_assoc, hVR, Matrix.mul_one]
  simp only [Matrix.sub_mul, Matrix.mul_sub, h1, h2, Matrix.mul_assoc]
  abel

end LQRProof


namespace LQRProof
open FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius

theorem alternate_performance_equation {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (Q X Z : Matrix (Fin n) (Fin n) ℝ)
    (K J : Matrix (Fin m) (Fin n) ℝ)
    (hR : R.transpose = R) (hXsym : X.transpose = X)
    (hX : (A-B*K).transpose * X + X*(A-B*K) + K.transpose*R*K+Q = 0)
    (hJ : (A-B*J).transpose * Z + Z*(A-B*J) + J.transpose*R*J+Q = 0) :
    (A-B*J).transpose*(X-Z)+(X-Z)*(A-B*J)+
      ((K-J).transpose*(R*K-B.transpose*X)+(R*K-B.transpose*X).transpose*(K-J)-
        (K-J).transpose*R*(K-J))=0 := by
  have he :
      (A-B*J).transpose*(X-Z)+(X-Z)*(A-B*J)+
        ((K-J).transpose*(R*K-B.transpose*X)+(R*K-B.transpose*X).transpose*(K-J)-
          (K-J).transpose*R*(K-J)) =
      ((A-B*K).transpose*X+X*(A-B*K)+K.transpose*R*K+Q)-
        ((A-B*J).transpose*Z+Z*(A-B*J)+J.transpose*R*J+Q) := by
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      hR,hXsym,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  rw [he,hX,hJ,sub_self]

theorem square_completion_psd {n m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ}
    (hR : R.PosDef) (D E : Matrix (Fin m) (Fin n) ℝ) :
    (E.transpose*R⁻¹*E-(D.transpose*E+E.transpose*D-D.transpose*R*D)).PosSemidef := by
  have hr : R.transpose = R := by simpa using hR.isHermitian.eq
  have hv : (R⁻¹).transpose = R⁻¹ := by simpa using hR.isHermitian.inv.eq
  have hu : IsUnit R.det := isUnit_iff_ne_zero.mpr hR.det_pos.ne'
  rw [square_completion R R⁻¹ D E hr hv (Matrix.mul_nonsing_inv _ hu) (Matrix.nonsing_inv_mul _ hu)]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hR.posSemidef.conjTranspose_mul_mul_same (D-R⁻¹*E)

theorem forcing_trace_upper {n m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ}
    (hR : R.PosDef) {Y : Matrix (Fin n) (Fin n) ℝ} (hY : Y.PosSemidef)
    (D E : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace ((D.transpose*E+E.transpose*D-D.transpose*R*D)*Y) ≤
      Matrix.trace (E.transpose*R⁻¹*E*Y) := by
  have h := trace_mul_nonneg (square_completion_psd hR D E) hY
  rw [Matrix.sub_mul,Matrix.trace_sub] at h
  linarith

end LQRProof


namespace LQRProof
open FatkhullinPolyak.Discrete
open scoped Matrix.Norms.Frobenius

theorem state_X_equation {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) {K : Matrix (Fin m) (Fin n) ℝ}
    (hK : K ∈ stabSet A B 1) :
    (A-B*K).transpose*lyapX A B 1 Q R K+lyapX A B 1 Q R K*(A-B*K)+K.transpose*R*K+Q=0 := by
  have hm : IsHurwitz (A-B*K) := by simpa only [stabSet, Set.mem_ofPred_eq, Matrix.mul_one] using hK
  have h := lyapSol_equation hm (K.transpose*R*K+Q)
  simpa only [lyapX, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, add_assoc] using h

theorem state_Y_equation {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    {K : Matrix (Fin m) (Fin n) ℝ} (hK : K ∈ stabSet A B 1) :
    (A-B*K)*lyapY A B 1 S K+lyapY A B 1 S K*(A-B*K).transpose+S=0 := by
  have hm : IsHurwitz (A-B*K) := by simpa only [stabSet, Set.mem_ofPred_eq, Matrix.mul_one] using hK
  simpa only [lyapY, Matrix.mul_one, Matrix.transpose_transpose] using
    lyapSol_equation (hurwitz_transpose hm) S

theorem state_gap_identity {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {Q S : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef) (hR : R.PosDef)
    {K J : Matrix (Fin m) (Fin n) ℝ} (hK : K ∈ stabSet A B 1) (hJ : J ∈ stabSet A B 1)
    (hopt : R*J=B.transpose*lyapX A B 1 Q R J) :
    lqrCost A B 1 Q R S K-lqrCost A B 1 Q R S J =
      Matrix.trace ((K-J).transpose*R*(K-J)*lyapY A B 1 S K) := by
  have hr : R.transpose=R := by simpa using hR.isHermitian.eq
  have hz : (lyapX A B 1 Q R J).transpose=lyapX A B 1 Q R J := by
    simpa using (state_X_posDef A B hQ hR hJ).isHermitian.eq
  have he := performance_equation A B R Q (lyapX A B 1 Q R K) (lyapX A B 1 Q R J)
    K J hr hz hopt (state_X_equation A B Q R hK) (state_X_equation A B Q R hJ)
  have ht := trace_lyapunov_duality (A-B*K) (lyapX A B 1 Q R K-lyapX A B 1 Q R J)
    (lyapY A B 1 S K) ((K-J).transpose*R*(K-J)) S he (state_Y_equation A B S hK)
  simpa only [Matrix.sub_mul,Matrix.trace_sub,lqrCost] using ht

theorem state_gap_upper {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {Q S : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef) (hR : R.PosDef) (hS : S.PosDef)
    {K J : Matrix (Fin m) (Fin n) ℝ} (hK : K ∈ stabSet A B 1) (hJ : J ∈ stabSet A B 1) :
    lqrCost A B 1 Q R S K-lqrCost A B 1 Q R S J ≤
      Matrix.trace ((R*K-B.transpose*lyapX A B 1 Q R K).transpose*R⁻¹*
        (R*K-B.transpose*lyapX A B 1 Q R K)*lyapY A B 1 S J) := by
  have hr : R.transpose=R := by simpa using hR.isHermitian.eq
  have hx : (lyapX A B 1 Q R K).transpose=lyapX A B 1 Q R K := by
    simpa using (state_X_posDef A B hQ hR hK).isHermitian.eq
  let E := R*K-B.transpose*lyapX A B 1 Q R K
  let D := K-J
  have he := alternate_performance_equation A B R Q (lyapX A B 1 Q R K)
    (lyapX A B 1 Q R J) K J hr hx (state_X_equation A B Q R hK) (state_X_equation A B Q R hJ)
  have ht := trace_lyapunov_duality (A-B*J) (lyapX A B 1 Q R K-lyapX A B 1 Q R J)
    (lyapY A B 1 S J) (D.transpose*E+E.transpose*D-D.transpose*R*D) S he
    (state_Y_equation A B S hJ)
  have hu := forcing_trace_upper hR (state_Y_posDef A B hS hJ).posSemidef D E
  rw [← ht] at hu
  simpa only [Matrix.sub_mul,Matrix.trace_sub,lqrCost,E] using hu

end LQRProof


noncomputable section
namespace LQRProof
open FatkhullinPolyak.Discrete Set
open scoped Matrix.Norms.Frobenius

local instance (p q : ℕ) : TopologicalSpace (Matrix (Fin p) (Fin q) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin p) (n := Fin q) (α := ℝ)).toUniformSpace.toTopologicalSpace

theorem trace_quadratic_pos {n m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ}
    {Y : Matrix (Fin n) (Fin n) ℝ} (hR : R.PosDef) (hY : Y.PosDef)
    {D : Matrix (Fin m) (Fin n) ℝ} (hD : D ≠ 0) :
    0 < Matrix.trace (D.transpose*R*D*Y) := by
  have hA : (D.transpose*R*D).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hR.posSemidef.conjTranspose_mul_mul_same D
  obtain ⟨r,hr,hRb⟩ := posDef_lower hR
  obtain ⟨y,hy,hYb⟩ := posDef_lower hY
  have ht := trace_transpose_coercive hRb D
  have hp : 0 < Matrix.trace (D.transpose*R*D) :=
    (mul_pos hr (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hD))).trans_le ht
  exact (mul_pos hy hp).trans_le (trace_mul_lower hA hYb)

theorem trace_quadratic_smul {n m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (Y : Matrix (Fin n) (Fin n) ℝ) (D : Matrix (Fin m) (Fin n) ℝ) (a : ℝ) :
    Matrix.trace ((a•D).transpose*R*(a•D)*Y) =
      a^2 * Matrix.trace (D.transpose*R*D*Y) := by
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]
  ring

theorem compact_positive_lower {E : Type*} [TopologicalSpace E] {S : Set E}
    (hS : IsCompact S) {f : E → ℝ} (hf : ContinuousOn f S)
    (hp : ∀ x ∈ S, 0 < f x) : ∃ b > 0, ∀ x ∈ S, b ≤ f x := by
  rcases S.eq_empty_or_nonempty with h | h
  · subst S
    exact ⟨1,zero_lt_one,by simp⟩
  · obtain ⟨x,hx,hmin⟩ := hS.exists_isMinOn h hf
    exact ⟨f x,hp x hx,hmin⟩

theorem continuous_trace_quadratic {n m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (fun p : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
      Matrix.trace (p.1.transpose*R*p.1*p.2)) := by fun_prop

theorem continuousOn_quadratic_family {n m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    {S : Set (Matrix (Fin m) (Fin n) ℝ)}
    {Y : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hY : ContinuousOn Y S) :
    ContinuousOn (fun p : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ =>
      Matrix.trace (p.2.transpose*R*p.2*Y p.1))
      (S ×ˢ Metric.sphere (0 : Matrix (Fin m) (Fin n) ℝ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hy : Continuous (fun p : ↥(S ×ˢ Metric.sphere (0 : Matrix (Fin m) (Fin n) ℝ) 1) => Y p.val.1) := by
    exact (continuousOn_iff_continuous_domRestrict.mp hY).comp
      (show Continuous (fun p : ↥(S ×ˢ Metric.sphere (0 : Matrix (Fin m) (Fin n) ℝ) 1) =>
        (⟨p.val.1,p.property.1⟩ : S)) from (continuous_fst.comp continuous_subtype_val).subtype_mk _)
  exact (((continuous_snd.comp continuous_subtype_val).matrix_transpose.matrix_mul
    continuous_const).matrix_mul (continuous_snd.comp continuous_subtype_val)).matrix_mul hy |>.matrix_trace

theorem compact_quadratic_unit_lower {n m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ}
    (hR : R.PosDef) {S : Set (Matrix (Fin m) (Fin n) ℝ)} (hS : IsCompact S)
    {Y : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hY : ContinuousOn Y S) (hp : ∀ K ∈ S, (Y K).PosDef) :
    ∃ b > 0, ∀ K ∈ S, ∀ D : Matrix (Fin m) (Fin n) ℝ,
      ‖D‖ = 1 → b ≤ Matrix.trace (D.transpose*R*D*Y K) := by
  let T := S ×ˢ Metric.sphere (0 : Matrix (Fin m) (Fin n) ℝ) 1
  let f : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ → ℝ :=
    fun p => Matrix.trace (p.2.transpose*R*p.2*Y p.1)
  have hT : IsCompact T := hS.prod (isCompact_sphere _ _)
  have hf : ContinuousOn f T := continuousOn_quadratic_family R hY
  have hfpos : ∀ p ∈ T, 0 < f p := by
    intro p hp'
    apply trace_quadratic_pos hR (hp p.1 hp'.1)
    intro hz
    have hh := hp'.2
    simp [hz] at hh
  obtain ⟨b,hb,hbound⟩ := compact_positive_lower hT hf hfpos
  refine ⟨b,hb,?_⟩
  intro K hK D hD
  exact hbound (K,D) ⟨hK,by simpa only [Metric.mem_sphere,dist_zero_right] using hD⟩

theorem quadratic_lower_of_unit {n m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (Y : Matrix (Fin n) (Fin n) ℝ) (b : ℝ)
    (hbound : ∀ D : Matrix (Fin m) (Fin n) ℝ, ‖D‖=1 →
      b ≤ Matrix.trace (D.transpose*R*D*Y)) (D : Matrix (Fin m) (Fin n) ℝ) :
    b*‖D‖^2 ≤ Matrix.trace (D.transpose*R*D*Y) := by
  by_cases hD : D = 0
  · simp [hD]
  · have hn : 0 < ‖D‖ := norm_pos_iff.mpr hD
    let V := ‖D‖⁻¹ • D
    have hV : ‖V‖ = 1 := by
      simp only [V,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),inv_mul_cancel₀ hn.ne']
    have hh := hbound V hV
    have he : ‖D‖ • V = D := by simp [V,smul_smul,hn.ne']
    have hx := trace_quadratic_smul R Y V ‖D‖
    rw [he] at hx
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖D‖)
    rw [← hx] at hm
    nlinarith

theorem compact_quadratic_lower {n m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ}
    (hR : R.PosDef) {S : Set (Matrix (Fin m) (Fin n) ℝ)} (hS : IsCompact S)
    {Y : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hY : ContinuousOn Y S) (hp : ∀ K ∈ S, (Y K).PosDef) :
    ∃ b > 0, ∀ K ∈ S, ∀ D : Matrix (Fin m) (Fin n) ℝ,
      b*‖D‖^2 ≤ Matrix.trace (D.transpose*R*D*Y K) := by
  obtain ⟨b,hb,hh⟩ := compact_quadratic_unit_lower hR hS hY hp
  exact ⟨b,hb,fun K hK D => quadratic_lower_of_unit R (Y K) b (hh K hK) D⟩

end LQRProof


noncomputable section
namespace LQRProof
open scoped Matrix.Norms.Frobenius

theorem trace_quadratic_upper {n m : ℕ} (V : Matrix (Fin m) (Fin m) ℝ)
    (Y : Matrix (Fin n) (Fin n) ℝ) (E : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace (E.transpose*V*E*Y) ≤ ‖V‖*‖Y‖*‖E‖^2 := by
  have h1 := abs_trace_mul_le (E.transpose*V*E) Y
  have h2 := Matrix.frobenius_norm_mul (E.transpose*V) E
  have h3 := Matrix.frobenius_norm_mul E.transpose V
  rw [Matrix.frobenius_norm_transpose] at h3
  have hh := mul_le_mul_of_nonneg_right h3 (norm_nonneg E)
  have hx := mul_le_mul_of_nonneg_right (h2.trans hh) (norm_nonneg Y)
  have ht := le_abs_self (Matrix.trace (E.transpose*V*E*Y))
  nlinarith

theorem residual_norm_bound {n m : ℕ} (E : Matrix (Fin m) (Fin n) ℝ)
    {Y : Matrix (Fin n) (Fin n) ℝ} (hY : IsUnit Y) :
    ‖E‖ ≤ ‖(2:ℝ)•(E*Y)‖ * ‖Y⁻¹‖ := by
  have he : E*Y*Y⁻¹=E := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv Y ((Matrix.isUnit_iff_isUnit_det Y).mp hY), Matrix.mul_one]
  have h := Matrix.frobenius_norm_mul (E*Y) Y⁻¹
  rw [he] at h
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
  nlinarith [mul_nonneg (norm_nonneg (E*Y)) (norm_nonneg Y⁻¹)]

theorem compact_inverse_bound {E : Type*} [TopologicalSpace E] {S : Set E}
    (hS : IsCompact S) {n : ℕ} {Y : E → Matrix (Fin n) (Fin n) ℝ}
    (hc : ContinuousOn Y S) (hp : ∀ x ∈ S, (Y x).PosDef) :
    ∃ C > 0, ∀ x ∈ S, ‖(Y x)⁻¹‖ ≤ C := by
  have hi : ContinuousOn (fun x => (Y x)⁻¹) S := by
    intro x hx
    have hdet : (Y x).det ≠ 0 := (hp x hx).det_pos.ne'
    have hInv : ContinuousAt (fun r : ℝ => Ring.inverse r) (Y x).det := by
      simpa only [Ring.inverse_eq_inv] using continuousAt_inv₀ hdet
    exact (continuousAt_matrix_inv (Y x) hInv).comp_continuousWithinAt (hc x hx)
  obtain ⟨C,hC⟩ := (hS.image_of_continuousOn hi).isBounded.exists_norm_le
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  exact (hC _ ⟨x,hx,rfl⟩).trans (le_max_right _ _)

end LQRProof


noncomputable section
namespace LQRProof
open FatkhullinPolyak.Discrete Set
open scoped Matrix.Norms.Frobenius

local instance (p q : ℕ) : TopologicalSpace (Matrix (Fin p) (Fin q) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin p) (n := Fin q) (α := ℝ)).toUniformSpace.toTopologicalSpace

theorem state_Y_continuousOn {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    {T : Set (Matrix (Fin m) (Fin n) ℝ)} (hT : T ⊆ stabSet A B 1) :
    ContinuousOn (lyapY A B 1 S) T := by
  intro K hK
  exact (state_Y_contDiffAt A B S (hT hK)).continuousAt.continuousWithinAt

theorem state_compact_growth {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {Q S : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef) (hR : R.PosDef) (hS : S.PosDef)
    (K₀ J : Matrix (Fin m) (Fin n) ℝ) (hJ : J ∈ stabSet A B 1)
    (hopt : R*J=B.transpose*lyapX A B 1 Q R J) :
    ∃ b > 0, ∀ K ∈ sublevel A B 1 Q R S K₀,
      b*‖K-J‖^2 ≤ lqrCost A B 1 Q R S K-lqrCost A B 1 Q R S J := by
  have hc := state_sublevel_compact A B hQ hR hS (lqrCost A B 1 Q R S K₀)
  have hy := state_Y_continuousOn A B S (T := sublevel A B 1 Q R S K₀) (fun _ h => h.1)
  obtain ⟨b,hb,hh⟩ := compact_quadratic_lower hR hc hy
    (fun K hK => state_Y_posDef A B hS hK.1)
  refine ⟨b,hb,?_⟩
  intro K hK
  rw [state_gap_identity A B hQ hR hK.1 hJ hopt]
  exact hh K hK (K-J)

theorem state_compact_pl {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {Q S : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef) (hR : R.PosDef) (hS : S.PosDef)
    (K₀ J : Matrix (Fin m) (Fin n) ℝ) (hJ : J ∈ stabSet A B 1) :
    ∃ C > 0, ∀ K ∈ sublevel A B 1 Q R S K₀,
      lqrCost A B 1 Q R S K-lqrCost A B 1 Q R S J ≤ C*‖lqrGrad A B 1 Q R S K‖^2 := by
  have hc := state_sublevel_compact A B hQ hR hS (lqrCost A B 1 Q R S K₀)
  have hy := state_Y_continuousOn A B S (T := sublevel A B 1 Q R S K₀) (fun _ h => h.1)
  obtain ⟨c,hc0,hc⟩ := compact_inverse_bound hc hy (fun K hK => state_Y_posDef A B hS hK.1)
  let a := ‖R⁻¹‖*‖lyapY A B 1 S J‖
  have ha : 0 ≤ a := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨1+a*c^2,by positivity,?_⟩
  intro K hK
  let E := R*K-B.transpose*lyapX A B 1 Q R K
  have hY := state_Y_posDef A B hS hK.1
  have hu : IsUnit (lyapY A B 1 S K) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hY.det_pos.ne')
  have he := residual_norm_bound E hu
  have hg : ‖E‖ ≤ ‖lqrGrad A B 1 Q R S K‖*c := by
    have h := mul_le_mul_of_nonneg_left (hc K hK) (norm_nonneg ((2:ℝ)•(E*lyapY A B 1 S K)))
    simpa only [lqrGrad,Matrix.mul_one,Matrix.transpose_one,E] using he.trans h
  have hsq : ‖E‖^2 ≤ (‖lqrGrad A B 1 Q R S K‖*c)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) hc0.le)).mpr hg
  have hgap := (state_gap_upper A B hQ hR hS hK.1 hJ).trans
    (trace_quadratic_upper R⁻¹ (lyapY A B 1 S J) E)
  have hh := mul_le_mul_of_nonneg_left hsq ha
  dsimp only [a] at hh ⊢
  nlinarith [sq_nonneg ‖lqrGrad A B 1 Q R S K‖]

end LQRProof


namespace LQRProof
open FatkhullinPolyak.Discrete Filter Topology
open scoped Matrix.Norms.Frobenius

theorem state_strict_rates {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {Q S : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef) (hR : R.PosDef) (hS : S.PosDef)
    (K₀ J : Matrix (Fin m) (Fin n) ℝ) (hK₀ : K₀ ∈ stabSet A B 1) (hJ : J ∈ stabSet A B 1)
    (hmin : ∀ K : Matrix (Fin m) (Fin n) ℝ, K ∈ stabSet A B 1 → lqrCost A B 1 Q R S J ≤ lqrCost A B 1 Q R S K)
    {L : ℝ} (hL : 0<L)
    (hlip : ∀ U ∈ sublevel A B 1 Q R S K₀, ∀ V ∈ sublevel A B 1 Q R S K₀,
      ‖lqrGrad A B 1 Q R S U-lqrGrad A B 1 Q R S V‖ ≤ L*‖U-V‖)
    (γ : ℕ → ℝ) {e₁ e₂ : ℝ} (h₁ : 0<e₁) (h₂ : 0<e₂)
    (hγ : ∀ j, e₁≤γ j ∧ γ j≤2/L-e₂) :
    Tendsto (fun j => ‖lqrGrad A B 1 Q R S (gradIter A B 1 Q R S K₀ γ j)‖) atTop (𝓝 0) ∧
    (∀ k : ℕ, 1≤k → (Finset.range (k+1)).inf' Finset.nonempty_range_add_one
      (fun j => ‖lqrGrad A B 1 Q R S (gradIter A B 1 Q R S K₀ γ j)‖^2) ≤
      lqrCost A B 1 Q R S K₀/(e₁*e₂*L/2*k)) ∧
    ∃ c q : ℝ, 0≤c ∧ 0≤q ∧ q<1 ∧ ∀ j, ‖gradIter A B 1 Q R S K₀ γ j-J‖≤c*q^j := by
  have hγ' : ∀ j, 0<γ j ∧ γ j≤2/L := by
    intro j
    exact ⟨h₁.trans_le (hγ j).1,by linarith [(hγ j).2]⟩
  obtain ⟨hmem,hdec⟩ := state_iteration_descent A B hQ hR hS K₀ hK₀ hL hlip γ hγ'
  let K := gradIter A B 1 Q R S K₀ γ
  let E : ℕ → ℝ := fun j => lqrCost A B 1 Q R S (K j)
  let g : ℕ → ℝ := fun j => ‖lqrGrad A B 1 Q R S (K j)‖
  let a := e₁*e₂*L/2
  have ha : 0<a := by dsimp [a]; positivity
  have hg : ∀ j, 0≤g j := fun j => norm_nonneg _
  have hE : ∀ j, 0≤E j := fun j => state_cost_nonneg A B hQ hR hS (hmem j).1
  have hstep : ∀ j, E (j+1)+a*(g j)^2≤E j := by
    intro j
    have hc := step_coefficient_lower hL h₁ h₂ (hγ j)
    have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg (g j))
    have hd := hdec j
    change E (j+1)≤E j-γ j*(1-L*γ j/2)*(g j)^2 at hd
    dsimp only [a] at hh ⊢
    linarith
  obtain ⟨e,he⟩ := energy_limit ha.le hstep hE
  refine ⟨residual_tendsto_zero ha hg hstep he,?_,?_⟩
  · intro k hk
    exact minimum_square_bound ha hstep hE k hk
  · have hopt := state_optimum_equation A B hQ hR hS J hJ hmin
    obtain ⟨b,hb,hgrowth⟩ := state_compact_growth A B hQ hR hS K₀ J hJ hopt
    obtain ⟨C,hC,hPL⟩ := state_compact_pl A B hQ hR hS K₀ J hJ
    let d : ℕ → ℝ := fun j => E j-lqrCost A B 1 Q R S J
    have hd : ∀ j, 0≤d j := fun j => sub_nonneg.mpr (hmin _ (hmem j).1)
    have hds : ∀ j, d (j+1)+a*(g j)^2≤d j := by intro j; dsimp [d]; linarith [hstep j]
    obtain ⟨c,hc,q,hq0,hq1,hbound⟩ := geometric_distance_bound ha hC hb hd
      (fun j => norm_nonneg (K j-J)) hds (fun j => hPL _ (hmem j))
      (fun j => hgrowth _ (hmem j))
    exact ⟨c,q,hc,hq0,hq1,hbound⟩

end LQRProof


namespace LQRProof
open FatkhullinPolyak.Discrete Filter Topology
open scoped Matrix.Norms.Frobenius

theorem full_native_result {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (_hB : B ≠ 0)
    (K₀ : Matrix (Fin m) (Fin n) ℝ) (hK₀ : K₀ ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ))
    (Kstar : Matrix (Fin m) (Fin n) ℝ) (hKstar : Kstar ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ))
    (hopt : ∀ K ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ), lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig Kstar ≤ lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K)
    (L : ℝ) (hLpos : 0 < L)
    (hL : ∀ K ∈ sublevel A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀, ∀ K' ∈ sublevel A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀,
      frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K - lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K') ≤ L * frobNorm (K - K'))
    (γ : ℕ → ℝ) :
    ((∀ j, 0 < γ j ∧ γ j ≤ 2 / L) →
      (∀ j, gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j ∈ sublevel A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀) ∧
      ∀ j, lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ (j + 1)) ≤
        lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j)
          - γ j * (1 - L * γ j / 2) *
            frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j)) ^ 2) ∧
    (∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → (∀ j, ε₁ ≤ γ j ∧ γ j ≤ 2 / L - ε₂) →
      Tendsto (fun j => frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j)))
        atTop (𝓝 0) ∧
      (∀ k : ℕ, 1 ≤ k →
        (Finset.range (k + 1)).inf' ⟨0, by simp⟩
            (fun j => frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j)) ^ 2)
          ≤ lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ / (ε₁ * ε₂ * L / 2 * k)) ∧
      ∃ c q : ℝ, 0 ≤ c ∧ 0 ≤ q ∧ q < 1 ∧
        ∀ j, frobNorm (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j - Kstar) ≤ c * q ^ j)  := by
  have hlip : ∀ K ∈ sublevel A B 1 Q R Sig K₀, ∀ K' ∈ sublevel A B 1 Q R Sig K₀,
      ‖lqrGrad A B 1 Q R Sig K-lqrGrad A B 1 Q R Sig K'‖ ≤ L*‖K-K'‖ := by
    simpa only [frobNorm_eq_norm] using hL
  constructor
  · intro hγ
    simpa only [frobNorm_eq_norm] using
      state_iteration_descent A B hQ hR hSig K₀ hK₀ hLpos hlip γ hγ
  · intro ε₁ ε₂ h₁ h₂ hγ
    simpa only [frobNorm_eq_norm] using
      state_strict_rates A B hQ hR hSig K₀ Kstar hK₀ hKstar hopt hLpos hlip γ h₁ h₂ hγ

end LQRProof


open Filter Topology

namespace FatkhullinPolyak.Discrete

/-- Theorem 4.2 (pp. 10–11) for state feedback `C = I`, with `L` any Lipschitz constant of `∇f`
on `S₀` (the paper's `L`-smoothness, §3.6; the explicit (3.8) is false). For the gradient method
(4.4) from `K₀ ∈ S`, with `K⋆ ∈ S` a minimum point of `f` on `S`:
(i) if `0 < γⱼ ≤ 2/L` for all `j`, every iterate stays in `S₀` and (4.5) holds;
(ii) if `0 < ε₁ ≤ γⱼ ≤ 2/L − ε₂`, `ε₂ > 0`, then `∇f(Kⱼ) → 0`,
`min_{0≤j≤k} ‖∇f(Kⱼ)‖_F² ≤ f(K₀)/(c₁k)` for `k ≥ 1` with `c₁ = ε₁ε₂L/2`, and the iterates
converge linearly to `K⋆`: (4.6) `‖Kⱼ − K⋆‖_F ≤ c qʲ` for some `c ≥ 0`, `0 ≤ q < 1`. -/
theorem gradient_method_slqr_linear_rate {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hB : B ≠ 0)
    (K₀ : Matrix (Fin m) (Fin n) ℝ) (hK₀ : K₀ ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ))
    (Kstar : Matrix (Fin m) (Fin n) ℝ) (hKstar : Kstar ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ))
    (hopt : ∀ K ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ), lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig Kstar ≤ lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K)
    (L : ℝ) (hLpos : 0 < L)
    (hL : ∀ K ∈ sublevel A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀, ∀ K' ∈ sublevel A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀,
      frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K - lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K') ≤ L * frobNorm (K - K'))
    (γ : ℕ → ℝ) :
    ((∀ j, 0 < γ j ∧ γ j ≤ 2 / L) →
      (∀ j, gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j ∈ sublevel A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀) ∧
      ∀ j, lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ (j + 1)) ≤
        lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j)
          - γ j * (1 - L * γ j / 2) *
            frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j)) ^ 2) ∧
    (∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → (∀ j, ε₁ ≤ γ j ∧ γ j ≤ 2 / L - ε₂) →
      Tendsto (fun j => frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j)))
        atTop (𝓝 0) ∧
      (∀ k : ℕ, 1 ≤ k →
        (Finset.range (k + 1)).inf' ⟨0, by simp⟩
            (fun j => frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j)) ^ 2)
          ≤ lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ / (ε₁ * ε₂ * L / 2 * k)) ∧
      ∃ c q : ℝ, 0 ≤ c ∧ 0 ≤ q ∧ q < 1 ∧
        ∀ j, frobNorm (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j - Kstar) ≤ c * q ^ j) := by
  exact LQRProof.full_native_result A B Q R Sig hQ hR hSig hB K₀ hK₀ Kstar hKstar hopt L hLpos hL γ

end FatkhullinPolyak.Discrete

open FatkhullinPolyak.Discrete Filter Topology

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hB : B ≠ 0)
    (K₀ : Matrix (Fin m) (Fin n) ℝ) (hK₀ : K₀ ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ))
    (Kstar : Matrix (Fin m) (Fin n) ℝ) (hKstar : Kstar ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ))
    (hopt : ∀ K ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ), lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig Kstar ≤ lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K)
    (L : ℝ) (hLpos : 0 < L)
    (hL : ∀ K ∈ sublevel A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀, ∀ K' ∈ sublevel A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀,
      frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K - lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K') ≤ L * frobNorm (K - K'))
    (γ : ℕ → ℝ) :
    ((∀ j, 0 < γ j ∧ γ j ≤ 2 / L) →
      (∀ j, gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j ∈ sublevel A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀) ∧
      ∀ j, lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ (j + 1)) ≤
        lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j)
          - γ j * (1 - L * γ j / 2) *
            frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j)) ^ 2) ∧
    (∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → (∀ j, ε₁ ≤ γ j ∧ γ j ≤ 2 / L - ε₂) →
      Tendsto (fun j => frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j)))
        atTop (𝓝 0) ∧
      (∀ k : ℕ, 1 ≤ k →
        (Finset.range (k + 1)).inf' ⟨0, by simp⟩
            (fun j => frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j)) ^ 2)
          ≤ lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ / (ε₁ * ε₂ * L / 2 * k)) ∧
      ∃ c q : ℝ, 0 ≤ c ∧ 0 ≤ q ∧ q < 1 ∧
        ∀ j, frobNorm (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j - Kstar) ≤ c * q ^ j) := FatkhullinPolyak.Discrete.gradient_method_slqr_linear_rate A B Q R Sig hQ hR hSig hB K₀ hK₀ Kstar hKstar hopt L hLpos hL γ
