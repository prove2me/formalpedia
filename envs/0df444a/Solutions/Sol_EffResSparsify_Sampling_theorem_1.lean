-- Prove2me | solution 1 for EffResSparsify.Sampling.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T14:34:12.49482+00:00
-- url     : https://prove2.me/submissions/1aded3aa-a379-4cba-9bab-2fa3b1e97fdb

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_EffResSparsify_Sampling_Defs

-- Complete module: ERProof/SharedBasics.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def opNorm {n : ℕ} (A : Mat n) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖

def signVal (b : Bool) : ℝ := if b then 1 else -1

def signMean {q : ℕ} (f : (Fin q → Bool) → ℝ) : ℝ :=
  (1 / (2 : ℝ)^q) * ∑ s, f s

def signSeries {q n : ℕ} (A : Fin q → Mat n) (s : Fin q → Bool) : Mat n :=
  ∑ i, signVal (s i) • A i

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/FrameAlgebra.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh
open Matrix

def outer {n : ℕ} (v : Fin n → ℝ) : Mat n := fun i j => v i*v j

theorem outer_hermitian {n : ℕ} (v : Fin n → ℝ) : (outer v).IsHermitian := by
  ext i j
  simp [outer, mul_comm]

theorem outer_mulVec {n : ℕ} (v x : Fin n → ℝ) :
    outer v *ᵥ x = (v ⬝ᵥ x) • v := by
  ext i
  simp only [outer, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem outer_square {n : ℕ} (v : Fin n → ℝ) :
    outer v * outer v = (v ⬝ᵥ v) • outer v := by
  ext i j
  simp only [Matrix.mul_apply, outer, Matrix.smul_apply, smul_eq_mul, dotProduct]
  simp_rw [show ∀ k, v i*v k*(v k*v j) = v k*v k*(v i*v j) by intro k; ring]
  rw [Finset.sum_mul]

theorem outer_trace {n : ℕ} (v : Fin n → ℝ) : Matrix.trace (outer v) = v ⬝ᵥ v := rfl

theorem outer_posSemidef {n : ℕ} (v : Fin n → ℝ) : (outer v).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨outer_hermitian v, ?_⟩
  intro x
  rw [outer_mulVec, dotProduct_smul]
  simpa only [star_trivial, dotProduct_comm x v, smul_eq_mul, pow_two] using sq_nonneg (v ⬝ᵥ x)

theorem frame_energy {n : ℕ} {I : Type*} [Fintype I] (v : I → Fin n → ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((∑ i, outer (v i))*ᵥ x) = ∑ i, (v i ⬝ᵥ x)^2 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [outer_mulVec, dotProduct_smul]
  simp only [dotProduct_comm x (v i), pow_two, smul_eq_mul]

theorem frame_kernel {n : ℕ} {I : Type*} [Fintype I] (v : I → Fin n → ℝ)
    (x : Fin n → ℝ) (hx : (∑ i, outer (v i))*ᵥ x = 0) (i : I) : v i ⬝ᵥ x = 0 := by
  have h := frame_energy v x
  rw [hx, dotProduct_zero] at h
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (v j ⬝ᵥ x))).mp h.symm i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hi

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/WeightedIncidence.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh
open Matrix
variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

def weightedVec (G : WGraph (Fin n) E) (e : E) : Fin n → ℝ :=
  fun i => Real.sqrt (G.w e)*G.incidence e i

omit [Fintype E] [DecidableEq E] in
theorem weightedVec_ne_zero (G : WGraph (Fin n) E) (e : E) : weightedVec G e ≠ 0 := by
  intro h
  have he := congrFun h (G.head e)
  have hp := Real.sqrt_pos.2 (G.w_pos e)
  simp [weightedVec, WGraph.incidence] at he
  linarith

theorem laplacian_eq_frame (G : WGraph (Fin n) E) : G.laplacian = ∑ e, outer (weightedVec G e) := by
  ext i j
  simp only [Matrix.sum_apply]
  change (∑ e, (G.incidenceᵀ * Matrix.diagonal G.w) i e * G.incidence e j) =
    ∑ e, (Real.sqrt (G.w e)*G.incidence e i)*(Real.sqrt (G.w e)*G.incidence e j)
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro e _
  calc G.incidence e i * G.w e * G.incidence e j =
       (Real.sqrt (G.w e))^2 * (G.incidence e i*G.incidence e j) := by rw [Real.sq_sqrt (G.w_pos e).le]; ring
       _ = _ := by ring

theorem laplacian_posSemidef (G : WGraph (Fin n) E) : G.laplacian.PosSemidef := by
  rw [laplacian_eq_frame]
  exact Matrix.posSemidef_sum _ (fun e _ => outer_posSemidef (weightedVec G e))

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/FrameTransform.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh
open Matrix

theorem outer_congr {n : ℕ} (M : Mat n) (v : Fin n → ℝ) :
    M * outer v * Mᵀ = outer (M *ᵥ v) := by
  change M * vecMulVec v v * Mᵀ = vecMulVec (M *ᵥ v) (M *ᵥ v)
  rw [mul_vecMulVec, vecMulVec_mul, vecMul_transpose]

theorem symmetric_transpose {n : ℕ} {M : Mat n} (hM : M.IsHermitian) : Mᵀ = M := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hM.eq

theorem symmetric_dot {n : ℕ} {M : Mat n} (hM : M.IsHermitian) (x y : Fin n → ℝ) :
    (M *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (M *ᵥ y) := by
  rw [← symmetric_transpose hM, dotProduct_transpose_mulVec, symmetric_transpose hM]
  exact dotProduct_comm _ _

theorem projection_fixes_frame {n : ℕ} {I : Type*} [Fintype I]
    (v : I → Fin n → ℝ) (P : Mat n) (hP : P.IsHermitian) (hPP : P*P=P)
    (hPL : P*(∑ i,outer (v i)) = ∑ i,outer (v i)) (i : I) : P *ᵥ v i = v i := by
  let z := v i - P *ᵥ v i
  have hLP : (∑ i,outer (v i))*P = ∑ i,outer (v i) := by
    have h := congrArg Matrix.transpose hPL
    simpa only [Matrix.transpose_mul, symmetric_transpose hP, Matrix.transpose_sum,
      symmetric_transpose (outer_hermitian _)] using h
  have hz : (∑ i,outer (v i))*ᵥ z = 0 := by
    dsimp [z]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hLP, sub_self]
  have hi := frame_kernel v z hz i
  have hpz : P *ᵥ z = 0 := by
    dsimp [z]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hPP, sub_self]
  have hzsq : z ⬝ᵥ z = 0 := by
    change (v i - P *ᵥ v i) ⬝ᵥ z = 0
    rw [sub_dotProduct, symmetric_dot hP, hpz, dotProduct_zero, hi, sub_self]
  have hz0 : z = 0 := by
    apply (dotProduct_self_eq_zero).mp
    exact hzsq
  exact (sub_eq_zero.mp hz0).symm

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/TraceBasics.lean

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace EffResSparsify.Sampling.ERFresh

noncomputable def rtrace {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  Matrix.trace A

noncomputable def series {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (x : Fin n → ℝ) : Matrix (Fin d) (Fin d) ℝ := ∑ i, x i • A i

@[simp] theorem rtrace_zero {d : ℕ} : rtrace (0 : Matrix (Fin d) (Fin d) ℝ) = 0 := by
  simp [rtrace]

@[simp] theorem rtrace_one {d : ℕ} : rtrace (1 : Matrix (Fin d) (Fin d) ℝ) = d := by
  simp [rtrace]

theorem rtrace_add {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) :
    rtrace (A + B) = rtrace A + rtrace B := by simp [rtrace]

theorem rtrace_sub {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) :
    rtrace (A - B) = rtrace A - rtrace B := by simp [rtrace]

theorem rtrace_smul {d : ℕ} (a : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    rtrace (a • A) = a * rtrace A := by simp [rtrace]

theorem rtrace_sum {ι : Type*} {d : ℕ} (s : Finset ι)
    (A : ι → Matrix (Fin d) (Fin d) ℝ) :
    rtrace (∑ i ∈ s, A i) = ∑ i ∈ s, rtrace (A i) := by simp [rtrace]

theorem rtrace_mul_comm {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) :
    rtrace (A * B) = rtrace (B * A) := by
  exact Matrix.trace_mul_comm A B

theorem rtrace_conj {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) :
    rtrace ((U : Matrix (Fin d) (Fin d) ℝ) * A * star (U : Matrix (Fin d) (Fin d) ℝ)) = rtrace A := by
  rw [rtrace_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]

theorem rtrace_diagonal {d : ℕ} (a : Fin d → ℝ) :
    rtrace (Matrix.diagonal (fun i => (a i : ℝ))) = ∑ i, a i := by
  simp [rtrace]

theorem series_hermitian {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (x : Fin n → ℝ) : (series A x).IsHermitian := by
  unfold series
  apply Finset.sum_induction
  · exact fun _ _ ha hb => ha.add hb
  · exact Matrix.isHermitian_zero
  · intro i _
    exact (hA i).smul (by rfl)

theorem series_neg {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (x : Fin n → ℝ) : series A (-x) = -series A x := by
  simp [series, Finset.sum_neg_distrib]

theorem continuous_series {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℝ) :
    Continuous (series A) := by unfold series; fun_prop

theorem continuous_rtrace {d : ℕ} :
    Continuous (rtrace (d := d)) := by unfold rtrace Matrix.trace Matrix.diag; fun_prop

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/SpectralTrace.lean

open scoped MatrixOrder ComplexOrder

namespace EffResSparsify.Sampling.ERFresh

theorem rtrace_cfc {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    rtrace (cfc f A) = ∑ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, rtrace_conj]
  exact rtrace_diagonal _

theorem rtrace_pow {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (m : ℕ) :
    rtrace (A ^ m) = ∑ i, hA.eigenvalues i ^ m := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, rtrace_conj, Matrix.diagonal_pow]
  change rtrace (Matrix.diagonal (fun i => (hA.eigenvalues i : ℝ) ^ m)) = _
  simpa only [map_pow]
    using rtrace_diagonal (fun i => hA.eigenvalues i ^ m)

theorem rtrace_even_nonneg {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (p : ℕ) : 0 ≤ rtrace (A ^ (2 * p)) := by
  rw [rtrace_pow A hA]
  exact Finset.sum_nonneg (fun i _ => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/SpectralMap.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh
open Matrix

def spectralMap {n : ℕ} {A : Mat n} (hA : A.IsHermitian) (f : ℝ → ℝ) : Mat n :=
  Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary (diagonal (f ∘ hA.eigenvalues))

theorem spectralMap_id {n : ℕ} {A : Mat n} (hA : A.IsHermitian) :
    spectralMap hA id = A := hA.spectral_theorem.symm

theorem spectralMap_mul {n : ℕ} {A : Mat n} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    spectralMap hA f * spectralMap hA g = spectralMap hA (fun t => f t*g t) := by
  unfold spectralMap
  rw [← map_mul, diagonal_mul_diagonal]
  rfl

theorem spectralMap_hermitian {n : ℕ} {A : Mat n} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (spectralMap hA f).IsHermitian := by
  change star (spectralMap hA f) = spectralMap hA f
  unfold spectralMap
  rw [← map_star]
  congr 1
  exact (isHermitian_diagonal_iff.mpr (fun _ => rfl))

theorem spectralMap_congr {n : ℕ} {A : Mat n} (hA : A.IsHermitian) (f g : ℝ → ℝ)
    (hfg : ∀i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) :
    spectralMap hA f = spectralMap hA g := by
  unfold spectralMap
  congr 2
  funext i
  exact hfg i

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/PinvCharacterization.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh
open scoped InnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]

theorem pinv_mem (L : V →ₗ[ℝ] W) (y : W) :
    HarmonicGames.Decomposition.pinv L y ∈ (LinearMap.ker L)ᗮ := by
  exact ((LinearEquiv.ofInjective _
    (HarmonicGames.Decomposition.pinv_restrict_injective L)).symm
    ((LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype)).orthogonalProjectionOnto y)).property

theorem pinv_image (L : V →ₗ[ℝ] W) (y : W) :
    L (HarmonicGames.Decomposition.pinv L y) =
      (LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype)).starProjection y := by
  let e := LinearEquiv.ofInjective _
    (HarmonicGames.Decomposition.pinv_restrict_injective L)
  exact congrArg Subtype.val (e.apply_symm_apply
    ((LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype)).orthogonalProjectionOnto y))

theorem pinv_eq_of_conditions (L : V →ₗ[ℝ] W) (y : W) (x : V)
    (hx : x ∈ (LinearMap.ker L)ᗮ)
    (hr : y - L x ∈ (LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype))ᗮ) :
    HarmonicGames.Decomposition.pinv L y = x := by
  have hp := Submodule.eq_starProjection_of_mem_orthogonal
    (show L x ∈ LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype) from ⟨⟨x,hx⟩,rfl⟩) hr
  have he : L (HarmonicGames.Decomposition.pinv L y) = L x := (pinv_image L y).trans hp
  have h := HarmonicGames.Decomposition.pinv_restrict_injective L
    (a₁ := ⟨_,pinv_mem L y⟩) (a₂ := ⟨x,hx⟩) he
  exact congrArg Subtype.val h

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/PinvSymmetric.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh
open scoped InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem pinv_eq_symmetric_inverse (L K : V →ₗ[ℝ] V)
    (hL : L.IsSymmetric) (hK : K.IsSymmetric)
    (hcomm : ∀x, L (K x) = K (L x))
    (hLKL : ∀x, L (K (L x)) = L x)
    (hKLK : ∀x, K (L (K x)) = K x) :
    HarmonicGames.Decomposition.pinv L = K := by
  have hker (z : V) (hz : L z = 0) : K z = 0 := by
    calc K z = K (L (K z)) := (hKLK z).symm
      _ = K (K (L z)) := congrArg K (hcomm z)
      _ = 0 := by rw [hz, map_zero, map_zero]
  ext y
  apply pinv_eq_of_conditions
  · apply (Submodule.mem_orthogonal _ _).mpr
    intro z hz
    rw [← hK z y, hker z hz, inner_zero_left]
  · apply (Submodule.mem_orthogonal _ _).mpr
    rintro z ⟨v,rfl⟩
    change inner ℝ (L (v : V)) (y - L (K y)) = 0
    rw [hL, map_sub, hcomm y, hLKL, sub_self, inner_zero_right]

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/SpectralInverse.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh
open Matrix

def spectralInv {n : ℕ} {A : Mat n} (hA : A.IsHermitian) : Mat n :=
  spectralMap hA (fun t => t⁻¹)

theorem spectralInv_hermitian {n : ℕ} {A : Mat n} (hA : A.IsHermitian) :
    (spectralInv hA).IsHermitian := spectralMap_hermitian hA _

theorem spectralInv_comm {n : ℕ} {A : Mat n} (hA : A.IsHermitian) :
    A * spectralInv hA = spectralInv hA * A := by
  conv_lhs => lhs; rw [← spectralMap_id hA]
  conv_rhs => rhs; rw [← spectralMap_id hA]
  rw [spectralInv, spectralMap_mul, spectralMap_mul]
  apply spectralMap_congr
  intro i
  exact mul_comm _ _

theorem spectralInv_left {n : ℕ} {A : Mat n} (hA : A.IsHermitian) :
    A * spectralInv hA * A = A := by
  conv_lhs => lhs; lhs; rw [← spectralMap_id hA]
  conv_lhs => rhs; rw [← spectralMap_id hA]
  rw [spectralInv, spectralMap_mul, spectralMap_mul]
  calc _ = spectralMap hA id := by
         apply spectralMap_congr
         intro i
         by_cases h : hA.eigenvalues i = 0
         · simp [h]
         · simp [h]
       _ = A := spectralMap_id hA

/-
  apply spectralMap_congr
  intro i
  by_cases h : hA.eigenvalues i = 0
  · simp [h]
  · simp [h]

-/
theorem spectralInv_right {n : ℕ} {A : Mat n} (hA : A.IsHermitian) :
    spectralInv hA * A * spectralInv hA = spectralInv hA := by
  conv_lhs => lhs; rhs; rw [← spectralMap_id hA]
  rw [spectralInv, spectralMap_mul, spectralMap_mul]
  apply spectralMap_congr
  intro i
  by_cases h : hA.eigenvalues i = 0
  · simp [h]
  · simp [h]

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/NativePinv.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh
open Matrix

theorem native_pinv_eq_spectral {n : ℕ} {A : Mat n} (hA : A.IsHermitian) :
    HarmonicGames.Decomposition.pinv (Matrix.toEuclideanLin A) =
      Matrix.toEuclideanLin (spectralInv hA) := by
  have he (M : Mat n) (x : EuclideanSpace ℝ (Fin n)) :
      Matrix.toEuclideanCLM (𝕜 := ℝ) M x = Matrix.toEuclideanLin M x := by
    exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) => L x)
      (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin M)
  apply pinv_eq_symmetric_inverse _ _
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (spectralInv_hermitian hA))
  · intro x
    have h := congrArg (fun M : Mat n => Matrix.toEuclideanCLM (𝕜 := ℝ) M x) (spectralInv_comm hA)
    simpa only [map_mul, mul_apply_eq_comp, he] using h
  · intro x
    have h := congrArg (fun M : Mat n => Matrix.toEuclideanCLM (𝕜 := ℝ) M x) (spectralInv_left hA)
    simpa only [map_mul, mul_apply_eq_comp, he] using h
  · intro x
    have h := congrArg (fun M : Mat n => Matrix.toEuclideanCLM (𝕜 := ℝ) M x) (spectralInv_right hA)
    simpa only [map_mul, mul_apply_eq_comp, he] using h

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/SpectralNorm.lean

noncomputable section
open scoped Matrix.Norms.L2Operator
namespace EffResSparsify.Sampling.ERFresh

theorem opNorm_eq_eigen_norm {n : ℕ} {A : Mat n} (hA : A.IsHermitian) :
    opNorm A = ‖hA.eigenvalues‖ := by
  change ‖A‖ = _
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  rfl

theorem opNorm_pow_le_trace {n : ℕ} {A : Mat n} (hA : A.IsHermitian) (p : ℕ)
    (hp : 0 < p) : opNorm A ^ (2*p) ≤ rtrace (A^(2*p)) := by
  by_cases hn : n = 0
  · subst n
    simp [opNorm, rtrace, Matrix.trace, ne_of_gt hp]
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖hA.eigenvalues i‖) Finset.univ_nonempty
  have hei : ‖hA.eigenvalues i‖ = ‖hA.eigenvalues‖ :=
    le_antisymm (norm_le_pi_norm _ i) ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j => hi j (Finset.mem_univ j)))
  rw [opNorm_eq_eigen_norm hA, ← hei, rtrace_pow A hA]
  rw [Real.norm_eq_abs, pow_mul, sq_abs]
  have hnon (j : Fin n) : 0 ≤ hA.eigenvalues j ^ (2*p) := by
    rw [pow_mul]; positivity
  simpa [pow_mul] using Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/SpectralSquareRoot.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh
open Matrix

def spectralSqrt {n : ℕ} {A : Mat n} (hA : A.IsHermitian) : Mat n :=
  spectralMap hA Real.sqrt

def spectralInvSqrt {n : ℕ} {A : Mat n} (hA : A.IsHermitian) : Mat n :=
  spectralMap hA (fun t => (Real.sqrt t)⁻¹)

def spectralProj {n : ℕ} {A : Mat n} (hA : A.IsHermitian) : Mat n :=
  spectralMap hA (fun t => if t = 0 then 0 else 1)

theorem spectralSqrt_sq {n : ℕ} {A : Mat n} (hA : A.PosSemidef) :
    spectralSqrt hA.1 * spectralSqrt hA.1 = A := by
  unfold spectralSqrt
  rw [spectralMap_mul]
  calc _ = spectralMap hA.1 id := by
         apply spectralMap_congr
         intro i
         exact Real.mul_self_sqrt (hA.eigenvalues_nonneg i)
       _ = A := spectralMap_id hA.1

theorem spectralInvSqrt_sq {n : ℕ} {A : Mat n} (hA : A.PosSemidef) :
    spectralInvSqrt hA.1 * spectralInvSqrt hA.1 = spectralInv hA.1 := by
  unfold spectralInvSqrt spectralInv
  rw [spectralMap_mul]
  apply spectralMap_congr
  intro i
  rw [← mul_inv, Real.mul_self_sqrt (hA.eigenvalues_nonneg i)]

theorem spectralSqrt_invSqrt {n : ℕ} {A : Mat n} (hA : A.PosSemidef) :
    spectralSqrt hA.1 * spectralInvSqrt hA.1 = spectralProj hA.1 := by
  unfold spectralSqrt spectralInvSqrt spectralProj
  rw [spectralMap_mul]
  apply spectralMap_congr
  intro i
  by_cases h : hA.1.eigenvalues i = 0
  · simp [h]
  · simp [h, ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm h)))]

theorem spectralInvSqrt_sqrt {n : ℕ} {A : Mat n} (hA : A.PosSemidef) :
    spectralInvSqrt hA.1 * spectralSqrt hA.1 = spectralProj hA.1 := by
  have h : spectralInvSqrt hA.1 * spectralSqrt hA.1 =
      spectralSqrt hA.1 * spectralInvSqrt hA.1 := by
    unfold spectralInvSqrt spectralSqrt
    rw [spectralMap_mul, spectralMap_mul]
    apply spectralMap_congr
    intro i
    exact mul_comm _ _
  exact h.trans (spectralSqrt_invSqrt hA)

theorem spectralProj_idem {n : ℕ} {A : Mat n} (hA : A.IsHermitian) :
    spectralProj hA * spectralProj hA = spectralProj hA := by
  unfold spectralProj
  rw [spectralMap_mul]
  apply spectralMap_congr
  intro i
  split_ifs <;> norm_num

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/SpectralProjection.lean

noncomputable section
open scoped Matrix.Norms.L2Operator
namespace EffResSparsify.Sampling.ERFresh
open Matrix

theorem spectralProj_mul {n : ℕ} {A : Mat n} (hA : A.IsHermitian) :
    spectralProj hA * A = A := by
  conv_lhs => rhs; rw [← spectralMap_id hA]
  unfold spectralProj
  rw [spectralMap_mul]
  calc _ = spectralMap hA id := by
         apply spectralMap_congr
         intro i
         by_cases h : hA.eigenvalues i = 0 <;> simp [h]
       _ = A := spectralMap_id hA

theorem spectralProj_norm_le {n : ℕ} {A : Mat n} (hA : A.IsHermitian) :
    opNorm (spectralProj hA) ≤ 1 := by
  change ‖spectralProj hA‖ ≤ 1
  unfold spectralProj spectralMap
  rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro i
  change ‖if hA.eigenvalues i = 0 then (0:ℝ) else 1‖ ≤ 1
  split_ifs <;> norm_num

theorem spectralProj_trace_le {n : ℕ} {A : Mat n} (hA : A.IsHermitian) :
    Matrix.trace (spectralProj hA) ≤ n := by
  unfold spectralProj spectralMap
  rw [Unitary.conjStarAlgAut_apply]
  change rtrace _ ≤ _
  rw [rtrace_conj, rtrace_diagonal]
  calc (∑ i : Fin n, if hA.eigenvalues i = 0 then (0:ℝ) else 1) ≤ ∑ _i : Fin n, (1:ℝ) := by
         apply Finset.sum_le_sum
         intro i _
         split_ifs <;> norm_num
       _ = n := by simp

theorem spectral_whiten {n : ℕ} {A : Mat n} (hA : A.PosSemidef) :
    spectralInvSqrt hA.1 * A * spectralInvSqrt hA.1 = spectralProj hA.1 := by
  conv_lhs => lhs; rhs; rw [← spectralSqrt_sq hA]
  rw [← mul_assoc, spectralInvSqrt_sqrt hA]
  rw [mul_assoc, spectralSqrt_invSqrt hA, spectralProj_idem]

theorem spectral_unwhiten {n : ℕ} {A : Mat n} (hA : A.PosSemidef) :
    spectralSqrt hA.1 * spectralProj hA.1 * spectralSqrt hA.1 = A := by
  have h : spectralSqrt hA.1 * spectralProj hA.1 = spectralSqrt hA.1 := by
    unfold spectralSqrt spectralProj
    rw [spectralMap_mul]
    apply spectralMap_congr
    intro i
    by_cases he : hA.1.eigenvalues i = 0 <;> simp [he]
  rw [h, spectralSqrt_sq hA]

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/NativeFrame.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh
open Matrix
variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

def whiteH (G : WGraph (Fin n) E) : Mat n := spectralSqrt (laplacian_posSemidef G).1
def whiteQ (G : WGraph (Fin n) E) : Mat n := spectralInvSqrt (laplacian_posSemidef G).1
def whiteP (G : WGraph (Fin n) E) : Mat n := spectralProj (laplacian_posSemidef G).1
def whiteVec (G : WGraph (Fin n) E) (e : E) : Fin n → ℝ := whiteQ G *ᵥ weightedVec G e

theorem whiteH_hermitian (G : WGraph (Fin n) E) : (whiteH G).IsHermitian := spectralMap_hermitian _ _
theorem whiteQ_hermitian (G : WGraph (Fin n) E) : (whiteQ G).IsHermitian := spectralMap_hermitian _ _
theorem whiteP_hermitian (G : WGraph (Fin n) E) : (whiteP G).IsHermitian := spectralMap_hermitian _ _
theorem whiteP_idem (G : WGraph (Fin n) E) : whiteP G*whiteP G=whiteP G := spectralProj_idem _
theorem whiteP_norm (G : WGraph (Fin n) E) : opNorm (whiteP G) ≤ 1 := spectralProj_norm_le _
theorem whiteP_trace (G : WGraph (Fin n) E) : Matrix.trace (whiteP G) ≤ n := spectralProj_trace_le _

theorem white_lift (G : WGraph (Fin n) E) (e : E) : whiteH G *ᵥ whiteVec G e = weightedVec G e := by
  unfold whiteVec
  rw [Matrix.mulVec_mulVec]
  change (spectralSqrt _ * spectralInvSqrt _) *ᵥ _ = _
  rw [spectralSqrt_invSqrt (laplacian_posSemidef G)]
  apply projection_fixes_frame (weightedVec G) _ (whiteP_hermitian G) (whiteP_idem G)
  rw [← laplacian_eq_frame]
  exact spectralProj_mul _

theorem whiteVec_ne_zero (G : WGraph (Fin n) E) (e : E) : whiteVec G e ≠ 0 := by
  intro h
  have hl := white_lift G e
  rw [h, Matrix.mulVec_zero] at hl
  exact weightedVec_ne_zero G e hl.symm

theorem white_covariance (G : WGraph (Fin n) E) : ∑ e, outer (whiteVec G e) = whiteP G := by
  have h (e : E) : outer (whiteVec G e) = whiteQ G * outer (weightedVec G e) * whiteQ G := by
    conv_rhs => rhs; rw [← symmetric_transpose (whiteQ_hermitian G)]
    exact (outer_congr _ _).symm
  simp_rw [h]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, ← laplacian_eq_frame]
  exact spectral_whiten (laplacian_posSemidef G)

theorem white_unwhiten (G : WGraph (Fin n) E) : whiteH G*whiteP G*whiteH G=G.laplacian :=
  spectral_unwhiten (laplacian_posSemidef G)

theorem lapPinv_eq_spectral (G : WGraph (Fin n) E) :
    G.lapPinv = spectralInv (laplacian_posSemidef G).1 := by
  unfold WGraph.lapPinv
  rw [native_pinv_eq_spectral (laplacian_posSemidef G).1, LinearEquiv.symm_apply_apply]

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/NativeResistance.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh
open Matrix
variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

theorem effRes_eq_dot (G : WGraph (Fin n) E) (e : E) :
    G.effRes e = G.incidence e ⬝ᵥ (G.lapPinv *ᵥ G.incidence e) := by
  unfold WGraph.effRes
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem white_mass (G : WGraph (Fin n) E) (e : E) :
    whiteVec G e ⬝ᵥ whiteVec G e = G.w e * G.effRes e := by
  unfold whiteVec
  rw [symmetric_dot (whiteQ_hermitian G), Matrix.mulVec_mulVec]
  have hQ : whiteQ G*whiteQ G=G.lapPinv := by
    rw [lapPinv_eq_spectral]
    exact spectralInvSqrt_sq (laplacian_posSemidef G)
  rw [hQ, effRes_eq_dot]
  change ((Real.sqrt (G.w e)) • G.incidence e) ⬝ᵥ
    (G.lapPinv *ᵥ ((Real.sqrt (G.w e)) • G.incidence e)) = _
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, Real.mul_self_sqrt (G.w_pos e).le]

theorem white_mass_pos (G : WGraph (Fin n) E) (e : E) : 0 < G.w e*G.effRes e := by
  rw [← white_mass]
  apply lt_of_le_of_ne (Finset.sum_nonneg (fun j _ => mul_self_nonneg (whiteVec G e j)))
  intro h
  exact whiteVec_ne_zero G e (dotProduct_self_eq_zero.mp h.symm)

theorem white_mass_sum (G : WGraph (Fin n) E) :
    ∑ e, G.w e*G.effRes e = Matrix.trace (whiteP G) := by
  simp_rw [← white_mass, ← outer_trace]
  rw [← Matrix.trace_sum, white_covariance]

omit [Fintype E] [DecidableEq E] in
theorem graph_edge_nonempty (G : WGraph (Fin n) E) (hn : 3 ≤ n) (hc : G.IsConnected) : Nonempty E := by
  by_contra h
  have : IsEmpty E := not_nonempty_iff.mp h
  have hbot : G.toSimpleGraph = ⊥ := by
    ext a b
    simp [WGraph.toSimpleGraph, SimpleGraph.fromRel]
  have hb : (⊥ : SimpleGraph (Fin n)).Connected := hbot ▸ hc
  have hs : Subsingleton (Fin n) := (SimpleGraph.connected_bot_iff).mp hb |>.1
  have he : (⟨0,by omega⟩ : Fin n) = ⟨1,by omega⟩ := hs.elim _ _
  have h01 : (0:ℕ)=1 := congrArg Fin.val he
  omega

theorem native_mass_bounds (G : WGraph (Fin n) E) (hn : 3 ≤ n) (hc : G.IsConnected) :
    0 < (∑ e, G.w e*G.effRes e) ∧ (∑ e,G.w e*G.effRes e) ≤ n := by
  let : Nonempty E := graph_edge_nonempty G hn hc
  constructor
  · exact Finset.sum_pos (fun e _ => white_mass_pos G e) Finset.univ_nonempty
  · rw [white_mass_sum]
    exact whiteP_trace G

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/SignMean.lean

noncomputable section
open scoped BigOperators
namespace EffResSparsify.Sampling.ERFresh

variable {q : ℕ}

theorem signMean_const (c : ℝ) : signMean (fun _ : Fin q → Bool => c) = c := by
  classical
  simp [signMean, Nat.cast_pow, Nat.cast_ofNat]

theorem signMean_add (f g : (Fin q → Bool) → ℝ) :
    signMean (fun s => f s + g s) = signMean f + signMean g := by
  simp only [signMean, Finset.sum_add_distrib, mul_add]

theorem signMean_sub (f g : (Fin q → Bool) → ℝ) :
    signMean (fun s => f s - g s) = signMean f - signMean g := by
  simp only [signMean, Finset.sum_sub_distrib, mul_sub]

theorem signMean_mul (c : ℝ) (f : (Fin q → Bool) → ℝ) :
    signMean (fun s => c * f s) = c * signMean f := by
  simp only [signMean, ← Finset.mul_sum]
  ring

theorem signMean_sum {ι : Type*} (s : Finset ι) (f : ι → (Fin q → Bool) → ℝ) :
    signMean (fun b => ∑ i ∈ s, f i b) = ∑ i ∈ s, signMean (f i) := by
  classical
  unfold signMean
  rw [Finset.sum_comm]
  exact Finset.mul_sum _ _ _

theorem signMean_mono {f g : (Fin q → Bool) → ℝ} (h : ∀ s, f s ≤ g s) :
    signMean f ≤ signMean g := by
  apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => h s)
  positivity

theorem signMean_nonneg {f : (Fin q → Bool) → ℝ} (h : ∀ s, 0 ≤ f s) :
    0 ≤ signMean f := by
  simpa only [signMean_const] using signMean_mono h

def signFlip (i : Fin q) (s : Fin q → Bool) : Fin q → Bool :=
  Function.update s i (!s i)

theorem signFlip_involutive (i : Fin q) : Function.Involutive (signFlip i) := by
  intro s
  funext j
  by_cases h : j = i
  · subst j
    simp [signFlip]
  · simp [signFlip, h]

theorem signMean_flip (i : Fin q) (f : (Fin q → Bool) → ℝ) :
    signMean (fun s => f (signFlip i s)) = signMean f := by
  classical
  unfold signMean
  congr 1
  let e : (Fin q → Bool) ≃ (Fin q → Bool) :=
    ⟨signFlip i, signFlip i, signFlip_involutive i, signFlip_involutive i⟩
  exact e.sum_comp f

theorem signVal_flip (i : Fin q) (s : Fin q → Bool) :
    signVal (signFlip i s i) = -signVal (s i) := by
  cases h : s i <;> simp [signFlip, signVal, h]

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/FiniteMean.lean

noncomputable section
open scoped BigOperators
namespace EffResSparsify.Sampling.ERFresh

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]

structure FiniteLaw (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  total : ∑ i, weight i = 1

namespace FiniteLaw

def mean (P : FiniteLaw ι) (f : ι → ℝ) : ℝ := ∑ i, P.weight i * f i

theorem mean_const (P : FiniteLaw ι) (c : ℝ) : P.mean (fun _ => c) = c := by
  rw [mean, ← Finset.sum_mul, P.total, one_mul]

theorem mean_add (P : FiniteLaw ι) (f g : ι → ℝ) :
    P.mean (fun i => f i + g i) = P.mean f + P.mean g := by
  simp only [mean, mul_add, Finset.sum_add_distrib]

theorem mean_sub (P : FiniteLaw ι) (f g : ι → ℝ) :
    P.mean (fun i => f i - g i) = P.mean f - P.mean g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_mul (P : FiniteLaw ι) (c : ℝ) (f : ι → ℝ) :
    P.mean (fun i => c * f i) = c * P.mean f := by
  simp only [mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem mean_mono (P : FiniteLaw ι) {f g : ι → ℝ} (h : ∀ i, f i ≤ g i) :
    P.mean f ≤ P.mean g :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (P.nonneg i)

theorem mean_nonneg (P : FiniteLaw ι) {f : ι → ℝ} (h : ∀ i, 0 ≤ f i) :
    0 ≤ P.mean f := by
  simpa only [P.mean_const] using P.mean_mono h

def prod (P : FiniteLaw ι) (Q : FiniteLaw κ) : FiniteLaw (ι × κ) where
  weight z := P.weight z.1 * Q.weight z.2
  nonneg z := mul_nonneg (P.nonneg z.1) (Q.nonneg z.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, Q.total, mul_one, P.total]

theorem mean_prod (P : FiniteLaw ι) (Q : FiniteLaw κ) (f : ι × κ → ℝ) :
    (P.prod Q).mean f = P.mean (fun i => Q.mean (fun j => f (i,j))) := by
  simp only [mean, prod, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

def vmean (P : FiniteLaw ι) (f : ι → E) : E := ∑ i, P.weight i • f i

theorem norm_vmean_le (P : FiniteLaw ι) (f : ι → E) :
    ‖P.vmean f‖ ≤ P.mean (fun i => ‖f i‖) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (P.nonneg i)]

theorem vmean_const (P : FiniteLaw ι) (x : E) : P.vmean (fun _ => x) = x := by
  rw [vmean, ← Finset.sum_smul, P.total, one_smul]

theorem vmean_sub (P : FiniteLaw ι) (f g : ι → E) :
    P.vmean (fun i => f i - g i) = P.vmean f - P.vmean g := by
  simp only [vmean, smul_sub, Finset.sum_sub_distrib]

theorem norm_sub_vmean_le (P : FiniteLaw ι) (x : E) (f : ι → E) :
    ‖x - P.vmean f‖ ≤ P.mean (fun i => ‖x - f i‖) := by
  have h := P.norm_vmean_le (fun i => x - f i)
  rwa [P.vmean_sub, P.vmean_const] at h

end FiniteLaw
end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/ProductLaw.lean

noncomputable section
open scoped BigOperators
namespace EffResSparsify.Sampling.ERFresh
namespace FiniteLaw
variable {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq J]

def iid (P : FiniteLaw ι) (J : Type*) [Fintype J] [DecidableEq J] : FiniteLaw (J → ι) where
  weight s := ∏ j, P.weight (s j)
  nonneg s := Finset.prod_nonneg fun j _ => P.nonneg (s j)
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp only [P.total, Finset.prod_const_one]

theorem mean_iid_prod (P : FiniteLaw ι) (f : J → ι → ℝ) :
    (P.iid J).mean (fun s => ∏ j, f j (s j)) = ∏ j, P.mean (f j) := by
  classical
  simp only [mean, iid, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j a => P.weight a * f j a)).symm

theorem mean_iid_eval (P : FiniteLaw ι) (i : J) (f : ι → ℝ) :
    (P.iid J).mean (fun s => f (s i)) = P.mean f := by
  classical
  have h := P.mean_iid_prod (fun j a => if j = i then f a else 1)
  have he (j : J) : P.mean (fun a => if j = i then f a else 1) =
      if j = i then P.mean f else 1 := by
    by_cases hj : j = i <;> simp [hj, P.mean_const]
  simp_rw [he] at h
  simpa only [Finset.prod_ite_eq', Finset.mem_univ, if_true] using h

omit [DecidableEq J] in
theorem mean_equiv (P : FiniteLaw ι) (e : ι ≃ ι)
    (he : ∀ i, P.weight (e i) = P.weight i) (f : ι → ℝ) :
    P.mean (fun i => f (e i)) = P.mean f := by
  unfold mean
  calc
    ∑ i, P.weight i * f (e i) = ∑ i, P.weight (e i) * f (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [he]
    _ = ∑ i, P.weight i * f i := e.sum_comp (fun i => P.weight i * f i)

omit [DecidableEq J] in
theorem mean_comm (P : FiniteLaw ι) (Q : FiniteLaw J) (f : ι → J → ℝ) :
    P.mean (fun i => Q.mean (f i)) = Q.mean (fun j => P.mean (fun i => f i j)) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vmean_iid_eval (P : FiniteLaw ι) (i : J) (f : ι → E) :
    (P.iid J).vmean (fun s => f (s i)) = P.vmean f := by
  classical
  have he (s : J → ι) : f (s i) = ∑ a, (if s i = a then (1:ℝ) else 0) • f a := by
    simp
  simp_rw [vmean, he, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [smul_smul]
  rw [← Finset.sum_smul]
  have hm := P.mean_iid_eval i (fun b => if b = a then (1:ℝ) else 0)
  change (∑ s, (P.iid J).weight s * (if s i = a then 1 else 0)) = _ at hm
  simp only [mean, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at hm
  simp only [mul_ite, mul_one, mul_zero]
  rw [hm]

end FiniteLaw
end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/FiniteMarkov.lean

noncomputable section
open scoped BigOperators
namespace EffResSparsify.Sampling.ERFresh
namespace FiniteLaw
variable {ι : Type*} [Fintype ι]

open Classical in
def prob (P : FiniteLaw ι) (s : Set ι) : ℝ := P.mean (fun i => if i ∈ s then 1 else 0)

theorem prob_nonneg (P : FiniteLaw ι) (s : Set ι) : 0 ≤ P.prob s := by
  classical
  apply P.mean_nonneg
  intro i
  split_ifs <;> norm_num

theorem prob_compl (P : FiniteLaw ι) (s : Set ι) : P.prob sᶜ = 1 - P.prob s := by
  classical
  unfold prob mean
  calc
    _ = ∑ i, (P.weight i - P.weight i * (if i ∈ s then (1:ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ s <;> simp [hi]
    _ = _ := by rw [Finset.sum_sub_distrib, P.total]

theorem markov (P : FiniteLaw ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    {a : ℝ} (ha : 0 < a) : P.prob {i | a < f i} ≤ P.mean f / a := by
  classical
  apply (le_div_iff₀ ha).2
  rw [mul_comm]
  change a * P.mean (fun i => if a < f i then 1 else 0) ≤ P.mean f
  rw [← P.mean_mul]
  apply P.mean_mono
  intro i
  split_ifs with hi
  · simpa only [mul_one] using hi.le
  · simpa only [mul_zero] using hf i

theorem good_half (P : FiniteLaw ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    {a : ℝ} (ha : 0 < a) (hmean : P.mean f ≤ a / 2) :
    1 / 2 ≤ P.prob {i | f i ≤ a} := by
  have hm := P.markov f hf ha
  have he : {i | f i ≤ a} = {i | a < f i}ᶜ := by ext i; simp
  rw [he, P.prob_compl]
  have hd : P.mean f / a ≤ 1 / 2 := (div_le_iff₀ ha).2 (by linarith)
  linarith

theorem mean_sq_le (P : FiniteLaw ι) (f : ι → ℝ) :
    (P.mean f)^2 ≤ P.mean (fun i => (f i)^2) := by
  have h := P.mean_nonneg (fun i => sq_nonneg (f i - P.mean f))
  have he : (fun i => (f i - P.mean f)^2) =
      (fun i => (f i)^2 - (2 * P.mean f) * f i + (P.mean f)^2) := by
    funext i
    ring
  rw [he, P.mean_add, P.mean_sub, P.mean_mul, P.mean_const] at h
  nlinarith

theorem mean_sqrt_le (P : FiniteLaw ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    P.mean (fun i => Real.sqrt (f i)) ≤ Real.sqrt (P.mean f) := by
  have h := P.mean_sq_le (fun i => Real.sqrt (f i))
  have he : (fun i => (Real.sqrt (f i))^2) = f := by
    funext i
    exact Real.sq_sqrt (hf i)
  rw [he] at h
  have hs := Real.sq_sqrt (P.mean_nonneg hf)
  have hn := Real.sqrt_nonneg (P.mean f)
  nlinarith

end FiniteLaw
end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/NativeCounts.lean

noncomputable section
open scoped BigOperators
namespace EffResSparsify.Sampling.ERFresh
variable {E F : Type*} [Fintype E] [DecidableEq E] [AddCommMonoid F]

theorem sum_eq_sampleCount {q : ℕ} (s : Fin q → E) (f : E → F) :
    (∑ i, f (s i)) = ∑ e, WGraph.sampleCount s e • f e := by
  classical
  calc
    _ = ∑ e, ∑ i : Fin q, if s i = e then f e else 0 := by
      rw [Finset.sum_comm]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, WGraph.sampleCount]

theorem sum_eq_sampleCount_real {q : ℕ} (s : Fin q → E) (f : E → ℝ) :
    (∑ i, f (s i)) = ∑ e, (WGraph.sampleCount s e : ℝ) * f e := by
  simpa only [nsmul_eq_mul] using sum_eq_sampleCount s f

variable {n : ℕ}

def graphLaw (G : WGraph (Fin n) E) (hp : ∀ e, 0 ≤ G.sampleProb e)
    (ht : ∑ e, G.sampleProb e = 1) : FiniteLaw E := ⟨G.sampleProb, hp, ht⟩

theorem graphLaw_outcome (G : WGraph (Fin n) E) (hp : ∀ e, 0 ≤ G.sampleProb e)
    (ht : ∑ e, G.sampleProb e = 1) (q : ℕ) (s : Fin q → E) :
    ((graphLaw G hp ht).iid (Fin q)).weight s = G.outcomeProb q s := rfl

theorem graphLaw_prob (G : WGraph (Fin n) E) (hp : ∀ e, 0 ≤ G.sampleProb e)
    (ht : ∑ e, G.sampleProb e = 1) (q : ℕ) (B : (Fin q → E) → Prop) :
    ((graphLaw G hp ht).iid (Fin q)).prob {s | B s} = G.sparsifyProb q B := by
  classical
  unfold FiniteLaw.prob FiniteLaw.mean WGraph.sparsifyProb
  apply Finset.sum_congr rfl
  intro s _
  rw [graphLaw_outcome]
  simp only [Set.mem_ofPred_eq, mul_ite, mul_one, mul_zero]

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/SampleMatrices.lean

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace EffResSparsify.Sampling.ERFresh
open Matrix
variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

def nativeMass (G : WGraph (Fin n) E) : ℝ := ∑ e, G.w e * G.effRes e

theorem sampleProb_pos (G : WGraph (Fin n) E) (hm : 0 < nativeMass G) (e : E) :
    0 < G.sampleProb e := div_pos (white_mass_pos G e) hm

theorem sampleProb_sum (G : WGraph (Fin n) E) (hm : 0 < nativeMass G) :
    ∑ e, G.sampleProb e = 1 := by
  simp only [WGraph.sampleProb, ← Finset.sum_div]
  exact div_self (ne_of_gt hm)

def sampleMatrix (G : WGraph (Fin n) E) (e : E) : Mat n :=
  (G.sampleProb e)⁻¹ • outer (whiteVec G e)

def samplingLaw (G : WGraph (Fin n) E) (hm : 0 < nativeMass G) : FiniteLaw E :=
  graphLaw G (fun e => (sampleProb_pos G hm e).le) (sampleProb_sum G hm)

theorem sampleMatrix_hermitian (G : WGraph (Fin n) E) (e : E) :
    (sampleMatrix G e).IsHermitian := by
  unfold sampleMatrix
  exact (outer_hermitian _).smul (by rfl)

theorem sampleMatrix_mean (G : WGraph (Fin n) E) (hm : 0 < nativeMass G) :
    (samplingLaw G hm).vmean (sampleMatrix G) = whiteP G := by
  unfold FiniteLaw.vmean samplingLaw graphLaw sampleMatrix
  simp only [smul_smul]
  have he (e : E) : G.sampleProb e * (G.sampleProb e)⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt (sampleProb_pos G hm e))
  simp_rw [he, one_smul]
  exact white_covariance G

theorem sampleMatrix_square (G : WGraph (Fin n) E) (hm : 0 < nativeMass G) (e : E) :
    (sampleMatrix G e)^2 = nativeMass G • sampleMatrix G e := by
  unfold sampleMatrix
  rw [pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul, outer_square,
    smul_smul, white_mass, smul_smul]
  congr 1
  have hp := ne_of_gt (sampleProb_pos G hm e)
  have hm0 := ne_of_gt hm
  have hrel : G.sampleProb e * nativeMass G = G.w e * G.effRes e := by
    change (G.w e * G.effRes e / nativeMass G) * nativeMass G = _
    exact div_mul_cancel₀ _ hm0
  field_simp [hp]
  nlinarith [hrel]

theorem samplingLaw_probability (G : WGraph (Fin n) E) (hm : 0 < nativeMass G)
    (q : ℕ) (B : (Fin q → E) → Prop) :
    ((samplingLaw G hm).iid (Fin q)).prob {s | B s} = G.sparsifyProb q B :=
  graphLaw_prob G _ _ q B

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/PairSwap.lean

noncomputable section
open scoped BigOperators
namespace EffResSparsify.Sampling.ERFresh
variable {ι : Type*} [Fintype ι] {q : ℕ}

def pairSwap (s : Fin q → Bool) (z : (Fin q → ι) × (Fin q → ι)) :=
  ((fun i => if s i then z.1 i else z.2 i),
   (fun i => if s i then z.2 i else z.1 i))

omit [Fintype ι] in
theorem pairSwap_involutive (s : Fin q → Bool) : Function.Involutive (pairSwap (ι := ι) s) := by
  intro z
  apply Prod.ext <;> funext i <;> cases h : s i <;> simp [pairSwap, h]

def pairSwapEquiv (s : Fin q → Bool) :
    ((Fin q → ι) × (Fin q → ι)) ≃ ((Fin q → ι) × (Fin q → ι)) :=
  ⟨pairSwap s, pairSwap s, pairSwap_involutive s, pairSwap_involutive s⟩

theorem pairSwap_weight (P : FiniteLaw ι) (s : Fin q → Bool)
    (z : (Fin q → ι) × (Fin q → ι)) :
    ((P.iid (Fin q)).prod (P.iid (Fin q))).weight (pairSwap s z) =
      ((P.iid (Fin q)).prod (P.iid (Fin q))).weight z := by
  simp only [FiniteLaw.prod, FiniteLaw.iid, pairSwap, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> simp [mul_comm]

theorem pairSwap_mean (P : FiniteLaw ι) (s : Fin q → Bool)
    (f : ((Fin q → ι) × (Fin q → ι)) → ℝ) :
    ((P.iid (Fin q)).prod (P.iid (Fin q))).mean (fun z => f (pairSwap s z)) =
      ((P.iid (Fin q)).prod (P.iid (Fin q))).mean f :=
  FiniteLaw.mean_equiv _ (pairSwapEquiv s) (pairSwap_weight P s) f

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def signedSum (A : Fin q → E) (s : Fin q → Bool) : E := ∑ i, signVal (s i) • A i

omit [Fintype ι] in
theorem pairSwap_difference (A : ι → E) (s : Fin q → Bool)
    (z : (Fin q → ι) × (Fin q → ι)) :
    (∑ i, A ((pairSwap s z).1 i)) - (∑ i, A ((pairSwap s z).2 i)) =
      signedSum (fun i => A (z.1 i) - A (z.2 i)) s := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases h : s i <;> simp [pairSwap, signVal, h, neg_sub]

theorem signedSum_sub (A B : Fin q → E) (s : Fin q → Bool) :
    signedSum (fun i => A i - B i) s = signedSum A s - signedSum B s := by
  simp only [signedSum, smul_sub, Finset.sum_sub_distrib]

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/Symmetrization.lean

noncomputable section
open scoped BigOperators
namespace EffResSparsify.Sampling.ERFresh
variable {ι : Type*} [Fintype ι] {q : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mean_signMean_comm (P : FiniteLaw ι) (f : ι → (Fin q → Bool) → ℝ) :
    P.mean (fun i => signMean (f i)) = signMean (fun s => P.mean (fun i => f i s)) := by
  simp only [FiniteLaw.mean, signMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem iid_vmean_sum (P : FiniteLaw ι) (A : ι → E) :
    (P.iid (Fin q)).vmean (fun z => ∑ i, A (z i)) = (q : ℝ) • P.vmean A := by
  calc
    _ = ∑ i : Fin q, (P.iid (Fin q)).vmean (fun z => A (z i)) := by
      simp only [FiniteLaw.vmean, Finset.smul_sum]
      rw [Finset.sum_comm]
    _ = ∑ _i : Fin q, P.vmean A := by simp_rw [P.vmean_iid_eval]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.cast_smul_eq_nsmul]

theorem finite_symmetrization (P : FiniteLaw ι) (A : ι → E) :
    (P.iid (Fin q)).mean (fun z => ‖(∑ i, A (z i)) - (q:ℝ) • P.vmean A‖) ≤
      2 * (P.iid (Fin q)).mean (fun z => signMean (fun s => ‖signedSum (fun i => A (z i)) s‖)) := by
  let Q := P.iid (Fin q)
  let F : (Fin q → ι) → E := fun z => ∑ i, A (z i)
  have hsym : Q.mean (fun z => ‖F z - (q:ℝ) • P.vmean A‖) ≤
      (Q.prod Q).mean (fun z => ‖F z.1 - F z.2‖) := by
    rw [FiniteLaw.mean_prod]
    apply Q.mean_mono
    intro z
    simpa only [F, ← iid_vmean_sum P A] using Q.norm_sub_vmean_le (F z) F
  have hinv (s : Fin q → Bool) :
      (Q.prod Q).mean (fun z => ‖signedSum (fun i => A (z.1 i) - A (z.2 i)) s‖) =
        (Q.prod Q).mean (fun z => ‖F z.1 - F z.2‖) := by
    simpa only [pairSwap_difference, F] using pairSwap_mean P s (fun z => ‖F z.1 - F z.2‖)
  have htri : (Q.prod Q).mean (fun z => signMean (fun s =>
      ‖signedSum (fun i => A (z.1 i) - A (z.2 i)) s‖)) ≤
      2 * Q.mean (fun z => signMean (fun s => ‖signedSum (fun i => A (z i)) s‖)) := by
    calc
      _ ≤ (Q.prod Q).mean (fun z => signMean (fun s =>
          ‖signedSum (fun i => A (z.1 i)) s‖ + ‖signedSum (fun i => A (z.2 i)) s‖)) := by
        apply FiniteLaw.mean_mono
        intro z
        apply signMean_mono
        intro s
        rw [signedSum_sub]
        exact norm_sub_le _ _
      _ = _ := by
        simp only [signMean_add, FiniteLaw.mean_prod, FiniteLaw.mean_add,
          FiniteLaw.mean_const]
        ring
  rw [mean_signMean_comm] at htri
  simp_rw [hinv] at htri
  rw [signMean_const] at htri
  exact hsym.trans htri

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/CovarianceBound.lean

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace EffResSparsify.Sampling.ERFresh
variable {ι : Type*} [Fintype ι] {n q : ℕ}

theorem opNorm_eq_norm (A : Mat n) : opNorm A = ‖A‖ := rfl

theorem covariance_self_bound (P0 : FiniteLaw ι) (A : ι → Mat n) (P : Mat n)
    (hmean : P0.vmean A = P) (hP : opNorm P ≤ 1)
    {r K : ℝ} (hr : 0 ≤ r) (hK : 0 ≤ K) (hA : ∀ e, (A e)^2 = r • A e)
    (hsign : ∀ z : Fin q → ι,
      signMean (fun s => opNorm (signSeries (fun i => A (z i)) s)) ≤
        K * Real.sqrt (opNorm (∑ i, (A (z i))^2))) :
    let D := (P0.iid (Fin q)).mean (fun z => opNorm ((∑ i, A (z i)) - (q:ℝ) • P))
    D^2 ≤ 4 * K^2 * r * ((q:ℝ) + D) := by
  dsimp only
  let Q := P0.iid (Fin q)
  let S : (Fin q → ι) → Mat n := fun z => ∑ i, A (z i)
  let D := Q.mean (fun z => ‖S z - (q:ℝ) • P‖)
  have hD : 0 ≤ D := Q.mean_nonneg (fun _ => norm_nonneg _)
  have hS (z : Fin q → ι) : ‖S z‖ ≤ (q:ℝ) + ‖S z - (q:ℝ) • P‖ := by
    have hnorm : ‖(q:ℝ) • P‖ ≤ (q:ℝ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg q)]
      have hp : ‖P‖ ≤ 1 := hP
      nlinarith
    have ht := norm_add_le (S z - (q:ℝ) • P) ((q:ℝ) • P)
    simp only [sub_add_cancel] at ht
    linarith
  have hSmean : Q.mean (fun z => ‖S z‖) ≤ (q:ℝ) + D := by
    calc
      _ ≤ Q.mean (fun z => (q:ℝ) + ‖S z - (q:ℝ) • P‖) := Q.mean_mono hS
      _ = _ := by rw [Q.mean_add, Q.mean_const]
  have hsquare (z : Fin q → ι) : opNorm (∑ i, (A (z i))^2) = r * ‖S z‖ := by
    simp_rw [hA]
    rw [← Finset.smul_sum, opNorm_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  have hsym : D ≤ 2 * Q.mean (fun z => signMean (fun s =>
      opNorm (signSeries (fun i => A (z i)) s))) := by
    simpa only [D, S, Q, hmean, opNorm_eq_norm, signedSum, signSeries]
      using finite_symmetrization (q := q) P0 A
  have hroot : Q.mean (fun z => Real.sqrt (r * ‖S z‖)) ≤
      Real.sqrt (r * ((q:ℝ) + D)) := by
    calc
      _ ≤ Real.sqrt (Q.mean (fun z => r * ‖S z‖)) :=
        Q.mean_sqrt_le _ (fun _ => mul_nonneg hr (norm_nonneg _))
      _ ≤ _ := by
        rw [Q.mean_mul]
        exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hSmean hr)
  have hbound : D ≤ 2 * K * Real.sqrt (r * ((q:ℝ) + D)) := by
    calc
      D ≤ 2 * Q.mean (fun z => K * Real.sqrt (r * ‖S z‖)) := by
        apply hsym.trans
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Q.mean_mono
        intro z
        simpa only [hsquare] using hsign z
      _ = 2 * K * Q.mean (fun z => Real.sqrt (r * ‖S z‖)) := by rw [Q.mean_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hroot (by positivity)
  have hsq := mul_self_le_mul_self hD hbound
  have hrq : 0 ≤ r * ((q:ℝ) + D) := mul_nonneg hr (by positivity)
  have hs := Real.sq_sqrt hrq
  change D^2 ≤ 4*K^2*r*((q:ℝ)+D)
  have he : 2*K*Real.sqrt (r*((q:ℝ)+D)) * (2*K*Real.sqrt (r*((q:ℝ)+D))) =
      4*K^2*r*((q:ℝ)+D) := by
    calc
      _ = 4*K^2*(Real.sqrt (r*((q:ℝ)+D)))^2 := by ring
      _ = _ := by rw [hs]; ring
  rw [he] at hsq
  nlinarith

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/TraceOverlap.lean

namespace EffResSparsify.Sampling.ERFresh

theorem rtrace_diagonal_overlap {d : ℕ} (a b : Fin d → ℝ)
    (U : Mat d) :
    rtrace (Matrix.diagonal a * U * Matrix.diagonal b * star U) =
      ∑ i, ∑ j, a i * b j * (U i j)^2 := by
  simp only [rtrace, Matrix.trace, Matrix.diag]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ j, ((Matrix.diagonal a * U * Matrix.diagonal b) i j) * U i j) = _
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem rtrace_conj_product {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℝ)
    (B C : Mat d) :
    rtrace (((U : Mat d) * B * star (U : Mat d)) *
      ((V : Mat d) * C * star (V : Mat d))) =
      rtrace (B * (star (U : Mat d) * (V : Mat d)) * C *
        star (star (U : Mat d) * (V : Mat d))) := by
  simp only [star_mul, star_star, mul_assoc]
  rw [rtrace_mul_comm (U : Mat d)]
  simp only [mul_assoc]

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/MixedSpectral.lean

namespace EffResSparsify.Sampling.ERFresh

noncomputable def overlap {d : ℕ} {B C : Matrix (Fin d) (Fin d) ℝ}
    (hB : B.IsHermitian) (hC : C.IsHermitian) (i j : Fin d) : ℝ :=
  ((star (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) *
    (hC.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) i j)^2

theorem overlap_nonneg {d : ℕ} {B C : Matrix (Fin d) (Fin d) ℝ}
    (hB : B.IsHermitian) (hC : C.IsHermitian) (i j : Fin d) :
    0 ≤ overlap hB hC i j := sq_nonneg _

theorem spectral_power {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ)
    (hB : B.IsHermitian) (r : ℕ) :
    B ^ r = (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) *
      Matrix.diagonal (fun i => ((hB.eigenvalues i ^ r : ℝ) : ℝ)) *
        star (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) := by
  conv_lhs => rw [hB.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.diagonal_pow]
  congr 2

theorem rtrace_mixed_pow {d : ℕ} (B C : Matrix (Fin d) (Fin d) ℝ)
    (hB : B.IsHermitian) (hC : C.IsHermitian) (r s : ℕ) :
    rtrace (B ^ r * C ^ s) =
      ∑ i, ∑ j, (hB.eigenvalues i ^ r) * (hC.eigenvalues j ^ s) * overlap hB hC i j := by
  rw [spectral_power B hB r, spectral_power C hC s, rtrace_conj_product,
    rtrace_diagonal_overlap]
  rfl

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/SecantAlgebra.lean

namespace EffResSparsify.Sampling.ERFresh

theorem rtrace_cycle {d : ℕ} (A B C : Matrix (Fin d) (Fin d) ℝ) :
    rtrace (A * B * C) = rtrace (C * A * B) :=
  Matrix.trace_mul_cycle A B C

theorem secant_trace_expand {d : ℕ} (B C : Matrix (Fin d) (Fin d) ℝ) (m : ℕ) :
    rtrace ((B-C)*(B^m-C^m)) =
      rtrace (B^(m+1)*C^0) - rtrace (B^1*C^m) -
        rtrace (B^m*C^1) + rtrace (B^0*C^(m+1)) := by
  simp only [pow_zero, pow_one, mul_one, one_mul, sub_mul, mul_sub, rtrace_sub]
  rw [pow_succ', pow_succ', rtrace_mul_comm C (B^m)]
  ring

theorem square_trace_expand {d : ℕ} (B C : Matrix (Fin d) (Fin d) ℝ) (r : ℕ) :
    rtrace ((B-C)^2*(B^r+C^r)) =
      rtrace (B^(r+2)*C^0) + rtrace (B^2*C^r) + rtrace (B^r*C^2) +
        rtrace (B^0*C^(r+2)) - 2*rtrace (B^(r+1)*C^1) -
          2*rtrace (B^1*C^(r+1)) := by
  have hex : (B-C)^2*(B^r+C^r) =
      B*B*B^r + B*B*C^r - B*C*B^r - B*C*C^r - C*B*B^r - C*B*C^r +
        C*C*B^r + C*C*C^r := by noncomm_ring
  have h1 : rtrace (B*C*B^r) = rtrace (B^(r+1)*C) := by
    rw [rtrace_cycle, ← pow_succ]
  have h2 : rtrace (C*B*B^r) = rtrace (B^(r+1)*C) := by
    rw [mul_assoc, ← pow_succ', rtrace_mul_comm]
  have h3 : rtrace (B*C*C^r) = rtrace (B*C^(r+1)) := by
    rw [mul_assoc, ← pow_succ']
  have h4 : rtrace (C*B*C^r) = rtrace (B*C^(r+1)) := by
    rw [rtrace_cycle, ← pow_succ, rtrace_mul_comm]
  have h5 : rtrace (C*C*B^r) = rtrace (B^r*C^2) := by
    rw [rtrace_mul_comm, pow_two]
  have h6 (A : Matrix (Fin d) (Fin d) ℝ) : A*A*A^r = A^(r+2) := by
    rw [← pow_two, ← pow_add]
    congr 1
    omega
  rw [hex]
  simp only [rtrace_add, rtrace_sub, h1, h2, h3, h4, h5, h6,
    pow_zero, pow_one, mul_one, one_mul, pow_two]
  ring

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/ScalarSecant.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh
open MeasureTheory Set

theorem odd_power_secant (p : ℕ) (a b : ℝ) :
    (a - b) * (a ^ (2 * p + 1) - b ^ (2 * p + 1)) ≤
      ((2 * p + 1 : ℕ) : ℝ) / 2 * (a - b) ^ 2 * (a ^ (2 * p) + b ^ (2 * p)) := by
  let m : ℝ := (2 * p + 1 : ℕ)
  let F : ℝ → ℝ := fun t => (a - b) * (b + t * (a - b)) ^ (2 * p + 1)
  let f : ℝ → ℝ := fun t => m * (a - b) ^ 2 * (b + t * (a - b)) ^ (2 * p)
  let g : ℝ → ℝ := fun t => m * (a - b) ^ 2 * ((1 - t) * b ^ (2 * p) + t * a ^ (2 * p))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hd (t : ℝ) : HasDerivAt F (f t) t := by
    have h := (((hasDerivAt_id t).mul_const (a - b)).const_add b).pow (2 * p + 1)
    have h' := h.const_mul (a - b)
    apply h'.congr_deriv
    dsimp [f, m]
    ring
  have he : (∫ t in (0 : ℝ)..1, f t) = F 1 - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hf.intervalIntegrable (μ := volume) 0 1)
  have hfg : (∫ t in (0 : ℝ)..1, f t) ≤ ∫ t in (0 : ℝ)..1, g t := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hf.intervalIntegrable (μ := volume) 0 1)
      (hg.intervalIntegrable (μ := volume) 0 1)
    intro t ht
    have hc := (show Even (2 * p) from even_two_mul p).convexOn_pow (𝕜 := ℝ)
    have hb := hc.2 (mem_univ b) (mem_univ a) (by linarith [ht.2] : 0 ≤ 1 - t)
      ht.1 (by ring : (1 - t) + t = 1)
    have hh : (b + t * (a - b)) ^ (2 * p) ≤ (1 - t) * b ^ (2 * p) + t * a ^ (2 * p) := by
      simpa only [smul_eq_mul, show (1 - t) * b + t * a = b + t * (a - b) by ring] using hb
    exact mul_le_mul_of_nonneg_left hh (by dsimp [m]; positivity)
  have hge : (∫ t in (0 : ℝ)..1, g t) =
      m / 2 * (a - b) ^ 2 * (a ^ (2 * p) + b ^ (2 * p)) := by
    have hg' : g = fun t => m * (a - b) ^ 2 * b ^ (2 * p) +
        (m * (a - b) ^ 2 * (a ^ (2 * p) - b ^ (2 * p))) * t := by
      funext t; dsimp [g]; ring
    have hi := intervalIntegral.integral_add ((show Continuous (fun _ : ℝ => m * (a - b) ^ 2 * b ^ (2 * p)) from continuous_const).intervalIntegrable (μ := volume) 0 1)
      ((show Continuous (fun t : ℝ => m * (a - b) ^ 2 * (a ^ (2 * p) - b ^ (2 * p)) * t) by fun_prop).intervalIntegrable (μ := volume) 0 1)
    rw [hg', hi, intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
    norm_num
    ring
  rw [he, hge] at hfg
  dsimp [F, m] at hfg ⊢
  simp only [one_mul, zero_mul, add_zero] at hfg
  rw [show b + (a - b) = a by ring] at hfg
  nlinarith

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/MatrixSecant.lean

namespace EffResSparsify.Sampling.ERFresh

theorem secant_trace_spectral {d : ℕ} (B C : Matrix (Fin d) (Fin d) ℝ)
    (hB : B.IsHermitian) (hC : C.IsHermitian) (m : ℕ) :
    rtrace ((B-C)*(B^m-C^m)) = ∑ i, ∑ j,
      ((hB.eigenvalues i - hC.eigenvalues j) *
        (hB.eigenvalues i ^ m - hC.eigenvalues j ^ m)) * overlap hB hC i j := by
  rw [secant_trace_expand]
  simp_rw [rtrace_mixed_pow B C hB hC]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [pow_zero, pow_succ]
  ring

theorem square_trace_spectral {d : ℕ} (B C : Matrix (Fin d) (Fin d) ℝ)
    (hB : B.IsHermitian) (hC : C.IsHermitian) (r : ℕ) :
    rtrace ((B-C)^2*(B^r+C^r)) = ∑ i, ∑ j,
      ((hB.eigenvalues i - hC.eigenvalues j)^2 *
        (hB.eigenvalues i ^ r + hC.eigenvalues j ^ r)) * overlap hB hC i j := by
  rw [square_trace_expand]
  simp_rw [rtrace_mixed_pow B C hB hC]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [pow_zero, pow_succ]
  ring

theorem matrix_odd_power_secant {d : ℕ} (B C : Matrix (Fin d) (Fin d) ℝ)
    (hB : B.IsHermitian) (hC : C.IsHermitian) (p : ℕ) :
    rtrace ((B-C)*(B^(2*p+1)-C^(2*p+1))) ≤
      ((2*p+1 : ℕ) : ℝ)/2 * rtrace ((B-C)^2*(B^(2*p)+C^(2*p))) := by
  rw [secant_trace_spectral B C hB hC, square_trace_spectral B C hB hC]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h := mul_le_mul_of_nonneg_right
    (odd_power_secant p (hB.eigenvalues i) (hC.eigenvalues j))
    (overlap_nonneg hB hC i j)
  convert h using 1
  ring

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/SignTraceAlgebra.lean

namespace EffResSparsify.Sampling.ERFresh

theorem rademacher_trace_step {d : ℕ} (H A : Matrix (Fin d) (Fin d) ℝ)
    (hH : H.IsHermitian) (hA : A.IsHermitian) (p : ℕ) :
    (rtrace (A*(H+A)^(2*p+1))-rtrace (A*(H-A)^(2*p+1)))/2 ≤
      ((2*p+1 : ℕ):ℝ) *
        (rtrace (A^2*(H+A)^(2*p))+rtrace (A^2*(H-A)^(2*p)))/2 := by
  have h := matrix_odd_power_secant (H+A) (H-A) (hH.add hA) (hH.sub hA) p
  have hd : H+A-(H-A) = (2:ℝ) • A := by module
  have hs : ((2:ℝ) • A)^2 = (4:ℝ) • A^2 := by
    simp only [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul]
    norm_num
  rw [hd, hs, smul_mul_assoc, rtrace_smul, smul_mul_assoc, rtrace_smul,
    mul_sub, rtrace_sub, mul_add, rtrace_add] at h
  linarith

theorem trace_series_power_step {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (x : Fin n → ℝ) (m : ℕ) :
    rtrace (series A x ^ (m+1)) = ∑ i, x i * rtrace (A i * series A x ^ m) := by
  rw [pow_succ']
  conv_lhs => arg 1; lhs; unfold series
  rw [Finset.sum_mul, rtrace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_mul_assoc, rtrace_smul]

theorem trace_variance_sum {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ) :
    ∑ i, rtrace (A i ^ 2 * H) = rtrace ((∑ i, A i ^ 2) * H) := by
  rw [Finset.sum_mul, rtrace_sum]

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/SignCoordinates.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh

def signRest {q n : ℕ} (A : Fin q → Mat n) (i : Fin q) (s : Fin q → Bool) : Mat n :=
  ∑ j ∈ Finset.univ.erase i, signVal (s j) • A j

theorem signSeries_split {q n : ℕ} (A : Fin q → Mat n) (i : Fin q) (s : Fin q → Bool) :
    signSeries A s = signRest A i s + signVal (s i) • A i := by
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm

theorem signRest_flip {q n : ℕ} (A : Fin q → Mat n) (i : Fin q) (s : Fin q → Bool) :
    signRest A i (signFlip i s) = signRest A i s := by
  apply Finset.sum_congr rfl
  intro j hj
  simp only [signFlip, Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem signRest_hermitian {q n : ℕ} (A : Fin q → Mat n) (hA : ∀i,(A i).IsHermitian)
    (i : Fin q) (s : Fin q → Bool) : (signRest A i s).IsHermitian := by
  unfold signRest
  apply Finset.sum_induction
  · exact fun _ _ ha hb => ha.add hb
  · exact Matrix.isHermitian_zero
  · intro j _
    exact (hA j).smul (by rfl)

theorem sign_pair_bound {q n : ℕ} (A : Fin q → Mat n) (hA : ∀i,(A i).IsHermitian)
    (i : Fin q) (s : Fin q → Bool) (p : ℕ) :
    signVal (s i) * rtrace (A i * signSeries A s ^ (2*p+1)) +
      signVal (signFlip i s i) * rtrace (A i * signSeries A (signFlip i s) ^ (2*p+1)) ≤
    (2*p+1 : ℕ) * (rtrace (A i^2*signSeries A s^(2*p)) +
      rtrace (A i^2*signSeries A (signFlip i s)^(2*p))) := by
  have h := rademacher_trace_step (signRest A i s) (A i) (signRest_hermitian A hA i s) (hA i) p
  rw [signSeries_split A i s, signSeries_split A i (signFlip i s), signRest_flip]
  simp only [signFlip, Function.update_self]
  cases hb : s i <;> simp [signVal, sub_eq_add_neg] at h ⊢ <;> linarith

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/VarianceOrder.lean

open scoped Matrix.Norms.L2Operator

namespace EffResSparsify.Sampling.ERFresh

theorem eigenvalue_le_opNorm {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ)
    (hV : V.IsHermitian) (i : Fin d) : hV.eigenvalues i ≤ opNorm V := by
  let : Nonempty (Fin d) := ⟨i⟩
  have h := spectrum.norm_le_norm_of_mem (hV.eigenvalues_mem_spectrum_real i)
  have he : |hV.eigenvalues i| ≤ opNorm V := by
    simpa only [Real.norm_eq_abs, opNorm, Matrix.cstar_norm_def] using h
  exact (le_abs_self _).trans he

theorem rtrace_mul_even_le {d : ℕ} (V H : Matrix (Fin d) (Fin d) ℝ)
    (hV : V.IsHermitian) (hH : H.IsHermitian) (p : ℕ) :
    rtrace (V * H^(2*p)) ≤ opNorm V * rtrace (H^(2*p)) := by
  have hleft := rtrace_mixed_pow V H hV hH 1 (2*p)
  have hright := rtrace_mixed_pow V H hV hH 0 (2*p)
  simp only [pow_one] at hleft
  simp only [pow_zero, one_mul] at hright
  rw [hleft, hright]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hp : 0 ≤ hH.eigenvalues j ^ (2*p) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have h := mul_le_mul_of_nonneg_right (eigenvalue_le_opNorm V hV i)
    (mul_nonneg hp (overlap_nonneg hV hH i j))
  simpa only [mul_assoc] using h

theorem variance_hermitian {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i, (A i).IsHermitian) : (∑ i, A i ^ 2).IsHermitian := by
  exact isSelfAdjoint_sum _ (fun i _ => (hA i).pow 2)

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/SignRecurrence.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh

theorem signSeries_hermitian {q n : ℕ} (A : Fin q → Mat n)
    (hA : ∀i,(A i).IsHermitian) (s : Fin q → Bool) : (signSeries A s).IsHermitian := by
  unfold signSeries
  apply Finset.sum_induction
  · exact fun _ _ ha hb => ha.add hb
  · exact Matrix.isHermitian_zero
  · intro i _
    exact (hA i).smul (by rfl)

theorem sign_trace_recurrence {q n : ℕ} (A : Fin q → Mat n)
    (hA : ∀i,(A i).IsHermitian) (p : ℕ) :
    signMean (fun s => rtrace (signSeries A s^(2*(p+1)))) ≤
    (2*p+1 : ℕ) * opNorm (∑ i, A i^2) * signMean (fun s => rtrace (signSeries A s^(2*p))) := by
  have hi (i : Fin q) :
      signMean (fun s => signVal (s i)*rtrace (A i*signSeries A s^(2*p+1))) ≤
      (2*p+1 : ℕ)*signMean (fun s => rtrace (A i^2*signSeries A s^(2*p))) := by
    have h := signMean_mono (fun s => sign_pair_bound A hA i s p)
    rw [signMean_add, signMean_mul, signMean_add] at h
    have hflip := signMean_flip i (fun s => signVal (s i)*rtrace (A i*signSeries A s^(2*p+1)))
    have hflip2 := signMean_flip i (fun s => rtrace (A i^2*signSeries A s^(2*p)))
    rw [hflip, hflip2] at h
    linarith
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hi i)
  rw [← signMean_sum, ← Finset.mul_sum, ← signMean_sum] at hs
  have he (s : Fin q → Bool) :
      rtrace (signSeries A s^(2*(p+1))) =
      ∑ i, signVal (s i)*rtrace (A i*signSeries A s^(2*p+1)) := by
    simpa only [series, signSeries, show 2*p+1+1 = 2*(p+1) by omega] using
      trace_series_power_step A (fun i => signVal (s i)) (2*p+1)
  simp_rw [← he, trace_variance_sum] at hs
  have hv := signMean_mono (fun s => rtrace_mul_even_le (∑ i, A i^2) (signSeries A s)
    (variance_hermitian A hA) (signSeries_hermitian A hA s) p)
  rw [signMean_mul] at hv
  exact hs.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hv (by positivity : (0:ℝ)≤(2*p+1:ℕ)))

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/SignMomentBound.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh

theorem sign_trace_product_bound {q n : ℕ} (A : Fin q → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (p : ℕ) :
    signMean (fun s => rtrace (signSeries A s^(2*p))) ≤
      (n:ℝ) * (∏ j ∈ Finset.range p, ((2*j+1:ℕ):ℝ)) * opNorm (∑ i, A i^2)^p := by
  induction p with
  | zero => simp [rtrace_one, signMean_const]
  | succ p ih =>
    have h := sign_trace_recurrence A hA p
    have hm := mul_le_mul_of_nonneg_left ih
      (show (0:ℝ) ≤ (2*p+1:ℕ)*opNorm (∑ i,A i^2) by unfold opNorm; positivity)
    apply h.trans
    apply hm.trans_eq
    rw [Finset.prod_range_succ, pow_succ]
    ring

theorem sign_norm_moment_bound {q n : ℕ} (A : Fin q → Mat n)
    (hA : ∀ i, (A i).IsHermitian) {p : ℕ} (hp : 1 ≤ p) :
    signMean (fun s => opNorm (signSeries A s)^(2*p)) ≤
      (n:ℝ) * ((2*p:ℝ)*opNorm (∑ i,A i^2))^p := by
  have h1 := signMean_mono (fun s => opNorm_pow_le_trace (signSeries_hermitian A hA s) p hp)
  have h2 := sign_trace_product_bound A hA p
  have hprod : (∏ j ∈ Finset.range p, ((2*j+1:ℕ):ℝ)) ≤ (2*p:ℝ)^p := by
    calc _ ≤ ∏ _j ∈ Finset.range p, (2*p:ℝ) := by
           apply Finset.prod_le_prod
           · intro j _; positivity
           · intro j hj
             have hj' := Finset.mem_range.mp hj
             exact_mod_cast (show 2*j+1 ≤ 2*p by omega)
         _ = _ := by simp
  apply h1.trans (h2.trans ?_)
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by positivity : (0:ℝ)≤n))
    (pow_nonneg (show 0 ≤ opNorm (∑ i,A i^2) from norm_nonneg _) p)
  simpa only [mul_pow, mul_assoc] using h

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/FinitePowerMean.lean

noncomputable section
open scoped BigOperators
namespace EffResSparsify.Sampling.ERFresh
namespace FiniteLaw
variable {ι : Type*} [Fintype ι]

theorem mean_pow_le (P : FiniteLaw ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (m : ℕ) :
    (P.mean f)^m ≤ P.mean (fun i => (f i)^m) := by
  exact Real.pow_arith_mean_le_arith_mean_pow Finset.univ P.weight f
    (fun i _ => P.nonneg i) P.total (fun i _ => hf i) m

theorem mean_le_rpow (P : FiniteLaw ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    {m : ℕ} (hm : 0 < m) : P.mean f ≤ (P.mean (fun i => (f i)^m)) ^ (1 / (m:ℝ)) := by
  have h := Real.rpow_le_rpow (pow_nonneg (P.mean_nonneg hf) m)
    (P.mean_pow_le f hf m) (by positivity : 0 ≤ (m:ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast (P.mean_nonneg hf) (ne_of_gt hm)] at h
  simpa only [one_div] using h

end FiniteLaw

def signLaw (q : ℕ) : FiniteLaw (Fin q → Bool) where
  weight _ := 1 / (2:ℝ)^q
  nonneg _ := by positivity
  total := by
    have h := signMean_const (q := q) (1:ℝ)
    simpa only [signMean, Finset.mul_sum, mul_one] using h

theorem signLaw_mean {q : ℕ} (f : (Fin q → Bool) → ℝ) :
    (signLaw q).mean f = signMean f := by
  simp only [FiniteLaw.mean, signLaw, signMean, Finset.mul_sum]

theorem signMean_le_rpow {q p : ℕ} (hp : 1 ≤ p) (f : (Fin q → Bool) → ℝ)
    (hf : ∀ s, 0 ≤ f s) :
    signMean f ≤ (signMean (fun s => (f s)^(2*p)))^(1 / (2*(p:ℝ))) := by
  have h := (signLaw q).mean_le_rpow f hf (m := 2*p) (by omega)
  simpa only [signLaw_mean, Nat.cast_mul, Nat.cast_ofNat] using h

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/SignMeanBound.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh

theorem moment_root_identity {n p : ℕ} (hp : 1 ≤ p) {v : ℝ} (hv : 0 ≤ v) :
    ((n:ℝ) * ((2*(p:ℝ))*v)^p)^(1/(2*(p:ℝ))) =
      (n:ℝ)^(1/(2*(p:ℝ))) * Real.sqrt (2*(p:ℝ)) * Real.sqrt v := by
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hx : 0 ≤ (2*(p:ℝ))*v := by positivity
  rw [Real.mul_rpow (Nat.cast_nonneg n) (pow_nonneg hx p)]
  rw [← Real.rpow_natCast ((2*(p:ℝ))*v) p, ← Real.rpow_mul hx]
  have he : (p:ℝ) * (1/(2*(p:ℝ))) = (1:ℝ)/2 := by field_simp [hp0]
  rw [he, ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity : 0 ≤ 2*(p:ℝ))]
  ring

theorem sign_mean_norm_bound {q n p : ℕ} (A : Fin q → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hp : 1 ≤ p) :
    signMean (fun s => opNorm (signSeries A s)) ≤
      (n:ℝ)^(1/(2*(p:ℝ))) * Real.sqrt (2*(p:ℝ)) *
        Real.sqrt (opNorm (∑ i, (A i)^2)) := by
  have h := signMean_le_rpow hp (fun s => opNorm (signSeries A s))
    (fun _ => norm_nonneg _)
  apply h.trans
  have hm := Real.rpow_le_rpow
    (signMean_nonneg (fun s => pow_nonneg (norm_nonneg _) (2*p)))
    (sign_norm_moment_bound A hA hp) (by positivity : 0 ≤ 1/(2*(p:ℝ)))
  have hv : 0 ≤ opNorm (∑ i, (A i)^2) := norm_nonneg _
  exact hm.trans_eq (moment_root_identity (n := n) (p := p) hp hv)

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/SelfBound.lean

namespace EffResSparsify.Sampling.ERFresh

theorem scalar_self_bound {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : δ^2 ≤ ε^2 / 36 * (1 + δ)) : δ < ε / 2 := by
  by_contra hh
  have hd : ε / 2 ≤ δ := le_of_not_gt hh
  have h1 := mul_nonneg (sub_nonneg.mpr hd) hδ
  have h2 := mul_nonneg (sub_nonneg.mpr hd) (by positivity : 0 ≤ δ + ε / 2)
  have h3 := mul_nonneg (mul_nonneg hε.le (sub_nonneg.mpr hε1)) hδ
  nlinarith [sq_pos_of_pos hε]

theorem scalar_self_bound_sqrt {δ ε b : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hbε : b^2 ≤ ε^2 / 36)
    (h : δ ≤ b * Real.sqrt (1 + δ)) : δ < ε / 2 := by
  apply scalar_self_bound hδ hε hε1
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 + δ)
  have hp := mul_self_le_mul_self hδ h
  have hm := mul_le_mul_of_nonneg_right hbε (by positivity : 0 ≤ 1 + δ)
  nlinarith

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/SampleConstants.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh

def momentOrder (n : ℕ) : ℕ := ⌈Real.log (n : ℝ)⌉₊

theorem log_ge_one {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log (n : ℝ) := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  apply (Real.le_log_iff_exp_le hn0).2
  exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hn)

theorem momentOrder_bounds {n : ℕ} (hn : 3 ≤ n) :
    1 ≤ momentOrder n ∧ Real.log (n:ℝ) ≤ momentOrder n ∧
      (momentOrder n : ℝ) ≤ 2 * Real.log (n:ℝ) := by
  have hl := log_ge_one hn
  have hc := Nat.le_ceil (Real.log (n:ℝ))
  have hu := Nat.ceil_lt_add_one (by linarith : 0 ≤ Real.log (n:ℝ))
  refine ⟨?_, hc, ?_⟩
  · have : (1:ℝ) ≤ (momentOrder n : ℝ) := hl.trans hc
    exact_mod_cast this
  · change (⌈Real.log (n:ℝ)⌉₊ : ℝ) ≤ _
    linarith

theorem dimension_root_bound {n : ℕ} (hn : 3 ≤ n) :
    (n:ℝ) ^ (1 / (2 * (momentOrder n : ℝ))) ≤ 2 := by
  have hb := momentOrder_bounds hn
  have hp : 0 < (momentOrder n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hb.1)
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  rw [Real.rpow_def_of_pos hn0]
  have he : Real.log (n:ℝ) * (1 / (2 * (momentOrder n : ℝ))) ≤ (1:ℝ)/2 := by
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (momentOrder n : ℝ))).2
    nlinarith [hb.2.1]
  have hm := Real.exp_le_exp.mpr he
  have hs : (Real.exp ((1:ℝ)/2))^2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  have hp0 := Real.exp_pos ((1:ℝ)/2)
  have h3 := Real.exp_one_lt_three
  nlinarith

def sampleSize (n : ℕ) (ε : ℝ) : ℕ := ⌈9 * (128:ℝ)^2 * n * Real.log (n:ℝ) / ε^2⌉₊

theorem sampleSize_bounds {n : ℕ} (hn : 3 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    0 < sampleSize n ε ∧
      64 * (n:ℝ) * Real.log (n:ℝ) / sampleSize n ε ≤ ε^2 / 36 := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hl := log_ge_one hn
  have hv : 0 < 9 * (128:ℝ)^2 * n * Real.log (n:ℝ) / ε^2 := by positivity
  have hc := Nat.le_ceil (9 * (128:ℝ)^2 * n * Real.log (n:ℝ) / ε^2)
  have hq : 0 < (sampleSize n ε : ℝ) := hv.trans_le hc
  refine ⟨by exact_mod_cast hq, ?_⟩
  apply (div_le_iff₀ hq).2
  have hm := (div_le_iff₀ (sq_pos_of_pos hε)).1 hc
  change 9 * (128:ℝ)^2 * n * Real.log (n:ℝ) ≤ (sampleSize n ε : ℝ) * ε^2 at hm
  nlinarith [mul_nonneg hn0.le (show 0 ≤ Real.log (n:ℝ) by linarith)]

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/CovarianceConcentration.lean

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace EffResSparsify.Sampling.ERFresh
variable {ι : Type*} [Fintype ι] {n q : ℕ}

theorem covariance_concentration (P0 : FiniteLaw ι) (A : ι → Mat n) (P : Mat n)
    (hmean : P0.vmean A = P) (hP : opNorm P ≤ 1)
    (hherm : ∀ e, (A e).IsHermitian) {r : ℝ} (hr : 0 ≤ r) (hrn : r ≤ n)
    (hA : ∀ e, (A e)^2 = r • A e) (hn : 3 ≤ n) (hq : 0 < q)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : 64*(n:ℝ)*Real.log (n:ℝ)/(q:ℝ) ≤ ε^2/36) :
    1/2 ≤ (P0.iid (Fin q)).prob {z |
      opNorm ((1/(q:ℝ)) • (∑ i, A (z i)) - P) ≤ ε} := by
  let Q := P0.iid (Fin q)
  let S : (Fin q → ι) → Mat n := fun z => ∑ i, A (z i)
  let D := Q.mean (fun z => opNorm (S z - (q:ℝ) • P))
  let K := (n:ℝ)^(1/(2*(momentOrder n:ℝ))) * Real.sqrt (2*(momentOrder n:ℝ))
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq
  have hD : 0 ≤ D := Q.mean_nonneg (fun _ => norm_nonneg _)
  have hp := momentOrder_bounds hn
  have hk0 : 0 ≤ K := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.sqrt_nonneg _)
  have hb := covariance_self_bound (q := q) P0 A P hmean hP hr hk0 hA
    (fun z => sign_mean_norm_bound (fun i => A (z i)) (fun i => hherm (z i)) hp.1)
  change D^2 ≤ 4*K^2*r*((q:ℝ)+D) at hb
  have hk : K^2 ≤ 16 * Real.log (n:ℝ) := by
    have hnroot := dimension_root_bound hn
    have hnroot0 := Real.rpow_nonneg (Nat.cast_nonneg n) (1/(2*(momentOrder n:ℝ)))
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 2*(momentOrder n:ℝ))
    have hmul := mul_le_mul_of_nonneg_right
      (show ((n:ℝ)^(1/(2*(momentOrder n:ℝ))))^2 ≤ 4 by nlinarith)
      (show 0 ≤ 2*(momentOrder n:ℝ) by positivity)
    dsimp only [K]
    nlinarith [hp.2.2]
  have hcoef : 4*K^2*r ≤ 64*(n:ℝ)*Real.log (n:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hk hr
    have h2 := mul_le_mul_of_nonneg_left hrn (show 0 ≤ 16*Real.log (n:ℝ) by linarith [log_ge_one hn])
    nlinarith
  have hb' : D^2 ≤ 64*(n:ℝ)*Real.log (n:ℝ)*((q:ℝ)+D) :=
    hb.trans (mul_le_mul_of_nonneg_right hcoef (by positivity))
  have hsmall : (D/(q:ℝ))^2 ≤ ε^2/36*(1+D/(q:ℝ)) := by
    have hm := (div_le_iff₀ hq0).1 hsize
    have hm' := mul_le_mul_of_nonneg_right hm (show 0 ≤ (q:ℝ)+D by positivity)
    have he : (D/(q:ℝ))^2 = D^2/(q:ℝ)^2 := by ring
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos hq0)).2
    have hnq : (q:ℝ) ≠ 0 := ne_of_gt hq0
    field_simp [hnq]
    nlinarith
  have hd := scalar_self_bound (div_nonneg hD hq0.le) hε hε1 hsmall
  apply Q.good_half _ (fun _ => norm_nonneg _) hε
  have he (z : Fin q → ι) :
      opNorm ((1/(q:ℝ)) • S z - P) = (1/(q:ℝ)) * opNorm (S z - (q:ℝ) • P) := by
    have hm : (1/(q:ℝ)) • S z - P = (1/(q:ℝ)) • (S z - (q:ℝ) • P) := by
      rw [smul_sub, smul_smul, one_div_mul_cancel (ne_of_gt hq0), one_smul]
    rw [hm, opNorm_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rfl
  change Q.mean (fun z => opNorm ((1/(q:ℝ)) • S z - P)) ≤ ε/2
  simp_rw [he]
  rw [Q.mean_mul]
  change (1/(q:ℝ))*D ≤ ε/2
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hd.le

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/NativeProbability.lean

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace EffResSparsify.Sampling.ERFresh
variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

theorem native_whitened_probability (G : WGraph (Fin n) E) (hn : 3 ≤ n)
    (hc : G.IsConnected) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1/2 ≤ G.sparsifyProb (sampleSize n ε) (fun s =>
      opNorm ((1/(sampleSize n ε : ℝ)) • (∑ i, sampleMatrix G (s i)) - whiteP G) ≤ ε) := by
  have hm := native_mass_bounds G hn hc
  have hm0 : 0 < nativeMass G := hm.1
  have hq := sampleSize_bounds hn hε
  have h := covariance_concentration (samplingLaw G hm0) (sampleMatrix G) (whiteP G)
    (sampleMatrix_mean G hm0) (whiteP_norm G) (sampleMatrix_hermitian G)
    hm0.le hm.2 (sampleMatrix_square G hm0) hn hq.1 hε hε1 hq.2
  rwa [samplingLaw_probability] at h

omit [DecidableEq E] in
theorem finiteLaw_event_mono (P : FiniteLaw E) {S T : Set E} (h : S ⊆ T) :
    P.prob S ≤ P.prob T := by
  classical
  apply P.mean_mono
  intro e
  by_cases hs : e ∈ S
  · simp [hs, h hs]
  · simp only [hs, if_false]
    split_ifs <;> norm_num

theorem native_probability_mono (G : WGraph (Fin n) E) (hm : 0 < nativeMass G)
    (q : ℕ) {S T : (Fin q → E) → Prop} (h : ∀ s, S s → T s) :
    G.sparsifyProb q S ≤ G.sparsifyProb q T := by
  rw [← samplingLaw_probability G hm q S, ← samplingLaw_probability G hm q T]
  exact finiteLaw_event_mono _ h

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/QuadraticTransfer.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh
open Matrix
open scoped RealInnerProductSpace

theorem quadratic_abs_le {n : ℕ} (M : Mat n) (x : Fin n → ℝ) :
    |x ⬝ᵥ (M *ᵥ x)| ≤ opNorm M * (x ⬝ᵥ x) := by
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  have h := abs_real_inner_le_norm y (Matrix.toEuclideanCLM (𝕜 := ℝ) M y)
  have hh := (Matrix.toEuclideanCLM (𝕜 := ℝ) M).le_opNorm y
  have he : ‖y‖^2 = x ⬝ᵥ x := by
    rw [← real_inner_self_eq_norm_sq]
    exact EuclideanSpace.inner_eq_star_dotProduct _ _
  rw [Matrix.inner_toEuclideanCLM] at h
  change |x ⬝ᵥ (M *ᵥ x)| ≤ _ at h
  calc _ ≤ ‖y‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M y‖ := h
       _ ≤ ‖y‖ * (opNorm M * ‖y‖) := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
       _ = opNorm M * (x ⬝ᵥ x) := by rw [← he]; ring

theorem quadratic_congruence {n : ℕ} (H S : Mat n) (hH : H.IsHermitian) (x : Fin n → ℝ) :
    x ⬝ᵥ ((H*S*H)*ᵥ x) = (H*ᵥ x) ⬝ᵥ (S*ᵥ (H*ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← symmetric_dot hH]

theorem white_quadratic_transfer {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (G : WGraph (Fin n) E) (S : Mat n) (ε : ℝ)
    (hε : opNorm (S-whiteP G) ≤ ε) (x : Fin n → ℝ) :
    (1-ε)*(x ⬝ᵥ (G.laplacian*ᵥ x)) ≤ x ⬝ᵥ ((whiteH G*S*whiteH G)*ᵥ x) ∧
      x ⬝ᵥ ((whiteH G*S*whiteH G)*ᵥ x) ≤ (1+ε)*(x ⬝ᵥ (G.laplacian*ᵥ x)) := by
  let y := whiteH G*ᵥ x
  have henergy : y ⬝ᵥ y = x ⬝ᵥ (G.laplacian*ᵥ x) := by
    dsimp [y]
    rw [symmetric_dot (whiteH_hermitian G), Matrix.mulVec_mulVec]
    rw [show whiteH G*whiteH G=G.laplacian from spectralSqrt_sq (laplacian_posSemidef G)]
  have hbase : y ⬝ᵥ (whiteP G*ᵥ y) = x ⬝ᵥ (G.laplacian*ᵥ x) := by
    rw [← quadratic_congruence _ _ (whiteH_hermitian G), white_unwhiten]
  have he := quadratic_abs_le (S-whiteP G) y
  have hy0 : 0 ≤ y ⬝ᵥ y := Finset.sum_nonneg (fun j _ => mul_self_nonneg (y j))
  have hb := he.trans (mul_le_mul_of_nonneg_right hε hy0)
  rw [Matrix.sub_mulVec, dotProduct_sub, hbase, henergy] at hb
  rw [quadratic_congruence _ _ (whiteH_hermitian G)]
  have hh := abs_le.mp hb
  constructor <;> nlinarith [hh.1,hh.2]

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/NativeSampleTransport.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh
open Matrix
variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
theorem outer_weighted (G : WGraph (Fin n) E) (e : E) :
    outer (weightedVec G e) = G.w e • outer (G.incidence e) := by
  ext i j
  change (Real.sqrt (G.w e)*G.incidence e i)*(Real.sqrt (G.w e)*G.incidence e j) =
    G.w e*(G.incidence e i*G.incidence e j)
  calc _ = (Real.sqrt (G.w e))^2*(G.incidence e i*G.incidence e j) := by ring
       _ = _ := by rw [Real.sq_sqrt (G.w_pos e).le]

theorem white_sample_congr (G : WGraph (Fin n) E) (e : E) :
    whiteH G*sampleMatrix G e*whiteH G =
      ((G.sampleProb e)⁻¹*G.w e) • outer (G.incidence e) := by
  unfold sampleMatrix
  rw [Matrix.mul_smul, Matrix.smul_mul]
  have h : whiteH G*outer (whiteVec G e)*whiteH G = outer (weightedVec G e) := by
    conv_lhs => rhs; rw [← symmetric_transpose (whiteH_hermitian G)]
    rw [outer_congr, white_lift]
  rw [h, outer_weighted, smul_smul]

theorem sampled_congruence (G : WGraph (Fin n) E) (q : ℕ) (s : Fin q → E) :
    whiteH G*((1/(q:ℝ)) • ∑ i,sampleMatrix G (s i))*whiteH G = G.sparsifiedLaplacian q s := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [white_sample_congr]
  ext a b
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, outer]
  rw [sum_eq_sampleCount_real s (fun e => (G.sampleProb e)⁻¹*G.w e*(G.incidence e a*G.incidence e b))]
  change (1/(q:ℝ))*(∑ e,(WGraph.sampleCount s e:ℝ)*
    ((G.sampleProb e)⁻¹*G.w e*(G.incidence e a*G.incidence e b))) =
    ∑ e,(G.incidenceᵀ*Matrix.diagonal (G.sparsifiedWeight q s)) a e * G.incidence e b
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, WGraph.sparsifiedWeight,
    WGraph.sparsifyS, div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem sample_good_implies (G : WGraph (Fin n) E) (q : ℕ) (s : Fin q → E) (ε : ℝ)
    (h : opNorm ((1/(q:ℝ)) • (∑ i, sampleMatrix G (s i)) - whiteP G) ≤ ε) :
    ∀ x : Fin n → ℝ,
      (1-ε)*(x ⬝ᵥ (G.laplacian*ᵥ x)) ≤ x ⬝ᵥ (G.sparsifiedLaplacian q s*ᵥ x) ∧
      x ⬝ᵥ (G.sparsifiedLaplacian q s*ᵥ x) ≤ (1+ε)*(x ⬝ᵥ (G.laplacian*ᵥ x)) := by
  intro x
  simpa only [sampled_congruence] using white_quadratic_transfer G _ ε h x

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/NativeConclusion.lean

noncomputable section
namespace EffResSparsify.Sampling.ERFresh
open Matrix

theorem native_theorem_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ (E : Type) [Fintype E] [DecidableEq E] (G : WGraph (Fin n) E), G.IsConnected →
      ∀ ε : ℝ, 1 / Real.sqrt n < ε → ε ≤ 1 →
        (1 / 2 : ℝ) ≤ G.sparsifyProb ⌈9 * C ^ 2 * n * Real.log n / ε ^ 2⌉₊
          (fun s => ∀ x : Fin n → ℝ,
            (1 - ε) * (x ⬝ᵥ (G.laplacian *ᵥ x)) ≤
                x ⬝ᵥ (G.sparsifiedLaplacian ⌈9 * C ^ 2 * n * Real.log n / ε ^ 2⌉₊ s *ᵥ x) ∧
              x ⬝ᵥ (G.sparsifiedLaplacian ⌈9 * C ^ 2 * n * Real.log n / ε ^ 2⌉₊ s *ᵥ x) ≤
                (1 + ε) * (x ⬝ᵥ (G.laplacian *ᵥ x)))  := by
  refine ⟨128, by norm_num, 3, ?_⟩
  intro n hn E _ _ G hc ε hε hε1
  have hε0 : 0 < ε := lt_of_le_of_lt (by positivity : 0 ≤ 1 / Real.sqrt (n:ℝ)) hε
  have hprob := native_whitened_probability G hn hc hε0 hε1
  have hm : 0 < nativeMass G := (native_mass_bounds G hn hc).1
  apply hprob.trans
  exact native_probability_mono G hm (sampleSize n ε)
    (fun s hs => sample_good_implies G (sampleSize n ε) s ε hs)

end EffResSparsify.Sampling.ERFresh

-- Complete module: ERProof/FinalRoot.lean

namespace EffResSparsify.Sampling

open Matrix

/-- Theorem 1, p. 2: there are an absolute constant `C > 0` and a threshold `N₀` such that for
every `n ≥ N₀`, every connected weighted graph `G` on `n` vertices and every
`1/√n < ε ≤ 1`, with `q = ⌈9 C² n log n / ε²⌉`, the graph `H = Sparsify(G, q)` satisfies
`(1 − ε) xᵀ L x ≤ xᵀ L̃ x ≤ (1 + ε) xᵀ L x` for all `x ∈ ℝⁿ` with probability at least `1/2`. -/
theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ (E : Type) [Fintype E] [DecidableEq E] (G : WGraph (Fin n) E), G.IsConnected →
      ∀ ε : ℝ, 1 / Real.sqrt n < ε → ε ≤ 1 →
        (1 / 2 : ℝ) ≤ G.sparsifyProb ⌈9 * C ^ 2 * n * Real.log n / ε ^ 2⌉₊
          (fun s => ∀ x : Fin n → ℝ,
            (1 - ε) * (x ⬝ᵥ (G.laplacian *ᵥ x)) ≤
                x ⬝ᵥ (G.sparsifiedLaplacian ⌈9 * C ^ 2 * n * Real.log n / ε ^ 2⌉₊ s *ᵥ x) ∧
              x ⬝ᵥ (G.sparsifiedLaplacian ⌈9 * C ^ 2 * n * Real.log n / ε ^ 2⌉₊ s *ᵥ x) ≤
                (1 + ε) * (x ⬝ᵥ (G.laplacian *ᵥ x))) := by
  exact ERFresh.native_theorem_1

end EffResSparsify.Sampling


open EffResSparsify.Sampling Matrix
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ (E : Type) [Fintype E] [DecidableEq E] (G : WGraph (Fin n) E), G.IsConnected →
      ∀ ε : ℝ, 1 / Real.sqrt n < ε → ε ≤ 1 →
        (1 / 2 : ℝ) ≤ G.sparsifyProb ⌈9 * C ^ 2 * n * Real.log n / ε ^ 2⌉₊
          (fun s => ∀ x : Fin n → ℝ,
            (1 - ε) * (x ⬝ᵥ (G.laplacian *ᵥ x)) ≤
                x ⬝ᵥ (G.sparsifiedLaplacian ⌈9 * C ^ 2 * n * Real.log n / ε ^ 2⌉₊ s *ᵥ x) ∧
              x ⬝ᵥ (G.sparsifiedLaplacian ⌈9 * C ^ 2 * n * Real.log n / ε ^ 2⌉₊ s *ᵥ x) ≤
                (1 + ε) * (x ⬝ᵥ (G.laplacian *ᵥ x))) := by
  exact EffResSparsify.Sampling.theorem_1
