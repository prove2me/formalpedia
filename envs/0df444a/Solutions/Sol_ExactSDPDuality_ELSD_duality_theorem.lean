-- Prove2me | solution 1 for ExactSDPDuality.ELSD.duality_theorem
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-12T05:22:13.154092+00:00
-- url     : https://prove2.me/submissions/2cd6f07b-a692-45f3-a93b-14141edaf840

-- Complete checked reconstruction of the native Ramana exact semidefinite duality theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_ExactSDPDuality_ELSD_Model
import Mathlib


-- Begin Canonical

-- End Canonical

-- Begin SymmetricSpace

open Matrix
open scoped BigOperators
namespace ExactSDPDuality.ELSD.Proof

noncomputable def symmSpace (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {A | A.IsSymm}
  zero_mem' := by simp [Matrix.IsSymm]
  add_mem' := fun hA hB => hA.add hB
  smul_mem' := fun c _ hA => hA.smul c

lemma symmSpace_mem {n : ℕ} (A : symmSpace n) : (A.val).IsSymm := A.property

noncomputable def symmProject (n : ℕ) : (Matrix (Fin n) (Fin n) ℝ) →ₗ[ℝ] symmSpace n where
  toFun A := ⟨(1/2:ℝ) • (A+Aᵀ), by
    change ((1/2:ℝ) • (A+Aᵀ)).IsSymm
    simp [Matrix.IsSymm, Matrix.transpose_add,add_comm]⟩
  map_add' A B := by ext i j; simp; ring
  map_smul' c A := by ext i j; simp; ring

lemma symmProject_self {n : ℕ} (A : symmSpace n) : symmProject n A.val = A := by
  apply Subtype.ext
  ext i j
  have h := congrFun (congrFun A.property i) j
  change (1/2:ℝ)*(A.val i j+A.val j i)=A.val i j
  change A.val j i=A.val i j at h
  rw [h]
  ring

lemma symmProject_single {n : ℕ} (i j : Fin n) :
    symmProject n (Matrix.single i j 1)=symmProject n (Matrix.single j i 1) := by
  apply Subtype.ext
  simp only [symmProject,LinearMap.coe_mk,AddHom.coe_mk,Matrix.transpose_single]
  rw [add_comm]

lemma linear_frob_representation {n : ℕ} (f : (Matrix (Fin n) (Fin n) ℝ) →ₗ[ℝ] ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) :
    f D=frob (fun i j => f (Matrix.single i j 1)) D := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single D]
  simp only [map_sum]
  unfold frob
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : Matrix.single i j (D i j)=D i j • Matrix.single i j (1:ℝ) := by simp
  rw [he,map_smul,smul_eq_mul]
  ring

lemma symmetric_functional {n : ℕ} (f : symmSpace n →ₗ[ℝ] ℝ) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, U.IsSymm ∧ ∀ A : symmSpace n,f A=frob U A.val := by
  let F := f.comp (symmProject n)
  let U : Matrix (Fin n) (Fin n) ℝ := fun i j => F (Matrix.single i j 1)
  refine ⟨U,?_,?_⟩
  · ext i j
    change f (symmProject n (Matrix.single j i 1))=f (symmProject n (Matrix.single i j 1))
    rw [symmProject_single]
  · intro A
    have h := linear_frob_representation F A.val
    simpa only [U,F,LinearMap.comp_apply,symmProject_self] using h

end ExactSDPDuality.ELSD.Proof
-- End SymmetricSpace

-- Begin MatrixBasic

namespace ExactSDPDuality.ELSD.Proof
open Matrix
variable {n m : ℕ}

theorem frob_comm (A B : Matrix (Fin n) (Fin n) ℝ) : frob A B = frob B A := by
  simp only [frob, mul_comm]

theorem frob_add_left (A B C : Matrix (Fin n) (Fin n) ℝ) :
    frob (A + B) C = frob A C + frob B C := by
  simp [frob, add_mul, Finset.sum_add_distrib]

theorem frob_smul_left (a : ℝ) (A B : Matrix (Fin n) (Fin n) ℝ) :
    frob (a • A) B = a * frob A B := by
  simp [frob, mul_assoc, Finset.mul_sum]

theorem frob_zero_left (A : Matrix (Fin n) (Fin n) ℝ) : frob 0 A = 0 := by
  simp [frob]

def qstarLinear (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (Fin m → ℝ) where
  toFun := Qstar Q
  map_add' A B := by ext i; exact frob_add_left A B (Q i)
  map_smul' a A := by ext i; exact frob_smul_left a A (Q i)

def qsharpKernel (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {X | QsharpZero Q0 Q X}
  zero_mem' := by
    constructor
    · simp [frob]
    · ext i; simp [Qstar, frob]
  add_mem' := by
    intro A B hA hB
    constructor
    · rw [frob_comm, frob_add_left, frob_comm A, frob_comm B, hA.1, hB.1, add_zero]
    · change qstarLinear Q (A + B) = 0
      rw [map_add]
      change Qstar Q A + Qstar Q B = 0
      rw [hA.2, hB.2, add_zero]
  smul_mem' := by
    intro a A hA
    constructor
    · rw [frob_comm, frob_smul_left, frob_comm A, hA.1, mul_zero]
    · change qstarLinear Q (a • A) = 0
      rw [map_smul]
      change a • Qstar Q A = 0
      rw [hA.2, smul_zero]

theorem qsharp_add {Q0 : Matrix (Fin n) (Fin n) ℝ}
    {Q : Fin m → Matrix (Fin n) (Fin n) ℝ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : QsharpZero Q0 Q A) (hB : QsharpZero Q0 Q B) : QsharpZero Q0 Q (A+B) :=
  (qsharpKernel Q0 Q).add_mem hA hB

theorem qsharp_smul {Q0 : Matrix (Fin n) (Fin n) ℝ}
    {Q : Fin m → Matrix (Fin n) (Fin n) ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (a : ℝ) (hA : QsharpZero Q0 Q A) : QsharpZero Q0 Q (a • A) :=
  (qsharpKernel Q0 Q).smul_mem a hA

end ExactSDPDuality.ELSD.Proof
-- End MatrixBasic

-- Begin PSDPairing

namespace ExactSDPDuality.ELSD.Proof
open Matrix
open scoped MatrixOrder
variable {n : ℕ}

theorem frob_eq_trace (A B : Matrix (Fin n) (Fin n) ℝ) :
    frob A B = (Aᵀ * B).trace := by
  simp only [frob,trace,diag,mul_apply,transpose_apply]
  rw [Finset.sum_comm]

theorem psd_gram (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) :
    ∃ B, A=Bᵀ*B := by
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨B,by simpa only [star_eq_conjTranspose,conjTranspose_eq_transpose_of_trivial] using hB⟩

theorem frob_gram (B D : Matrix (Fin n) (Fin n) ℝ) :
    frob (Bᵀ*B) (Dᵀ*D) = ((B*Dᵀ)ᵀ*(B*Dᵀ)).trace := by
  rw [frob_eq_trace]
  simp only [transpose_mul,transpose_transpose]
  rw [Matrix.mul_assoc,trace_mul_cycle]
  simpa only [Matrix.mul_assoc] using trace_mul_comm Bᵀ (B*(Dᵀ*D))

theorem psd_frob_nonneg {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ frob A B := by
  obtain ⟨C,rfl⟩ := psd_gram A hA
  obtain ⟨D,rfl⟩ := psd_gram B hB
  rw [frob_gram]
  exact (posSemidef_conjTranspose_mul_self (C*Dᵀ)).trace_nonneg

theorem psd_mul_eq_zero_of_frob_eq_zero {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (h : frob A B = 0) : A*B=0 := by
  obtain ⟨C,rfl⟩ := psd_gram A hA
  obtain ⟨D,rfl⟩ := psd_gram B hB
  rw [frob_gram] at h
  have hz : C*Dᵀ=0 := trace_conjTranspose_mul_self_eq_zero_iff.mp h
  calc
    (Cᵀ*C)*(Dᵀ*D) = Cᵀ*(C*Dᵀ)*D := by noncomm_ring
    _ = 0 := by rw [hz,mul_zero,zero_mul]

end ExactSDPDuality.ELSD.Proof
-- End PSDPairing

-- Begin PairingBasic

namespace ExactSDPDuality.ELSD.Proof
open Matrix
variable {n m : ℕ}

theorem frob_add_right (A B C : Matrix (Fin n) (Fin n) ℝ) :
    frob A (B+C) = frob A B + frob A C := by
  rw [frob_comm, frob_add_left, frob_comm B, frob_comm C]

theorem frob_sub_left (A B C : Matrix (Fin n) (Fin n) ℝ) :
    frob (A-B) C = frob A C - frob B C := by
  simp [frob, sub_mul, Finset.sum_sub_distrib]

theorem frob_sub_right (A B C : Matrix (Fin n) (Fin n) ℝ) :
    frob A (B-C) = frob A B - frob A C := by
  rw [frob_comm, frob_sub_left, frob_comm B, frob_comm C]

theorem frob_qhat (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (U : Matrix (Fin n) (Fin n) ℝ) :
    frob U (Qhat Q x) = Qstar Q U ⬝ᵥ x := by
  simp only [frob,Qhat,Qstar,dotProduct,Matrix.sum_apply,Matrix.smul_apply,
    smul_eq_mul,Finset.mul_sum]
  calc
    _ = ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n, U j k * (x i * Q i j k) := by
      conv_lhs =>
        arg 2
        ext j
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem frob_qaff (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) :
    frob U (Qaff Q0 Q x) = frob U Q0 - Qstar Q U ⬝ᵥ x := by
  rw [Qaff,frob_sub_right,frob_qhat]

theorem qsharp_frob_qaff {Q0 : Matrix (Fin n) (Fin n) ℝ}
    {Q : Fin m → Matrix (Fin n) (Fin n) ℝ} {U : Matrix (Fin n) (Fin n) ℝ}
    (h : QsharpZero Q0 Q U) (x : Fin m → ℝ) : frob (Qaff Q0 Q x) U = 0 := by
  rw [frob_comm,frob_qaff,frob_comm U,h.1,h.2]
  simp

end ExactSDPDuality.ELSD.Proof
-- End PairingBasic

-- Begin MatrixCompression

open Matrix
open scoped BigOperators InnerProductSpace
namespace ExactSDPDuality.ELSD.Proof

noncomputable def compressionBasis {n : ℕ} (H : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Matrix (Fin n) (Fin (Module.finrank ℝ H)) ℝ :=
  fun i j => ((stdOrthonormalBasis ℝ H) j).val i

lemma compressionBasis_orthonormal {n : ℕ} (H : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    (compressionBasis H)ᵀ * compressionBasis H=1 := by
  ext i j
  have hh := (stdOrthonormalBasis ℝ H).inner_eq_ite i j
  simpa only [compressionBasis,mul_apply,transpose_apply,Submodule.coe_inner,
    PiLp.inner_apply,RCLike.inner_apply,star_trivial,starRingEnd_apply,Matrix.one_apply,mul_comm] using hh

lemma compressionBasis_mul_mem {n : ℕ} (H : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : Fin (Module.finrank ℝ H) → ℝ) :
    WithLp.toLp 2 ((compressionBasis H)*ᵥx)∈H := by
  have hh : WithLp.toLp 2 ((compressionBasis H)*ᵥx) =
      ∑j,x j • ((stdOrthonormalBasis ℝ H) j).val := by
    ext i
    simp [compressionBasis,mulVec,dotProduct,mul_comm]
  rw [hh]
  exact H.sum_mem fun j _ => H.smul_mem _ ((stdOrthonormalBasis ℝ H) j).property

lemma compressionBasis_reconstruct {n : ℕ} (H : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x∈H) :
    (compressionBasis H)*ᵥ((compressionBasis H)ᵀ*ᵥ(WithLp.ofLp x))=WithLp.ofLp x := by
  have hh := (stdOrthonormalBasis ℝ H).sum_repr' (⟨x,hx⟩:H)
  have hv := congrArg (fun y:H => y.val) hh
  ext i
  have hi := congrFun (congrArg WithLp.ofLp hv) i
  simpa only [compressionBasis,mulVec,dotProduct,Submodule.coe_sum,Submodule.coe_smul,
    WithLp.ofLp_sum,WithLp.ofLp_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    Submodule.coe_inner,PiLp.inner_apply,RCLike.inner_apply,star_trivial,starRingEnd_apply,transpose_apply,
    mul_comm] using hi

lemma compressionBasis_project {n : ℕ} (H : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀x:Fin n→ℝ,WithLp.toLp 2 (A*ᵥx)∈H) :
    (compressionBasis H)*(compressionBasis H)ᵀ*A=A := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  simpa only [←mulVec_mulVec,WithLp.ofLp_toLp] using
    compressionBasis_reconstruct H (WithLp.toLp 2 (A*ᵥx)) (hA x)

lemma compressionBasis_supported {n : ℕ} (H : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ) (hs : A.IsSymm)
    (hA : ∀x:Fin n→ℝ,WithLp.toLp 2 (A*ᵥx)∈H) :
    compressionBasis H*((compressionBasis H)ᵀ*A*compressionBasis H)*(compressionBasis H)ᵀ=A := by
  have hleft := compressionBasis_project H A hA
  have hright : A*(compressionBasis H*(compressionBasis H)ᵀ)=A := by
    have hh := congrArg Matrix.transpose hleft
    simpa only [transpose_mul,transpose_transpose,hs.eq] using hh
  calc
    _ = (compressionBasis H*(compressionBasis H)ᵀ*A)*
      (compressionBasis H*(compressionBasis H)ᵀ) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [hleft,hright]

end ExactSDPDuality.ELSD.Proof
-- End MatrixCompression

-- Begin CommonRange

open Matrix
open scoped BigOperators InnerProductSpace
namespace ExactSDPDuality.ELSD.Proof

noncomputable def commonRange {ι : Type*} {n : ℕ}
    (A : ι → Matrix (Fin n) (Fin n) ℝ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ {v | ∃i x,v=WithLp.toLp 2 (A i*ᵥx)}

lemma commonRange_mem {ι : Type*} {n : ℕ}
    (A : ι → Matrix (Fin n) (Fin n) ℝ) (i : ι) (x : Fin n → ℝ) :
    WithLp.toLp 2 (A i*ᵥx)∈commonRange A :=
  Submodule.subset_span ⟨i,x,rfl⟩

lemma commonRange_annihilate {ι : Type*} {n : ℕ}
    (A : ι → Matrix (Fin n) (Fin n) ℝ) (hA : ∀i,(A i).IsSymm)
    (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : ∀x:Fin n→ℝ,WithLp.toLp 2 (U*ᵥx)∈commonRange A)
    (hz : ∀i,A i*U=0) : U=0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  have ho : WithLp.toLp 2 (U*ᵥx)∈(commonRange A)ᗮ := by
    apply (commonRange A).mem_orthogonal _ |>.mpr
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i,y,rfl⟩ := hv
      rw [EuclideanSpace.inner_toLp_toLp,star_trivial,dotProduct_mulVec,
        ←mulVec_transpose,(hA i).eq,mulVec_mulVec,hz,Matrix.zero_mulVec,zero_dotProduct]
    | zero => simp
    | add v w _ _ hv hw => simp only [inner_add_left,hv,hw,add_zero]
    | smul a v _ hv => simp only [inner_smul_left,hv,mul_zero]
  have hh := (commonRange A).inner_right_of_mem_orthogonal (hU x) ho
  have hzero : WithLp.toLp 2 (U*ᵥx)=0 := (inner_self_eq_zero).mp hh
  simpa using congrArg WithLp.ofLp hzero

end ExactSDPDuality.ELSD.Proof
-- End CommonRange

-- Begin CompressionAlgebra

open Matrix
namespace ExactSDPDuality.ELSD.Proof

lemma compressed_psd {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℝ)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    (Bᵀ*A*B).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using hA.conjTranspose_mul_mul_same B

lemma lifted_psd {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℝ)
    {U : Matrix (Fin r) (Fin r) ℝ} (hU : U.PosSemidef) :
    (B*U*Bᵀ).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using hU.mul_mul_conjTranspose_same B

lemma frob_lift {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℝ)
    (U : Matrix (Fin r) (Fin r) ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    frob (B*U*Bᵀ) A=frob U (Bᵀ*A*B) := by
  rw [frob_eq_trace,frob_eq_trace]
  simp only [transpose_mul,transpose_transpose]
  rw [Matrix.mul_assoc,trace_mul_comm B]
  simp only [Matrix.mul_assoc]

lemma lift_injective {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℝ) (hB : Bᵀ*B=1)
    {U : Matrix (Fin r) (Fin r) ℝ} (hU : B*U*Bᵀ=0) : U=0 := by
  have hh := congrArg (fun A => Bᵀ*A*B) hU
  simpa only [Matrix.mul_assoc,←Matrix.mul_assoc Bᵀ B,hB,one_mul,mul_one,Matrix.mul_zero,Matrix.zero_mul] using hh

end ExactSDPDuality.ELSD.Proof
-- End CompressionAlgebra

-- Begin SymmetricCompression

open Matrix
namespace ExactSDPDuality.ELSD.Proof

noncomputable def symmCompress {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℝ) :
    symmSpace n →ₗ[ℝ] symmSpace r where
  toFun A := ⟨Bᵀ*A.val*B,by
    change (Bᵀ*A.val*B).IsSymm
    rw [Matrix.IsSymm,transpose_mul,transpose_mul,transpose_transpose,(symmSpace_mem A).eq]
    simp only [Matrix.mul_assoc]⟩
  map_add' A C := by apply Subtype.ext; simp only [Submodule.coe_add,Matrix.mul_add,Matrix.add_mul]
  map_smul' c A := by apply Subtype.ext; simp only [Submodule.coe_smul,RingHom.id_apply,Matrix.mul_smul,Matrix.smul_mul]

lemma symmCompress_psd {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℝ)
    (A : symmSpace n) (hA : A.val.PosSemidef) : (symmCompress B A).val.PosSemidef :=
  compressed_psd B hA

lemma symmCompress_psd_iff {n : ℕ} (H : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (A : symmSpace n) (hA : ∀x:Fin n→ℝ,WithLp.toLp 2 (A.val*ᵥx)∈H) :
    (symmCompress (compressionBasis H) A).val.PosSemidef ↔ A.val.PosSemidef := by
  constructor
  · intro hh
    have hp := lifted_psd (compressionBasis H) hh
    change (compressionBasis H*((compressionBasis H)ᵀ*A.val*compressionBasis H)*(compressionBasis H)ᵀ).PosSemidef at hp
    rwa [compressionBasis_supported H A.val (symmSpace_mem A) hA] at hp
  · exact symmCompress_psd _ A

end ExactSDPDuality.ELSD.Proof
-- End SymmetricCompression

-- Begin QuadraticBounds

open Matrix
open scoped BigOperators MatrixOrder
namespace ExactSDPDuality.ELSD.Proof

noncomputable def vecSq {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i,x i^2
noncomputable def matSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ∑ i,∑ j,A i j^2

lemma vecSq_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ vecSq x :=
  Finset.sum_nonneg (fun _i _ => sq_nonneg _)
lemma matSq_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ matSq A :=
  Finset.sum_nonneg (fun _i _ => Finset.sum_nonneg (fun _j _ => sq_nonneg _))

lemma vecSq_mulVec_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    vecSq (A*ᵥx) ≤ matSq A*vecSq x := by
  unfold vecSq matSq
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) x

lemma quadratic_gram {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((Bᵀ*B)*ᵥx)=vecSq (B*ᵥx) := by
  rw [← Matrix.mulVec_mulVec,dotProduct_mulVec,Matrix.vecMul_transpose]
  simp [dotProduct,vecSq,pow_two]

lemma quadratic_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((A-B)*ᵥx)=x ⬝ᵥ (A*ᵥx)-x ⬝ᵥ (B*ᵥx) := by
  rw [Matrix.sub_mulVec,dotProduct_sub]

lemma quadratic_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (c : ℝ) :
    x ⬝ᵥ ((c•A)*ᵥx)=c*(x ⬝ᵥ (A*ᵥx)) := by
  simp [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

lemma gram_domination {n : ℕ} (B V : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (((Bᵀ*B)*V)*((Bᵀ*B)*V)ᵀ)*ᵥx ≤
      matSq ((B*V)ᵀ)*(x ⬝ᵥ ((Bᵀ*B)*ᵥx)) := by
  have he : ((Bᵀ*B)*V)ᵀ=(B*V)ᵀ*B := by simp [Matrix.transpose_mul,Matrix.mul_assoc]
  have h := vecSq_mulVec_le ((B*V)ᵀ) (B*ᵥx)
  have heq : x ⬝ᵥ ((((Bᵀ*B)*V)*((Bᵀ*B)*V)ᵀ)*ᵥx)=vecSq (((Bᵀ*B)*V)ᵀ*ᵥx) := by
    simpa only [Matrix.transpose_transpose] using quadratic_gram (((Bᵀ*B)*V)ᵀ) x
  rw [heq,he,← Matrix.mulVec_mulVec,quadratic_gram]
  exact h

lemma exists_small_domination {n : ℕ} (U V : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.PosSemidef) : ∃ e : ℝ,0<e ∧ (U-(e•(U*V))*(e•(U*V))ᵀ).PosSemidef := by
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hU.nonneg
  have he : U=Bᵀ*B := by simpa only [star_eq_conjTranspose,conjTranspose_eq_transpose_of_trivial] using hB
  let c := matSq ((B*V)ᵀ)
  have hc : 0≤c := matSq_nonneg _
  let e := 1/(1+c)
  have hep : 0<e := one_div_pos.mpr (by linarith)
  have hec : e^2*c≤1 := by
    dsimp [e]
    rw [div_pow,one_pow,div_mul_eq_mul_div,one_mul]
    apply (div_le_iff₀ (by positivity : 0<(1+c)^2)).mpr
    nlinarith [sq_nonneg c]
  refine ⟨e,hep,Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_⟩
  · exact hU.isHermitian.sub (Matrix.isHermitian_mul_conjTranspose_self (e•(U*V)))
  · intro x
    simp only [star_trivial]
    have hq : 0≤x ⬝ᵥ (U*ᵥx) := by simpa only [star_trivial] using hU.dotProduct_mulVec_nonneg x
    have hg : x ⬝ᵥ (((U*V)*(U*V)ᵀ)*ᵥx)≤c*(x ⬝ᵥ (U*ᵥx)) := by
      rw [he]
      exact gram_domination B V x
    have hm : (e•(U*V))*(e•(U*V))ᵀ=e^2•((U*V)*(U*V)ᵀ) := by
      simp [Matrix.transpose_smul,smul_smul,pow_two]
    rw [hm,quadratic_sub,quadratic_smul]
    have hmul := mul_le_mul_of_nonneg_left hg (sq_nonneg e)
    nlinarith [mul_le_mul_of_nonneg_right hec hq]

end ExactSDPDuality.ELSD.Proof
-- End QuadraticBounds

-- Begin QuadraticContinuity

open Matrix
open scoped BigOperators
namespace ExactSDPDuality.ELSD.Proof

lemma coord_sq_le_vecSq {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : x i^2≤vecSq x := by
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

lemma abs_coord_mul_le_vecSq {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) :
    |x i*x j|≤vecSq x := by
  rw [abs_mul]
  have hi := coord_sq_le_vecSq x i
  have hj := coord_sq_le_vecSq x j
  have hh := sq_nonneg (|x i|-|x j|)
  rw [sub_sq,sq_abs,sq_abs] at hh
  nlinarith

lemma quadratic_abs_le_entries {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    {r : ℝ} (hr : 0≤r) (hD : ∀i j,|D i j|≤r) :
    |x ⬝ᵥ (D*ᵥx)|≤(n:ℝ)^2*r*vecSq x := by
  have he : x ⬝ᵥ (D*ᵥx)=∑i,∑j,D i j*(x i*x j) := by
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  calc
    _ ≤ ∑i,|∑j,D i j*(x i*x j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑i,∑j,|D i j*(x i*x j)| := Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑_i : Fin n,∑_j : Fin n,r*vecSq x := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hD i j) (abs_coord_mul_le_vecSq x i j) (abs_nonneg _) hr
    _ = _ := by simp [pow_two]; ring

noncomputable def strictPSD {n : ℕ} (A : symmSpace n) : Prop :=
  ∃ e : ℝ,0<e ∧ ∀x,e*vecSq x≤x ⬝ᵥ (A.val*ᵥx)

lemma strictPSD_psd {n : ℕ} {A : symmSpace n} (hA : strictPSD A) : A.val.PosSemidef := by
  obtain ⟨e,he,h⟩ := hA
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (by simpa only [Matrix.IsHermitian,Matrix.IsSymm,conjTranspose_eq_transpose_of_trivial] using (symmSpace_mem A))
  intro x
  simpa only [star_trivial] using (mul_nonneg he.le (vecSq_nonneg x)).trans (h x)

lemma strictPSD_one (n : ℕ) : strictPSD (⟨1,by change (1:Matrix (Fin n) (Fin n) ℝ).IsSymm; simp⟩ : symmSpace n) := by
  refine ⟨1,zero_lt_one,?_⟩
  intro x
  simp [vecSq,dotProduct,pow_two]

lemma isOpen_strictPSD (n : ℕ) : IsOpen {A : symmSpace n | strictPSD A} := by
  apply isOpen_iff_mem_nhds.mpr
  intro A hA
  obtain ⟨e,he,hA⟩ := hA
  let r := e/(2*((n:ℝ)+1)^2)
  have hr : 0<r := div_pos he (by positivity)
  have hsmall : (n:ℝ)^2*r≤e/2 := by
    dsimp [r]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<2*((n:ℝ)+1)^2)).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hop : IsOpen {B : symmSpace n | ∀i j,|B.val i j-A.val i j|<r} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_lt _ continuous_const
    have hv : Continuous (fun B : symmSpace n => B.val) := continuous_subtype_val
    have hi : Continuous (fun B : symmSpace n => B.val i) := (continuous_apply i).comp hv
    have hij : Continuous (fun B : symmSpace n => B.val i j) := (continuous_apply j).comp hi
    exact (hij.sub continuous_const).abs
  have hmem : A∈{B : symmSpace n | ∀i j,|B.val i j-A.val i j|<r} := by simpa using (fun (_i _j : Fin n) => hr)
  apply Filter.mem_of_superset (hop.mem_nhds hmem)
  intro B hB
  refine ⟨e/2,by positivity,?_⟩
  intro x
  have hd := quadratic_abs_le_entries (B.val-A.val) x hr.le (fun i j => (hB i j).le)
  rw [quadratic_sub] at hd
  have hz := vecSq_nonneg x
  have hm := mul_le_mul_of_nonneg_right hsmall hz
  have hb := (neg_le_abs (x ⬝ᵥ (B.val*ᵥx)-x ⬝ᵥ (A.val*ᵥx))).trans hd
  nlinarith [hA x]

end ExactSDPDuality.ELSD.Proof
-- End QuadraticContinuity

-- Begin StrictCone

open Matrix Filter
open scoped BigOperators Topology
namespace ExactSDPDuality.ELSD.Proof

noncomputable def symmOne (n : ℕ) : symmSpace n := ⟨1,by change (1 : Matrix (Fin n) (Fin n) ℝ).IsSymm; simp⟩

lemma strictPSD_symmOne (n : ℕ) : strictPSD (symmOne n) := strictPSD_one n

lemma quadratic_one {n : ℕ} (x : Fin n → ℝ) : x ⬝ᵥ ((1:Matrix (Fin n) (Fin n) ℝ)*ᵥx)=vecSq x := by
  simp [vecSq,dotProduct,pow_two]

lemma quadratic_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((A+B)*ᵥx)=x ⬝ᵥ (A*ᵥx)+x ⬝ᵥ (B*ᵥx) := by
  rw [Matrix.add_mulVec,dotProduct_add]

lemma strictPSD_smul {n : ℕ} {A : symmSpace n} (hA : strictPSD A) {c : ℝ} (hc : 0<c) :
    strictPSD (c•A) := by
  obtain ⟨e,he,hA⟩ := hA
  refine ⟨c*e,mul_pos hc he,?_⟩
  intro x
  change (c*e)*vecSq x≤x ⬝ᵥ ((c•A.val)*ᵥx)
  rw [quadratic_smul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hA x) hc.le

lemma convex_strictPSD (n : ℕ) : Convex ℝ {A : symmSpace n | strictPSD A} := by
  intro A hA B hB a b ha hb hab
  obtain ⟨e,he,hA⟩ := hA
  obtain ⟨f,hf,hB⟩ := hB
  have hp : 0<a*e+b*f := by
    by_cases haz : a=0
    · subst a
      simp only [zero_add] at hab
      rw [zero_mul,zero_add,hab,one_mul]
      exact hf
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm haz)) he) (mul_nonneg hb hf.le)
  refine ⟨a*e+b*f,hp,?_⟩
  intro x
  change _≤x ⬝ᵥ ((a•A.val+b•B.val)*ᵥx)
  rw [quadratic_add,quadratic_smul,quadratic_smul]
  have h1 := mul_le_mul_of_nonneg_left (hA x) ha
  have h2 := mul_le_mul_of_nonneg_left (hB x) hb
  nlinarith

lemma strictPSD_add_eps {n : ℕ} (A : symmSpace n) (hA : A.val.PosSemidef)
    (e : ℝ) (he : 0<e) : strictPSD (A+e•symmOne n) := by
  refine ⟨e,he,?_⟩
  intro x
  change _≤x ⬝ᵥ ((A.val+e•(1:Matrix (Fin n) (Fin n) ℝ))*ᵥx)
  rw [quadratic_add,quadratic_smul,quadratic_one]
  have h := hA.dotProduct_mulVec_nonneg x
  simpa only [star_trivial] using le_add_of_nonneg_left h

lemma psd_functional_nonneg {n : ℕ} (f : symmSpace n →ₗ[ℝ] ℝ)
    (hf : ∀ A,strictPSD A → 0≤f A) (A : symmSpace n) (hA : A.val.PosSemidef) : 0≤f A := by
  have ht : Tendsto (fun k : ℕ => (1:ℝ)/((k:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have htA : Tendsto (fun k : ℕ => A+((1:ℝ)/((k:ℝ)+1))•symmOne n) atTop (𝓝 A) := by
    simpa using tendsto_const_nhds.add (ht.smul_const (symmOne n))
  exact ge_of_tendsto ((f.continuous_of_finiteDimensional.tendsto A).comp htA)
    (Eventually.of_forall fun k => hf _ (strictPSD_add_eps A hA _ (by positivity)))

end ExactSDPDuality.ELSD.Proof
-- End StrictCone

-- Begin OpenConeSlater

open Set Filter
open scoped Topology Pointwise
namespace ExactSDPDuality.ELSD.Proof

lemma affine_all_lt_zero {a b c : ℝ} (h : ∀t:ℝ,t*a+b<c) : a=0 := by
  by_contra ha
  have hh := h ((c-b+1)/a)
  have he : ((c-b+1)/a)*a=c-b+1 := div_mul_cancel₀ _ ha
  linarith

lemma positive_scaling_nonpos {a b c : ℝ} (h : ∀t:ℝ,0<t → t*a+b<c) : a≤0 := by
  by_contra! ha
  have ht : 0<(|c-b|+1)/a := div_pos (by positivity) ha
  have hh := h _ ht
  have he := div_mul_cancel₀ (|c-b|+1) ha.ne'
  have hab := le_abs_self (c-b)
  linarith

lemma positive_scaling_limit {a b : ℝ} (h : ∀t:ℝ,0<t → t*a<b) : 0≤b := by
  have ht : Tendsto (fun k:ℕ => (1:ℝ)/((k:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hh := le_of_tendsto (ht.mul_const a) (Eventually.of_forall fun k => (h _ (by positivity)).le)
  simpa using hh

lemma functional_pos_on_open {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set F} (hK : IsOpen K) (f : F →L[ℝ] ℝ) (hf : ∀P∈K,0≤f P)
    (hne : f≠0) {P : F} (hP : P∈K) : 0<f P := by
  have hop : IsOpen (f '' K) := f.isOpenMap_of_ne_zero hne K hK
  have hsub : f '' K⊆Ici (0:ℝ) := by rintro y ⟨x,hx,rfl⟩; exact hf x hx
  have hi := interior_maximal hsub hop (mem_image_of_mem f hP)
  simpa only [interior_Ici,mem_Ioi] using hi

lemma open_cone_slater {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set F) (hK : Convex ℝ K) (ho : IsOpen K) (hne : K.Nonempty)
    (hscale : ∀P∈K,∀t:ℝ,0<t → t•P∈K)
    (L : E →ₗ[ℝ] F) (c : E →ₗ[ℝ] ℝ) (B : F)
    (hslater : ∃x:E,B-L x∈K)
    (hbound : ∀x:E,B-L x∈K → c x≤1) :
    ∃f : F →L[ℝ] ℝ,(∀P∈K,0≤f P) ∧ (∀x,f (L x)=c x) ∧ f B≤1 := by
  let J : E →ₗ[ℝ] F×ℝ := L.prod c
  let C : Set (F×ℝ) := (LinearMap.range J : Set (F×ℝ))+(K×ˢIio (0:ℝ))
  have hc : Convex ℝ C := (LinearMap.range J).convex.add (hK.prod (convex_Iio 0))
  have hop : IsOpen C := (ho.prod isOpen_Iio).add_left
  have hnot : (B,(1:ℝ))∉C := by
    rintro ⟨z,⟨x,rfl⟩,⟨P,r⟩,⟨hP,hr⟩,he⟩
    have he1 : L x+P=B := congrArg Prod.fst he
    have he2 : c x+r=1 := congrArg Prod.snd he
    have hx : B-L x=P := by rw [←he1]; abel
    have hh := hbound x (hx ▸ hP)
    change r<0 at hr
    linarith
  obtain ⟨ell,hell⟩ := geometric_hahn_banach_open_point hc hop hnot
  let f : F →L[ℝ] ℝ := -(ell.comp (ContinuousLinearMap.inl ℝ F ℝ))
  let beta : ℝ := ell (0,1)
  have heval (P:F) (r:ℝ) : ell (P,r)= -f P+beta*r := by
    have he : (P,r)=(P,(0:ℝ))+r•((0:F),(1:ℝ)) := by simp
    rw [he,map_add,map_smul]
    simp [f,beta,mul_comm]
  have htest (x:E) (P:F) (hP:P∈K) (r:ℝ) (hr:r<0) :
      -f (L x+P)+beta*(c x+r)< -f B+beta := by
    have hh := hell (J x+(P,r)) ⟨J x,⟨x,rfl⟩,(P,r),⟨hP,hr⟩,rfl⟩
    simpa only [J,LinearMap.prod_apply,Function.prod_apply,Prod.mk_add_mk,heval,mul_one] using hh
  obtain ⟨P0,hP0⟩ := hne
  have hbeta : 0≤beta := by
    have h := positive_scaling_nonpos (a := -beta) (b := -f P0) (c := -f B+beta) (by
      intro t ht
      have hh := htest 0 P0 hP0 (-t) (by linarith)
      simp only [map_zero,zero_add] at hh
      nlinarith)
    linarith
  have hf : ∀P∈K,0≤f P := by
    intro P hP
    have h := positive_scaling_nonpos (a := -f P) (b := -beta) (c := -f B+beta) (by
      intro t ht
      have hh := htest 0 (t•P) (hscale P hP t ht) (-1) (by norm_num)
      simpa only [map_zero,zero_add,map_smul,smul_eq_mul,mul_neg,mul_one,neg_mul,add_neg_cancel_right] using hh)
    linarith
  have hdual (x:E) : f (L x)=beta*c x := by
    have h := affine_all_lt_zero (a := -f (L x)+beta*c x) (b := -f P0-beta) (c := -f B+beta) (by
      intro t
      have hh := htest (t•x) P0 hP0 (-1) (by norm_num)
      simp only [map_smul,map_add,smul_eq_mul] at hh
      nlinarith)
    linarith
  have hcost : f B≤beta := by
    have h := positive_scaling_limit (a := -f P0-beta) (b := -f B+beta) (by
      intro t ht
      have hh := htest 0 (t•P0) (hscale P0 hP0 t ht) (-t) (by linarith)
      simp only [map_zero,zero_add,map_smul,smul_eq_mul] at hh
      nlinarith)
    linarith
  have hbp : 0<beta := by
    by_contra! hz
    have hb : beta=0 := le_antisymm hz hbeta
    obtain ⟨x,hx⟩ := hslater
    by_cases hfn : f=0
    · have hh := htest 0 P0 hP0 (-1) (by norm_num)
      simp [hfn,hb] at hh
    · have hh := functional_pos_on_open ho f hf hfn hx
      rw [map_sub,hdual,hb,zero_mul,sub_zero] at hh
      linarith
  refine ⟨(1/beta)•f,?_,?_,?_⟩
  · intro P hP
    change 0≤(1/beta)*f P
    exact mul_nonneg (by positivity) (hf P hP)
  · intro x
    change (1/beta)*f (L x)=c x
    rw [hdual]
    field_simp
  · change (1/beta)*f B≤1
    rw [one_div_mul_eq_div]
    exact (div_le_one hbp).mpr hcost

end ExactSDPDuality.ELSD.Proof
-- End OpenConeSlater

-- Begin PSDSlater

open Matrix
open scoped BigOperators Matrix.Norms.Frobenius
namespace ExactSDPDuality.ELSD.Proof

lemma frob_rankOne {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    frob U (vecMulVec x x)=x ⬝ᵥ (U*ᵥx) := by
  simp only [frob,vecMulVec_apply,dotProduct,mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma positive_symmetric_functional {n : ℕ} (f : symmSpace n →ₗ[ℝ] ℝ)
    (hf : ∀A : symmSpace n,strictPSD A → 0≤f A) :
    ∃U : Matrix (Fin n) (Fin n) ℝ,U.PosSemidef ∧ ∀A:symmSpace n,f A=frob U A.val := by
  obtain ⟨U,hU,he⟩ := symmetric_functional f
  refine ⟨U,?_,he⟩
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · simpa only [Matrix.IsHermitian,Matrix.IsSymm,conjTranspose_eq_transpose_of_trivial] using hU
  · intro x
    let A : symmSpace n := ⟨vecMulVec x x,by change (vecMulVec x x).IsSymm; simp [Matrix.IsSymm]⟩
    have hp : A.val.PosSemidef := by
      simpa only [star_trivial] using posSemidef_vecMulVec_self_star x
    have hh := psd_functional_nonneg f hf A hp
    rw [he] at hh
    simpa only [A,frob_rankOne,star_trivial] using hh

lemma psd_slater {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (L : E →ₗ[ℝ] symmSpace n) (c : E →ₗ[ℝ] ℝ) (B : symmSpace n)
    (hslater : ∃x:E,strictPSD (B-L x))
    (hbound : ∀x:E,(B-L x).val.PosSemidef → c x≤1) :
    ∃U : Matrix (Fin n) (Fin n) ℝ,U.PosSemidef ∧
      (∀x,frob U (L x).val=c x) ∧ frob U B.val≤1 := by
  have hs : ∀A∈{A:symmSpace n|strictPSD A},∀t:ℝ,0<t → t•A∈{A:symmSpace n|strictPSD A} := by
    intro A hA t ht
    exact strictPSD_smul hA ht
  have hb : ∀x:E,B-L x∈{A:symmSpace n|strictPSD A} → c x≤1 := by
    intro x hx
    exact hbound x (strictPSD_psd hx)
  have hh : ∃f : symmSpace n →L[ℝ] ℝ,
      (∀P,strictPSD P → 0≤f P) ∧ (∀x,f (L x)=c x) ∧ f B≤1 := by
    apply open_cone_slater {A:symmSpace n|strictPSD A}
    · exact convex_strictPSD n
    · exact isOpen_strictPSD n
    · exact ⟨symmOne n,strictPSD_symmOne n⟩
    · exact hs
    · exact hslater
    · exact hb
  obtain ⟨f,hf,he,hc⟩ := hh
  obtain ⟨U,hU,hrep⟩ := positive_symmetric_functional f.toLinearMap hf
  refine ⟨U,hU,?_,?_⟩
  · intro x
    rw [←hrep]
    exact he x
  · rw [←hrep]
    exact hc

end ExactSDPDuality.ELSD.Proof
-- End PSDSlater

-- Begin OpenConeAlternative

open Set
open scoped Pointwise
namespace ExactSDPDuality.ELSD.Proof

lemma open_cone_alternative {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set F) (hK : Convex ℝ K) (ho : IsOpen K) (hne : K.Nonempty)
    (hscale : ∀P∈K,∀t:ℝ,0<t → t•P∈K)
    (L : E →ₗ[ℝ] F) (B : F)
    (hnot : ¬∃x:E,B-L x∈K) :
    ∃f : F →L[ℝ] ℝ,f≠0 ∧ (∀P∈K,0≤f P) ∧ (∀x,f (L x)=0) ∧ f B≤0 := by
  let C : Set F := (LinearMap.range L : Set F)+K
  have hc : Convex ℝ C := (LinearMap.range L).convex.add hK
  have hop : IsOpen C := ho.add_left
  have hb : B∉C := by
    rintro ⟨_,⟨x,rfl⟩,P,hP,he⟩
    apply hnot
    refine ⟨x,?_⟩
    have hh : B-L x=P := sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using he.symm)
    rwa [hh]
  obtain ⟨ell,hell⟩ := geometric_hahn_banach_open_point hc hop hb
  let f : F →L[ℝ] ℝ := -ell
  have htest (x:E) (P:F) (hP:P∈K) : f B<f (L x+P) := by
    have hh := hell (L x+P) ⟨L x,⟨x,rfl⟩,P,hP,rfl⟩
    change -ell B < -ell (L x+P)
    linarith
  obtain ⟨P0,hP0⟩ := hne
  have hfn : f≠0 := by
    intro he
    have hh := htest 0 P0 hP0
    simp [he] at hh
  have hf : ∀P∈K,0≤f P := by
    intro P hP
    have hh := positive_scaling_nonpos (a := -f P) (b := 0) (c := -f B) (by
      intro t ht
      have hh := htest 0 (t•P) (hscale P hP t ht)
      simp only [map_zero,zero_add,map_smul,smul_eq_mul] at hh
      nlinarith)
    linarith
  have hv (x:E) : f (L x)=0 := by
    have hh := affine_all_lt_zero (a := -f (L x)) (b := -f P0) (c := -f B) (by
      intro t
      have hh := htest (t•x) P0 hP0
      simp only [map_smul,map_add,smul_eq_mul] at hh
      nlinarith)
    linarith
  have hcost : f B≤0 := by
    have hh := positive_scaling_limit (a := -f P0) (b := -f B) (by
      intro t ht
      have hh := htest 0 (t•P0) (hscale P0 hP0 t ht)
      simp only [map_zero,zero_add,map_smul,smul_eq_mul] at hh
      nlinarith)
    linarith
  exact ⟨f,hfn,hf,hv,hcost⟩

end ExactSDPDuality.ELSD.Proof
-- End OpenConeAlternative

-- Begin PSDAlternative

open Matrix
open scoped Matrix.Norms.Frobenius
namespace ExactSDPDuality.ELSD.Proof

lemma psd_alternative {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (L : E →ₗ[ℝ] symmSpace n) (B : symmSpace n) (hB : B.val.PosSemidef)
    (hnot : ¬∃x:E,strictPSD (B-L x)) :
    ∃U : Matrix (Fin n) (Fin n) ℝ,U.PosSemidef ∧ U≠0 ∧
      (∀x,frob U (L x).val=0) ∧ frob U B.val=0 := by
  have hs : ∀A∈{A:symmSpace n|strictPSD A},∀t:ℝ,0<t → t•A∈{A:symmSpace n|strictPSD A} := by
    intro A hA t ht
    exact strictPSD_smul hA ht
  obtain ⟨f,hfn,hf,he,hc⟩ := open_cone_alternative {A:symmSpace n|strictPSD A}
    (convex_strictPSD n) (isOpen_strictPSD n) ⟨symmOne n,strictPSD_symmOne n⟩
    hs L B hnot
  obtain ⟨U,hU,hrep⟩ := positive_symmetric_functional f.toLinearMap hf
  refine ⟨U,hU,?_,?_,?_⟩
  · intro hzero
    apply hfn
    ext A
    have hh := hrep A
    simpa [hzero,frob] using hh
  · intro x
    rw [←hrep]
    exact he x
  · apply le_antisymm
    · rwa [←hrep]
    · exact psd_frob_nonneg hU hB

end ExactSDPDuality.ELSD.Proof
-- End PSDAlternative

-- Begin SupportedSlater

open Matrix
namespace ExactSDPDuality.ELSD.Proof

noncomputable def familyMatrices {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (B : symmSpace n) (L : E →ₗ[ℝ] symmSpace n) : Option E → Matrix (Fin n) (Fin n) ℝ
  | none => B.val
  | some x => (L x).val

noncomputable def familyRange {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (B : symmSpace n) (L : E →ₗ[ℝ] symmSpace n) := commonRange (familyMatrices B L)

lemma familyRange_affine {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (B : symmSpace n) (L : E →ₗ[ℝ] symmSpace n) (x:E) (v:Fin n→ℝ) :
    WithLp.toLp 2 ((B-L x).val*ᵥv)∈familyRange B L := by
  have hB := commonRange_mem (familyMatrices B L) none v
  have hL := commonRange_mem (familyMatrices B L) (some x) v
  have hh := (familyRange B L).sub_mem hB hL
  simpa only [Submodule.coe_sub,sub_mulVec,WithLp.toLp_sub,familyMatrices] using hh

lemma compressed_strict_feasible {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (B : symmSpace n) (L : E →ₗ[ℝ] symmSpace n) (hB:B.val.PosSemidef)
    (hstable : ∀U:Matrix (Fin n) (Fin n) ℝ,U.PosSemidef → frob U B.val=0 →
      (∀x:E,frob U (L x).val=0) → ∀x:E,(L x).val*U=0) :
    ∃x:E,strictPSD (symmCompress (compressionBasis (familyRange B L)) (B-L x)) := by
  let H := familyRange B L
  let R := compressionBasis H
  let C := symmCompress R
  by_contra hn
  have hn' : ¬∃x:E,strictPSD (C B-(C.comp L) x) := by
    simpa only [LinearMap.comp_apply,←map_sub] using hn
  obtain ⟨U,hU,hUn,horth,hzero⟩ := psd_alternative (C.comp L) (C B)
    (symmCompress_psd R B hB) hn'
  let V := R*U*Rᵀ
  have hV : V.PosSemidef := lifted_psd R hU
  have hVzero : frob V B.val=0 := by
    change frob (R*U*Rᵀ) B.val=0
    rw [frob_lift]
    exact hzero
  have hVorth : ∀x:E,frob V (L x).val=0 := by
    intro x
    change frob (R*U*Rᵀ) (L x).val=0
    rw [frob_lift]
    exact horth x
  have hbV : B.val*V=0 :=
    psd_mul_eq_zero_of_frob_eq_zero hB hV (by rwa [frob_comm])
  have hlV := hstable V hV hVzero hVorth
  have hv0 : V=0 := by
    apply commonRange_annihilate (familyMatrices B L)
    · intro o
      cases o with
      | none => exact symmSpace_mem B
      | some x => exact symmSpace_mem (L x)
    · intro x
      change WithLp.toLp 2 ((R*U*Rᵀ)*ᵥx)∈H
      simpa only [←mulVec_mulVec] using compressionBasis_mul_mem H (U*ᵥ(Rᵀ*ᵥx))
    · intro o
      cases o with
      | none => exact hbV
      | some x => exact hlV x
  exact hUn (lift_injective R (compressionBasis_orthonormal H) hv0)

lemma supported_polar_certificate {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (B : symmSpace n) (L : E →ₗ[ℝ] symmSpace n) (hB:B.val.PosSemidef)
    (hstable : ∀U:Matrix (Fin n) (Fin n) ℝ,U.PosSemidef → frob U B.val=0 →
      (∀x:E,frob U (L x).val=0) → ∀x:E,(L x).val*U=0)
    (c : E →ₗ[ℝ] ℝ) (hbound : ∀x:E,(B-L x).val.PosSemidef → c x≤1) :
    ∃U:Matrix (Fin n) (Fin n) ℝ,U.PosSemidef ∧
      (∀x:E,frob U (L x).val=c x) ∧ frob U B.val≤1 := by
  let H := familyRange B L
  let R := compressionBasis H
  let C := symmCompress R
  have hs : ∃x:E,strictPSD (C B-(C.comp L) x) := by
    simpa only [LinearMap.comp_apply,←map_sub] using compressed_strict_feasible B L hB hstable
  have hb : ∀x:E,(C B-(C.comp L) x).val.PosSemidef → c x≤1 := by
    intro x hx
    apply hbound x
    apply (symmCompress_psd_iff H (B-L x) (familyRange_affine B L x)).mp
    simpa only [LinearMap.comp_apply,←map_sub] using hx
  obtain ⟨U,hU,he,hc⟩ := psd_slater (C.comp L) c (C B) hs hb
  refine ⟨R*U*Rᵀ,lifted_psd R hU,?_,?_⟩
  · intro x
    rw [frob_lift]
    exact he x
  · rw [frob_lift]
    exact hc

end ExactSDPDuality.ELSD.Proof
-- End SupportedSlater

-- Begin CoordinateFunctional

namespace ExactSDPDuality.ELSD.Proof
open Matrix
variable {m : ℕ}

theorem linear_eq_dot (f : (Fin m → ℝ) →ₗ[ℝ] ℝ) (x : Fin m → ℝ) :
    f x = (fun i => f (Pi.single i 1)) ⬝ᵥ x := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : Pi.single i (x i) = x i • (Pi.single i 1 : Fin m → ℝ) := by
    ext j
    by_cases h : j=i <;> simp [h]
  rw [he,map_smul]
  simp [mul_comm]

theorem continuousLinear_eq_dot (f : (Fin m → ℝ) →L[ℝ] ℝ) (x : Fin m → ℝ) :
    f x = (fun i => f (Pi.single i 1)) ⬝ᵥ x := linear_eq_dot f.toLinearMap x

end ExactSDPDuality.ELSD.Proof
-- End CoordinateFunctional

-- Begin DotPerpendicular

open Matrix
namespace ExactSDPDuality.ELSD.Proof

def dotPerp {m : ℕ} (S : Submodule ℝ (Fin m → ℝ)) : Submodule ℝ (Fin m → ℝ) where
  carrier := {x | ∀s∈S,x ⬝ᵥ s=0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy s hs; rw [add_dotProduct,hx s hs,hy s hs,add_zero]
  smul_mem' := by intro a x hx s hs; rw [smul_dotProduct,hx s hs,smul_zero]

lemma mem_of_dotPerp {m : ℕ} (S : Submodule ℝ (Fin m → ℝ)) (v : Fin m → ℝ)
    (h : ∀x∈dotPerp S,x ⬝ᵥ v=0) : v∈S := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S v).mp
  intro f hf
  have hfzero := (S.mem_dualAnnihilator f).mp hf
  let x : Fin m → ℝ := fun i => f (Pi.single i 1)
  have hx : x∈dotPerp S := by
    intro s hs
    rw [←linear_eq_dot]
    exact hfzero s hs
  rw [linear_eq_dot]
  exact h x hx

lemma dotPerp_symm {m : ℕ} {S : Submodule ℝ (Fin m → ℝ)}
    {x s : Fin m → ℝ} (hx : x∈dotPerp S) (hs : s∈S) : s ⬝ᵥ x=0 := by
  rw [dotProduct_comm]
  exact hx s hs

end ExactSDPDuality.ELSD.Proof
-- End DotPerpendicular

-- Begin StableAnnihilation

open Matrix
namespace ExactSDPDuality.ELSD.Proof

lemma frob_mul_left {n : ℕ} (U V A : Matrix (Fin n) (Fin n) ℝ) :
    frob (U*V) A=frob V (Uᵀ*A) := by
  rw [frob_eq_trace,frob_eq_trace,transpose_mul,Matrix.mul_assoc]

lemma frob_self_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (h:frob A A=0) : A=0 := by
  rw [frob_eq_trace] at h
  exact trace_conjTranspose_mul_self_eq_zero_iff.mp h

lemma mul_zero_of_all_pairings {n : ℕ} (U A : Matrix (Fin n) (Fin n) ℝ)
    (hU:U.IsSymm) (hA:A.IsSymm) (h:∀V,frob (U*V) A=0) : A*U=0 := by
  have hh := h (U*A)
  rw [frob_mul_left,hU.eq] at hh
  have hz := frob_self_zero hh
  have ht := congrArg Matrix.transpose hz
  simpa only [transpose_mul,hU.eq,hA.eq,transpose_zero] using ht

lemma stable_annihilation {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (hQ:∀i,(Q i).IsSymm)
    (S : Submodule ℝ (Fin m → ℝ))
    (hext : ∀U:Matrix (Fin n) (Fin n) ℝ,U.PosSemidef → frob Q0 U=0 →
      Qstar Q U∈S → ∀V,Qstar Q (U*V)∈S)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU:U.PosSemidef) (hzero:frob U Q0=0)
    (horth : ∀x:dotPerp S,frob U (Qhat Q x.val)=0) :
    ∀x:dotPerp S,Qhat Q x.val*U=0 := by
  have hmem : Qstar Q U∈S := by
    apply mem_of_dotPerp S
    intro x hx
    have hh := horth ⟨x,hx⟩
    rwa [frob_qhat,dotProduct_comm] at hh
  intro x
  apply mul_zero_of_all_pairings U (Qhat Q x.val)
  · simpa only [IsHermitian,IsSymm,conjTranspose_eq_transpose_of_trivial] using hU.isHermitian
  · unfold Qhat
    simp only [IsSymm,transpose_sum,transpose_smul,fun i => (hQ i).eq]
  · intro V
    rw [frob_qhat]
    exact dotPerp_symm x.property (hext U hU (by rwa [frob_comm]) hmem V)

end ExactSDPDuality.ELSD.Proof
-- End StableAnnihilation

-- Begin StableCertificateBridge

open Matrix
open scoped BigOperators
namespace ExactSDPDuality.ELSD.Proof

noncomputable def qhatSymm {n m : ℕ} (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀i,(Q i).IsSymm) : (Fin m → ℝ) →ₗ[ℝ] symmSpace n where
  toFun x := ⟨Qhat Q x,by
    change (Qhat Q x).IsSymm
    unfold Qhat
    simp only [IsSymm,transpose_sum,
      transpose_smul,fun i => (hQ i).eq]⟩
  map_add' x y := by apply Subtype.ext; simp [Qhat,add_smul,Finset.sum_add_distrib]
  map_smul' c x := by
    apply Subtype.ext
    simp [Qhat,Finset.smul_sum,smul_smul]

lemma polar_certificate_of_stable {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (hQ0 : Q0.PosSemidef)
    (hQ : ∀i,(Q i).IsSymm) (S : Submodule ℝ (Fin m → ℝ))
    (hext : ∀U:Matrix (Fin n) (Fin n) ℝ,U.PosSemidef → frob Q0 U=0 →
      Qstar Q U∈S → ∀V,Qstar Q (U*V)∈S)
    (c : Fin m → ℝ) (hc : c∈polar (feasibleSet Q0 Q)) :
    ∃U:Matrix (Fin n) (Fin n) ℝ,U.PosSemidef ∧ frob U Q0≤1 ∧ c-Qstar Q U∈S := by
  let T := dotPerp S
  let B : symmSpace n := ⟨Q0,by
    change Q0.IsSymm
    simpa only [IsHermitian,IsSymm,conjTranspose_eq_transpose_of_trivial] using hQ0.isHermitian⟩
  let L : T →ₗ[ℝ] symmSpace n := (qhatSymm Q hQ).comp T.subtype
  let d : T →ₗ[ℝ] ℝ :=
    { toFun := fun x => c ⬝ᵥ x.val
      map_add' := by intro x y; exact dotProduct_add _ _ _
      map_smul' := by intro a x; simp [dotProduct_smul] }
  have hs : ∀U:Matrix (Fin n) (Fin n) ℝ,U.PosSemidef → frob U B.val=0 →
      (∀x:T,frob U (L x).val=0) → ∀x:T,(L x).val*U=0 := by
    intro U hU hz ho
    exact stable_annihilation Q0 Q hQ S hext U hU hz ho
  have hb : ∀x:T,(B-L x).val.PosSemidef → d x≤1 := by
    intro x hx
    simpa only [d,LinearMap.coe_mk,AddHom.coe_mk,dotProduct_comm] using hc x.val hx
  obtain ⟨U,hU,he,hcost⟩ := supported_polar_certificate B L hQ0 hs d hb
  refine ⟨U,hU,hcost,?_⟩
  apply mem_of_dotPerp S
  intro x hx
  have hh := he (⟨x,hx⟩:T)
  change frob U (Qhat Q x)=c ⬝ᵥ x at hh
  rw [frob_qhat] at hh
  rw [dotProduct_sub,dotProduct_comm x c,dotProduct_comm x (Qstar Q U),hh,sub_self]

end ExactSDPDuality.ELSD.Proof
-- End StableCertificateBridge

-- Begin SequenceRecursion

namespace ExactSDPDuality.ELSD.Proof
open Matrix
variable {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
  (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)

theorem mem_wset_zero {X : Matrix (Fin n) (Fin n) ℝ} :
    X ∈ Wset Q0 Q 0 ↔ X = 0 := by
  constructor
  · rintro ⟨U,W,h,hX⟩
    exact hX.symm.trans h.2.1
  · rintro rfl
    exact ⟨0,0,⟨rfl,rfl,by intro i hi hi'; omega⟩,rfl⟩

theorem mem_wset_succ {k : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} :
    X ∈ Wset Q0 Q (k+1) ↔ ∃ U W, W ∈ Wset Q0 Q k ∧
      QsharpZero Q0 Q (U+W) ∧ (U-X*Xᵀ).PosSemidef := by
  constructor
  · rintro ⟨U,W,h,hX⟩
    refine ⟨U (k+1),W k,⟨U,W,⟨h.1,h.2.1,?_⟩,rfl⟩,?_,?_⟩
    · intro i hi hik
      exact h.2.2 i hi (by omega)
    · simpa using (h.2.2 (k+1) (by omega) le_rfl).1
    · simpa [hX] using (h.2.2 (k+1) (by omega) le_rfl).2
  · rintro ⟨A,B,⟨U,W,h,hB⟩,hQ,hP⟩
    let U' := Function.update U (k+1) A
    let W' := Function.update W (k+1) X
    refine ⟨U',W',⟨?_,?_,?_⟩,?_⟩
    · simpa [U'] using h.1
    · simpa [W'] using h.2.1
    · intro i hi hik
      by_cases he : i = k+1
      · subst i
        simpa [U',W',hB] using And.intro hQ hP
      · have hi' : i ≤ k := by omega
        have hprev : i-1 ≠ k+1 := by omega
        simpa [U',W',he,hprev] using h.2.2 i hi hi'
    · simp [W']

end ExactSDPDuality.ELSD.Proof
-- End SequenceRecursion

-- Begin SequenceSubspace

namespace ExactSDPDuality.ELSD.Proof
open Matrix
variable {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
  (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)

theorem wset_zero_mem (k : ℕ) : (0 : Matrix (Fin n) (Fin n) ℝ) ∈ Wset Q0 Q k := by
  refine ⟨0,0,⟨rfl,rfl,?_⟩,rfl⟩
  intro i hi hik
  constructor
  · constructor
    · simp [frob]
    · ext j; simp [Qstar, frob]
  · change ((0 : Matrix (Fin n) (Fin n) ℝ) - 0 * (0 : Matrix (Fin n) (Fin n) ℝ)ᵀ).PosSemidef
    simpa using (PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)

theorem wset_smul_mem (k : ℕ) (a : ℝ) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ Wset Q0 Q k) : a • X ∈ Wset Q0 Q k := by
  induction k generalizing X a with
  | zero => simpa [(mem_wset_zero Q0 Q).mp hX] using wset_zero_mem Q0 Q 0
  | succ k ih =>
    rcases (mem_wset_succ Q0 Q).mp hX with ⟨U,W,hW,hQ,hP⟩
    apply (mem_wset_succ Q0 Q).mpr
    refine ⟨(a*a) • U,(a*a) • W,ih (a:=a*a) hW,?_,?_⟩
    · simpa only [smul_add] using qsharp_smul (a*a) hQ
    · have hh := hP.smul (mul_self_nonneg a)
      convert hh using 1; simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        smul_sub]

theorem wset_add_mem (k : ℕ) {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ Wset Q0 Q k) (hY : Y ∈ Wset Q0 Q k) : X+Y ∈ Wset Q0 Q k := by
  induction k generalizing X Y with
  | zero =>
    rw [(mem_wset_zero Q0 Q).mp hX,(mem_wset_zero Q0 Q).mp hY,add_zero]
    exact wset_zero_mem Q0 Q 0
  | succ k ih =>
    rcases (mem_wset_succ Q0 Q).mp hX with ⟨U,W,hW,hQ,hP⟩
    rcases (mem_wset_succ Q0 Q).mp hY with ⟨U',W',hW',hQ',hP'⟩
    apply (mem_wset_succ Q0 Q).mpr
    refine ⟨(2:ℝ) • (U+U'),(2:ℝ) • (W+W'),wset_smul_mem Q0 Q k 2 (ih hW hW'),?_,?_⟩
    · have hh := qsharp_smul (2:ℝ) (qsharp_add hQ hQ')
      convert hh using 1
      simp only [smul_add]
      abel
    · have hh := ((hP.add hP').smul (show (0:ℝ) ≤ 2 by norm_num)).add
        (posSemidef_self_mul_conjTranspose (X-Y))
      have he : (2:ℝ) • ((U-X*Xᵀ)+(U'-Y*Yᵀ))+(X-Y)*(X-Y)ᴴ =
          (2:ℝ) • (U+U')-(X+Y)*(X+Y)ᵀ := by
        simp only [conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_add,
          two_smul]
        noncomm_ring
      rw [he] at hh
      exact hh

def wSubmodule (k : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := Wset Q0 Q k
  zero_mem' := wset_zero_mem Q0 Q k
  add_mem' := wset_add_mem Q0 Q k
  smul_mem' := fun a _ h => wset_smul_mem Q0 Q k a h

def sSubmodule (k : ℕ) : Submodule ℝ (Fin m → ℝ) :=
  (wSubmodule Q0 Q k).map (qstarLinear Q)

end ExactSDPDuality.ELSD.Proof
-- End SequenceSubspace

-- Begin SequenceMonotone

namespace ExactSDPDuality.ELSD.Proof
open Matrix
variable {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
  (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)

theorem wset_succ_subset (k : ℕ) : Wset Q0 Q k ⊆ Wset Q0 Q (k+1) := by
  induction k with
  | zero =>
    intro X hX
    rw [(mem_wset_zero Q0 Q).mp hX]
    exact wset_zero_mem Q0 Q 1
  | succ k ih =>
    intro X hX
    rcases (mem_wset_succ Q0 Q).mp hX with ⟨U,W,hW,hQ,hP⟩
    exact (mem_wset_succ Q0 Q).mpr ⟨U,W,ih hW,hQ,hP⟩

theorem wset_monotone : Monotone (Wset Q0 Q) := by
  exact monotone_nat_of_le_succ (wset_succ_subset Q0 Q)

theorem sSubmodule_carrier (k : ℕ) : (sSubmodule Q0 Q k : Set (Fin m → ℝ)) =
    Sset Q0 Q k := rfl

theorem sSubmodule_zero : sSubmodule Q0 Q 0 = ⊥ := by
  ext x
  constructor
  · rintro ⟨W,hW,rfl⟩
    rw [(mem_wset_zero Q0 Q).mp hW]
    exact map_zero (qstarLinear Q)
  · intro hx
    have he : x = 0 := hx
    subst x
    exact (sSubmodule Q0 Q 0).zero_mem

theorem sSubmodule_monotone : Monotone (sSubmodule Q0 Q) := by
  intro i j hij x hx
  rcases hx with ⟨W,hW,hx⟩
  exact ⟨W,wset_monotone Q0 Q hij hW,hx⟩

end ExactSDPDuality.ELSD.Proof
-- End SequenceMonotone

-- Begin PSDDomination

namespace ExactSDPDuality.ELSD.Proof
open Matrix
variable {n : ℕ}

theorem frob_eq_zero_of_mul_eq_zero {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (h : A*B=0) : frob A B=0 := by
  rw [frob_eq_trace]
  have ht : Aᵀ=A := hA
  rw [ht,h,trace_zero]

theorem domination_psd {U W : Matrix (Fin n) (Fin n) ℝ}
    (h : (U-W*Wᵀ).PosSemidef) : U.PosSemidef := by
  have hh := h.add (posSemidef_self_mul_conjTranspose W)
  simpa using hh

theorem domination_annihilate {A U W : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (h : (U-W*Wᵀ).PosSemidef) (hAU : frob A U=0) :
    A*U=0 ∧ A*W=0 := by
  have hU := domination_psd h
  have hW : (W*Wᵀ).PosSemidef := posSemidef_self_mul_conjTranspose W
  have h1 := psd_frob_nonneg hA h
  have h2 := psd_frob_nonneg hA hW
  rw [frob_sub_right,hAU] at h1
  have hz : frob A (W*Wᵀ)=0 := by linarith
  have hp := psd_mul_eq_zero_of_frob_eq_zero hA hW hz
  have ht : Aᵀ=A := hA.isHermitian
  have hg : (A*W)*(A*W)ᵀ=0 := by
    rw [transpose_mul,ht]
    calc
      A*W*(Wᵀ*A) = (A*(W*Wᵀ))*A := by noncomm_ring
      _ = 0 := by rw [hp,zero_mul]
  have hz' : ((A*W)*(A*W)ᴴ).trace=0 := by
    rw [conjTranspose_eq_transpose_of_trivial,hg,trace_zero]
  exact ⟨psd_mul_eq_zero_of_frob_eq_zero hA hU hAU,
    trace_mul_conjTranspose_self_eq_zero_iff.mp hz'⟩

end ExactSDPDuality.ELSD.Proof
-- End PSDDomination

-- Begin SequenceAnnihilation

namespace ExactSDPDuality.ELSD.Proof
open Matrix
variable {n m : ℕ} {Q0 : Matrix (Fin n) (Fin n) ℝ}
  {Q : Fin m → Matrix (Fin n) (Fin n) ℝ}

theorem cseq_annihilate {k : ℕ} {U W : ℕ → Matrix (Fin n) (Fin n) ℝ}
    (h : IsCSeq Q0 Q k U W) {x : Fin m → ℝ} (hx : x ∈ feasibleSet Q0 Q)
    (i : ℕ) (hi : i ≤ k) : Qaff Q0 Q x * U i=0 ∧ Qaff Q0 Q x * W i=0 := by
  induction i with
  | zero => rw [h.1,h.2.1,mul_zero]; exact ⟨rfl,rfl⟩
  | succ i ih =>
    have hp := ih (by omega)
    have hs := h.2.2 (i+1) (by omega) hi
    have hq := qsharp_frob_qaff hs.1 x
    have hw := frob_eq_zero_of_mul_eq_zero hx.isHermitian hp.2
    simp only [Nat.add_sub_cancel,frob_add_right,hw,add_zero] at hq
    exact domination_annihilate hx hs.2 hq

theorem wset_annihilate {k : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W ∈ Wset Q0 Q k) {x : Fin m → ℝ} (hx : x ∈ feasibleSet Q0 Q) :
    Qaff Q0 Q x * W=0 := by
  rcases hW with ⟨U,Ws,h,rfl⟩
  exact (cseq_annihilate h hx k le_rfl).2

theorem wset_frob_zero {k : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W ∈ Wset Q0 Q k) {x : Fin m → ℝ} (hx : x ∈ feasibleSet Q0 Q) :
    frob (Qaff Q0 Q x) W=0 :=
  frob_eq_zero_of_mul_eq_zero hx.isHermitian (wset_annihilate hW hx)

theorem zero_feasible (hQ0 : Q0.PosSemidef) : (0 : Fin m → ℝ) ∈ feasibleSet Q0 Q := by
  simpa [feasibleSet,Qaff,Qhat] using hQ0

theorem wset_q0_frob_zero (hQ0 : Q0.PosSemidef) {k : ℕ}
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W ∈ Wset Q0 Q k) : frob Q0 W=0 := by
  simpa [Qaff,Qhat] using wset_frob_zero hW (zero_feasible hQ0)

theorem feasible_annihilates_sSubmodule (hQ0 : Q0.PosSemidef) (k : ℕ)
    {x : Fin m → ℝ} (hx : x ∈ feasibleSet Q0 Q) {y : Fin m → ℝ}
    (hy : y ∈ sSubmodule Q0 Q k) : x ⬝ᵥ y=0 := by
  rcases hy with ⟨W,hW,rfl⟩
  have h := wset_frob_zero hW hx
  rw [frob_comm,frob_qaff,frob_comm W,wset_q0_frob_zero hQ0 hW] at h
  change x ⬝ᵥ Qstar Q W=0
  rw [dotProduct_comm]
  linarith

end ExactSDPDuality.ELSD.Proof
-- End SequenceAnnihilation

-- Begin StableExtension

namespace ExactSDPDuality.ELSD.Proof
open Matrix
variable {n m : ℕ} {Q0 : Matrix (Fin n) (Fin n) ℝ}
  {Q : Fin m → Matrix (Fin n) (Fin n) ℝ}

theorem stable_extension (hQ0 : Q0.PosSemidef) {k : ℕ}
    (hstable : sSubmodule Q0 Q (k+1)=sSubmodule Q0 Q k)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.PosSemidef)
    (hzero : frob Q0 U=0) (hmem : Qstar Q U ∈ sSubmodule Q0 Q k)
    (V : Matrix (Fin n) (Fin n) ℝ) : Qstar Q (U*V) ∈ sSubmodule Q0 Q k := by
  rcases hmem with ⟨W,hW,hWU⟩
  have hWneg : -W ∈ Wset Q0 Q k := (wSubmodule Q0 Q k).neg_mem hW
  have hQ : QsharpZero Q0 Q (U + -W) := by
    constructor
    · rw [frob_add_right,hzero]
      have hz := wset_q0_frob_zero hQ0 hWneg
      rw [hz,add_zero]
    · change qstarLinear Q (U + -W)=0
      rw [map_add,map_neg,hWU]
      change Qstar Q U + -Qstar Q U=0
      exact add_neg_cancel _
  obtain ⟨e,he,hdom⟩ := exists_small_domination U V hU
  have hw : e • (U*V) ∈ Wset Q0 Q (k+1) :=
    (mem_wset_succ Q0 Q).mpr ⟨U,-W,hWneg,hQ,hdom⟩
  have hs : qstarLinear Q (e • (U*V)) ∈ sSubmodule Q0 Q (k+1) := ⟨_,hw,rfl⟩
  rw [hstable,map_smul] at hs
  have ht := (sSubmodule Q0 Q k).smul_mem e⁻¹ hs
  simpa [smul_smul,ne_of_gt he,qstarLinear] using ht

end ExactSDPDuality.ELSD.Proof
-- End StableExtension

-- Begin WeakDuality

namespace ExactSDPDuality.ELSD.Proof
open Matrix
variable {n m : ℕ} {Q0 : Matrix (Fin n) (Fin n) ℝ}
  {Q : Fin m → Matrix (Fin n) (Fin n) ℝ}

theorem stage_weak_duality {k : ℕ} {U W : Matrix (Fin n) (Fin n) ℝ}
    (hU : U.PosSemidef) (hW : W ∈ Wset Q0 Q k)
    {x : Fin m → ℝ} (hx : x ∈ feasibleSet Q0 Q) :
    Qstar Q (U+W) ⬝ᵥ x ≤ frob (U+W) Q0 := by
  have hp := psd_frob_nonneg hU hx
  have hz := wset_frob_zero hW hx
  rw [frob_comm,frob_qaff] at hz
  rw [frob_qaff] at hp
  change qstarLinear Q (U+W) ⬝ᵥ x ≤ _
  rw [map_add,add_dotProduct,frob_add_left]
  change Qstar Q U ⬝ᵥ x + Qstar Q W ⬝ᵥ x ≤ _
  linarith

theorem native_weak_duality {c x : Fin m → ℝ} {U W : Matrix (Fin n) (Fin n) ℝ}
    (hx : x ∈ feasibleSet Q0 Q) (h : ELSDFeasible Q0 Q c U W) :
    c ⬝ᵥ x ≤ frob (U+W) Q0 := by
  rw [←h.1]
  exact stage_weak_duality h.2.2 h.2.1 hx

theorem native_weak_weak_duality {c x : Fin m → ℝ} {U W : Matrix (Fin n) (Fin n) ℝ}
    (hx : x ∈ feasibleSet Q0 Q) (h : WeakELSDFeasible Q0 Q c U W) :
    c ⬝ᵥ x ≤ frob (U+W) Q0 := by
  rw [←h.1]
  exact stage_weak_duality h.2.2 h.2.1 hx

end ExactSDPDuality.ELSD.Proof
-- End WeakDuality

-- Begin OneSidedPolar

namespace ExactSDPDuality.ELSD.Proof
open Set Matrix
variable {m : ℕ}

theorem polar_closed (A : Set (Fin m → ℝ)) : IsClosed (polar A) := by
  have he : polar A = ⋂ x ∈ A, {y | x ⬝ᵥ y ≤ (1:ℝ)} := by ext y; simp [polar]
  rw [he]
  exact isClosed_biInter fun x hx => isClosed_le (by fun_prop) continuous_const

theorem subset_bipolar (A : Set (Fin m → ℝ)) : A ⊆ polar (polar A) := by
  intro x hx y hy
  rw [dotProduct_comm]
  exact hy x hx

theorem bipolar_eq_closure {A : Set (Fin m → ℝ)} (hA : Convex ℝ A)
    (hz : (0 : Fin m → ℝ) ∈ A) : polar (polar A) = closure A := by
  apply le_antisymm
  · intro c hc
    by_contra hn
    obtain ⟨f,u,hsep,hcu⟩ := geometric_hahn_banach_closed_point hA.closure isClosed_closure hn
    have hu : 0<u := by simpa using hsep 0 (subset_closure hz)
    let x : Fin m → ℝ := fun i => f (Pi.single i 1)
    have hfx (y : Fin m → ℝ) : f y=x ⬝ᵥ y := continuousLinear_eq_dot f y
    have hx : u⁻¹ • x ∈ polar A := by
      intro y hy
      rw [dotProduct_smul,smul_eq_mul,←dotProduct_comm x y,←hfx]
      have hh := (hsep y (subset_closure hy)).le
      calc
        u⁻¹ * f y ≤ u⁻¹*u := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hu.le)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hu)
    have hh := hc (u⁻¹ • x) hx
    rw [smul_dotProduct,smul_eq_mul,←hfx] at hh
    have : f c ≤ u := by
      have ht := mul_le_mul_of_nonneg_left hh hu.le
      simpa [←mul_assoc,ne_of_gt hu] using ht
    linarith
  · exact closure_minimal (subset_bipolar A) (polar_closed _)

end ExactSDPDuality.ELSD.Proof
-- End OneSidedPolar

-- Begin AlgebraicPolar

namespace ExactSDPDuality.ELSD.Proof
open Matrix Set
variable {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
  (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)

theorem algPolar_zero : (0 : Fin m → ℝ) ∈ algPolar Q0 Q := by
  refine ⟨0,PosSemidef.zero,?_,?_⟩
  · simp [frob]
  · exact map_zero (qstarLinear Q)

theorem algPolar_convex : Convex ℝ (algPolar Q0 Q) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨U,hU,hU0,rfl⟩
  rcases hy with ⟨V,hV,hV0,rfl⟩
  refine ⟨a • U+b • V,(hU.smul ha).add (hV.smul hb),?_,?_⟩
  · rw [frob_add_left,frob_smul_left,frob_smul_left]
    nlinarith [mul_le_mul_of_nonneg_left hU0 ha,mul_le_mul_of_nonneg_left hV0 hb]
  · change qstarLinear Q (a • U+b • V) = _
    rw [map_add,map_smul,map_smul]
    rfl

theorem algPolar_subset_polar : algPolar Q0 Q ⊆ polar (feasibleSet Q0 Q) := by
  rintro y ⟨U,hU,hU0,rfl⟩ x hx
  have h := psd_frob_nonneg hU hx
  rw [frob_qaff] at h
  rw [dotProduct_comm]
  linarith

theorem feasible_subset_polar_algPolar : feasibleSet Q0 Q ⊆ polar (algPolar Q0 Q) := by
  intro x hx y hy
  rw [dotProduct_comm]
  exact algPolar_subset_polar Q0 Q hy x hx

end ExactSDPDuality.ELSD.Proof
-- End AlgebraicPolar

-- Begin PolarClosure

namespace ExactSDPDuality.ELSD.Proof
open Matrix Set
variable {n m : ℕ} {Q0 : Matrix (Fin n) (Fin n) ℝ}
  {Q : Fin m → Matrix (Fin n) (Fin n) ℝ}

theorem rankOne_frob (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    frob (vecMulVec v v) A = v ⬝ᵥ (A*ᵥv) := by
  simp only [frob,vecMulVec_apply,dotProduct,mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem polar_algPolar_eq_feasible (hQ0 : Q0.PosSemidef)
    (hQ : ∀i,(Q i).IsHermitian) : polar (algPolar Q0 Q) = feasibleSet Q0 Q := by
  apply le_antisymm
  · intro x hx
    apply PosSemidef.of_dotProduct_mulVec_nonneg
    · apply hQ0.isHermitian.sub
      change (Qhat Q x)ᴴ = Qhat Q x
      simp only [Qhat,conjTranspose_sum,conjTranspose_smul,star_trivial]
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun A => x i • A) (hQ i).eq)
    · intro v
      let U := vecMulVec v v
      have hU : U.PosSemidef := by simpa [U] using posSemidef_vecMulVec_self_star v
      have ha : 0 ≤ frob U Q0 := psd_frob_nonneg hU hQ0
      have hb : Qstar Q U ⬝ᵥ x ≤ frob U Q0 := by
        apply le_of_forall_pos_le_add
        intro e he
        let t := frob U Q0 + e
        have ht : 0<t := by dsimp [t]; linarith
        have hm : Qstar Q (t⁻¹ • U) ∈ algPolar Q0 Q := by
          refine ⟨t⁻¹ • U,hU.smul (inv_nonneg.mpr ht.le),?_,rfl⟩
          rw [frob_smul_left]
          calc
            t⁻¹ * frob U Q0 ≤ t⁻¹*t := mul_le_mul_of_nonneg_left (by dsimp [t]; linarith) (inv_nonneg.mpr ht.le)
            _ = 1 := inv_mul_cancel₀ (ne_of_gt ht)
        have hh := hx _ hm
        change qstarLinear Q (t⁻¹ • U) ⬝ᵥ x ≤ 1 at hh
        rw [map_smul,smul_dotProduct,smul_eq_mul] at hh
        have hh' := mul_le_mul_of_nonneg_left hh ht.le
        simpa [←mul_assoc,ne_of_gt ht,t,qstarLinear] using hh'
      have hz : 0 ≤ frob U (Qaff Q0 Q x) := by rw [frob_qaff]; linarith
      simpa only [U,rankOne_frob,star_trivial] using hz
  · exact feasible_subset_polar_algPolar Q0 Q

theorem closure_algPolar (hQ0 : Q0.PosSemidef) (hQ : ∀i,(Q i).IsHermitian) :
    closure (algPolar Q0 Q) = polar (feasibleSet Q0 Q) := by
  rw [← bipolar_eq_closure (algPolar_convex Q0 Q) (algPolar_zero Q0 Q),
    polar_algPolar_eq_feasible hQ0 hQ]

end ExactSDPDuality.ELSD.Proof
-- End PolarClosure

-- Begin ConvexDense

namespace ExactSDPDuality.ELSD.Proof
open Set
variable {m : ℕ}

theorem convex_dense_eq_univ {A : Set (Fin m → ℝ)} (hA : Convex ℝ A)
    (hcl : closure A=univ) : A=univ := by
  have hs : affineSpan ℝ A=⊤ := by
    apply top_unique
    intro x hx
    exact closure_minimal (subset_affineSpan ℝ A)
      (affineSpan ℝ A).closed_of_finiteDimensional (by rw [hcl]; trivial)
  have hi := hA.interior_nonempty_iff_affineSpan_eq_top.mpr hs
  have he := hA.interior_closure_eq_interior_of_nonempty_interior hi
  rw [hcl,interior_univ] at he
  apply Set.eq_univ_of_univ_subset
  rw [he]
  exact interior_subset

end ExactSDPDuality.ELSD.Proof
-- End ConvexDense

-- Begin DimensionStabilization

namespace ExactSDPDuality.ELSD.Proof

theorem stabilizes_or_top {m : ℕ} (S : ℕ → Submodule ℝ (Fin m → ℝ))
    (hmono : Monotone S) : (∃ k < m,S (k+1)=S k) ∨ S m=⊤ := by
  by_cases h : ∃ k < m,S (k+1)=S k
  · exact Or.inl h
  right
  have hh : ∀ k ≤ m,k ≤ Module.finrank ℝ (S k) := by
    intro k hk
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have he : S k ≠ S (k+1) := by
        intro he
        exact h ⟨k,by omega,he.symm⟩
      have hr := Submodule.finrank_lt_finrank_of_lt
        (lt_of_le_of_ne (hmono (by omega : k≤k+1)) he)
      have hp := ih (by omega)
      omega
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le _)
  simpa using hh m le_rfl

end ExactSDPDuality.ELSD.Proof
-- End DimensionStabilization

-- Begin StageCertificate

namespace ExactSDPDuality.ELSD.Proof
open Matrix Set
variable {n m : ℕ} {Q0 : Matrix (Fin n) (Fin n) ℝ}
  {Q : Fin m → Matrix (Fin n) (Fin n) ℝ}

def StableCertificate (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ k, sSubmodule Q0 Q (k+1)=sSubmodule Q0 Q k →
    ∀ c ∈ polar (feasibleSet Q0 Q), ∃ U, U.PosSemidef ∧ frob U Q0≤1 ∧
      c-Qstar Q U ∈ sSubmodule Q0 Q k

theorem weak_polar_certificate (hQ0 : Q0.PosSemidef) (hQ : ∀i,(Q i).IsHermitian)
    (hcert : StableCertificate Q0 Q) {c : Fin m → ℝ}
    (hc : c ∈ polar (feasibleSet Q0 Q)) :
    ∃ U W, U.PosSemidef ∧ frob U Q0≤1 ∧ W ∈ Wset Q0 Q (m-1) ∧ Qstar Q (U+W)=c := by
  rcases stabilizes_or_top (sSubmodule Q0 Q) (sSubmodule_monotone Q0 Q) with h | h
  · rcases h with ⟨k,hk,he⟩
    obtain ⟨U,hU,hU0,W,hW,hWU⟩ := hcert k he c hc
    refine ⟨U,W,hU,hU0,wset_monotone Q0 Q (by omega : k ≤ m - 1) hW,?_⟩
    change qstarLinear Q (U+W)=c
    rw [map_add,hWU]
    change Qstar Q U+(c-Qstar Q U)=c
    abel
  · have hG : feasibleSet Q0 Q = {0} := by
      ext x
      constructor
      · intro hx
        have hm : x ∈ sSubmodule Q0 Q m := by rw [h]; trivial
        have hh := feasible_annihilates_sSubmodule hQ0 m hx hm
        exact dotProduct_self_eq_zero.mp hh
      · rintro rfl
        exact zero_feasible hQ0
    have hcl : closure (algPolar Q0 Q)=univ := by
      rw [closure_algPolar hQ0 hQ,hG]
      ext y
      simp [polar]
    have hA := convex_dense_eq_univ (algPolar_convex Q0 Q) hcl
    have hm : c ∈ algPolar Q0 Q := by rw [hA]; trivial
    obtain ⟨U,hU,hU0,hUc⟩ := hm
    refine ⟨U,0,hU,hU0,wset_zero_mem Q0 Q (m-1),?_⟩
    simpa using hUc

end ExactSDPDuality.ELSD.Proof
-- End StageCertificate

-- Begin CertificateInterface

namespace ExactSDPDuality.ELSD.Proof

def PolarSystem : Prop := ∀ (n m : ℕ) (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ), Q0.PosSemidef →
    (∀ i,(Q i).IsHermitian) → ∀ c ∈ polar (feasibleSet Q0 Q),
    ∃ U W, U.PosSemidef ∧ frob U Q0≤1 ∧ W ∈ Wset Q0 Q (m-1) ∧ Qstar Q (U+W)=c

end ExactSDPDuality.ELSD.Proof
-- End CertificateInterface

-- Begin PolarSystem

namespace ExactSDPDuality.ELSD.Proof

theorem polar_system : PolarSystem := by
  intro n m Q0 Q hQ0 hQ c hc
  apply weak_polar_certificate hQ0 hQ
  · intro k hk d hd
    have hQs : ∀i,(Q i).IsSymm := hQ
    exact polar_certificate_of_stable Q0 Q hQ0 hQs (sSubmodule Q0 Q k)
      (stable_extension hQ0 hk) d hd
  · exact hc

end ExactSDPDuality.ELSD.Proof
-- End PolarSystem

-- Begin Translation

namespace ExactSDPDuality.ELSD.Proof
open Matrix Set
variable {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
  (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (a : Fin m → ℝ)

theorem qsharp_translate (X : Matrix (Fin n) (Fin n) ℝ) :
    QsharpZero (Qaff Q0 Q a) Q X ↔ QsharpZero Q0 Q X := by
  unfold QsharpZero
  rw [frob_comm (Qaff Q0 Q a),frob_qaff,frob_comm X]
  constructor <;> rintro ⟨h,hx⟩ <;> refine ⟨?_,hx⟩ <;> simpa [hx] using h

theorem cseq_translate (k : ℕ) (U W : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    IsCSeq (Qaff Q0 Q a) Q k U W ↔ IsCSeq Q0 Q k U W := by
  simp only [IsCSeq,qsharp_translate]

theorem wset_translate (k : ℕ) : Wset (Qaff Q0 Q a) Q k = Wset Q0 Q k := by
  ext W
  simp only [Wset,Set.mem_ofPred_eq,cseq_translate]

theorem qhat_add (x y : Fin m → ℝ) : Qhat Q (x+y)=Qhat Q x+Qhat Q y := by
  simp [Qhat,add_smul,Finset.sum_add_distrib]

theorem qaff_translate (x : Fin m → ℝ) :
    Qaff (Qaff Q0 Q a) Q x = Qaff Q0 Q (a+x) := by
  simp only [Qaff,qhat_add]
  abel

theorem feasible_translate (x : Fin m → ℝ) :
    x ∈ feasibleSet (Qaff Q0 Q a) Q ↔ a+x ∈ feasibleSet Q0 Q := by
  simp only [feasibleSet,Set.mem_ofPred_eq,qaff_translate]

theorem elsd_translate (c : Fin m → ℝ) (U W : Matrix (Fin n) (Fin n) ℝ) :
    ELSDFeasible (Qaff Q0 Q a) Q c U W ↔ ELSDFeasible Q0 Q c U W := by
  simp only [ELSDFeasible,wset_translate]

theorem weakElsd_translate (c : Fin m → ℝ) (U W : Matrix (Fin n) (Fin n) ℝ) :
    WeakELSDFeasible (Qaff Q0 Q a) Q c U W ↔ WeakELSDFeasible Q0 Q c U W := by
  simp only [WeakELSDFeasible,wset_translate]

theorem dual_cost_translate {c : Fin m → ℝ} {U W : Matrix (Fin n) (Fin n) ℝ}
    (h : Qstar Q (U+W)=c) :
    frob (U+W) (Qaff Q0 Q a) = frob (U+W) Q0-c ⬝ᵥ a := by
  rw [frob_qaff,h]

end ExactSDPDuality.ELSD.Proof
-- End Translation

-- Begin PositiveCertificate

namespace ExactSDPDuality.ELSD.Proof
open Matrix Set
variable {n m : ℕ} {Q0 : Matrix (Fin n) (Fin n) ℝ}
  {Q : Fin m → Matrix (Fin n) (Fin n) ℝ} {c : Fin m → ℝ}

theorem weak_to_elsd {U W : Matrix (Fin n) (Fin n) ℝ}
    (h : WeakELSDFeasible Q0 Q c U W) : ELSDFeasible Q0 Q c U W :=
  ⟨h.1,wset_monotone Q0 Q (Nat.sub_le m 1) h.2.1,h.2.2⟩

theorem positive_upper_certificate (hsys : PolarSystem) (hQ0 : Q0.PosSemidef)
    (hQ : ∀ i,(Q i).IsHermitian) {t : ℝ} (ht : 0<t)
    (hub : ∀x ∈ feasibleSet Q0 Q,c ⬝ᵥ x≤t) :
    ∃ U W, WeakELSDFeasible Q0 Q c U W ∧ frob (U+W) Q0≤t := by
  have hc : t⁻¹ • c ∈ polar (feasibleSet Q0 Q) := by
    intro x hx
    rw [dotProduct_smul,smul_eq_mul,dotProduct_comm x c]
    calc
      t⁻¹*(c ⬝ᵥ x) ≤ t⁻¹*t := mul_le_mul_of_nonneg_left (hub x hx) (inv_nonneg.mpr ht.le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt ht)
  obtain ⟨U,W,hU,hU0,hW,hUW⟩ := hsys n m Q0 Q hQ0 hQ (t⁻¹ • c) hc
  refine ⟨t • U,t • W,⟨?_,wset_smul_mem Q0 Q (m-1) t hW,hU.smul ht.le⟩,?_⟩
  · change qstarLinear Q (t • U+t • W)=c
    rw [←smul_add,map_smul]
    change t • Qstar Q (U+W)=c
    rw [hUW,smul_smul,mul_inv_cancel₀ (ne_of_gt ht),one_smul]
  · rw [←smul_add,frob_smul_left,frob_add_left,frob_comm W,wset_q0_frob_zero hQ0 hW,add_zero]
    simpa using mul_le_mul_of_nonneg_left hU0 ht.le

theorem weak_feasible_bdd {U W : Matrix (Fin n) (Fin n) ℝ}
    (h : WeakELSDFeasible Q0 Q c U W) : BddAbove (primalValues Q0 Q c) := by
  refine ⟨frob (U+W) Q0,?_⟩
  rintro y ⟨x,hx,rfl⟩
  exact native_weak_weak_duality hx h

theorem elsd_feasible_bdd {U W : Matrix (Fin n) (Fin n) ℝ}
    (h : ELSDFeasible Q0 Q c U W) : BddAbove (primalValues Q0 Q c) := by
  refine ⟨frob (U+W) Q0,?_⟩
  rintro y ⟨x,hx,rfl⟩
  exact native_weak_duality hx h

end ExactSDPDuality.ELSD.Proof
-- End PositiveCertificate

-- Begin NativeBoundedness

namespace ExactSDPDuality.ELSD.Proof
open Matrix Set
variable {n m : ℕ} {Q0 : Matrix (Fin n) (Fin n) ℝ}
  {Q : Fin m → Matrix (Fin n) (Fin n) ℝ} {c : Fin m → ℝ}

theorem upper_certificate (hsys : PolarSystem) (hQ : ∀ i,(Q i).IsHermitian)
    {a : Fin m → ℝ} (ha : a ∈ feasibleSet Q0 Q) {b : ℝ}
    (hb : c ⬝ᵥ a<b) (hub : ∀ x ∈ feasibleSet Q0 Q,c ⬝ᵥ x≤b) :
    ∃ U W, WeakELSDFeasible Q0 Q c U W ∧ frob (U+W) Q0≤b := by
  have ht : 0<b-c ⬝ᵥ a := by linarith
  have hu : ∀x ∈ feasibleSet (Qaff Q0 Q a) Q,c ⬝ᵥ x ≤ b-c ⬝ᵥ a := by
    intro x hx
    have hax := (feasible_translate Q0 Q a x).mp hx
    have h := hub (a+x) hax
    rw [dotProduct_add] at h
    linarith
  obtain ⟨U,W,hUW,hcost⟩ := positive_upper_certificate hsys ha hQ ht hu
  have hn := (weakElsd_translate Q0 Q a c U W).mp hUW
  refine ⟨U,W,hn,?_⟩
  rw [dual_cost_translate Q0 Q a hn.1] at hcost
  linarith

theorem native_boundedness (hsys : PolarSystem) (hQ : ∀ i,(Q i).IsHermitian)
    (hne : (feasibleSet Q0 Q).Nonempty) :
    (BddAbove (primalValues Q0 Q c) ↔ ∃ U W,ELSDFeasible Q0 Q c U W) ∧
    (BddAbove (primalValues Q0 Q c) ↔ ∃ U W,WeakELSDFeasible Q0 Q c U W) := by
  have hf : BddAbove (primalValues Q0 Q c) → ∃ U W,WeakELSDFeasible Q0 Q c U W := by
    rintro ⟨b,hb⟩
    obtain ⟨a,ha⟩ := hne
    have hba : c ⬝ᵥ a≤b := hb ⟨a,ha,rfl⟩
    obtain ⟨U,W,h,_⟩ := upper_certificate hsys hQ ha (b:=b+1) (by linarith)
      (fun x hx => (hb ⟨x,hx,rfl⟩).trans (by linarith))
    exact ⟨U,W,h⟩
  constructor
  · constructor
    · intro h; obtain ⟨U,W,h⟩ := hf h; exact ⟨U,W,weak_to_elsd h⟩
    · rintro ⟨U,W,h⟩; exact elsd_feasible_bdd h
  · exact ⟨hf,fun ⟨U,W,h⟩ => weak_feasible_bdd h⟩

end ExactSDPDuality.ELSD.Proof
-- End NativeBoundedness

-- Begin CommonValue

namespace ExactSDPDuality.ELSD.Proof
open Matrix Set
variable {n m : ℕ} {Q0 : Matrix (Fin n) (Fin n) ℝ}
  {Q : Fin m → Matrix (Fin n) (Fin n) ℝ} {c : Fin m → ℝ}

theorem primal_nonempty (hne : (feasibleSet Q0 Q).Nonempty) :
    (primalValues Q0 Q c).Nonempty := hne.image _

theorem lub_le_weak_cost {v : ℝ} (hv : IsLUB (primalValues Q0 Q c) v)
    {U W : Matrix (Fin n) (Fin n) ℝ} (h : WeakELSDFeasible Q0 Q c U W) :
    v≤frob (U+W) Q0 := by
  apply hv.2
  rintro z ⟨x,hx,rfl⟩
  exact native_weak_weak_duality hx h

theorem lub_le_cost {v : ℝ} (hv : IsLUB (primalValues Q0 Q c) v)
    {U W : Matrix (Fin n) (Fin n) ℝ} (h : ELSDFeasible Q0 Q c U W) :
    v≤frob (U+W) Q0 := by
  apply hv.2
  rintro z ⟨x,hx,rfl⟩
  exact native_weak_duality hx h

theorem dual_glbs (hsys : PolarSystem) (hQ : ∀i,(Q i).IsHermitian)
    (hne : (feasibleSet Q0 Q).Nonempty) {v : ℝ}
    (hv : IsLUB (primalValues Q0 Q c) v) :
    IsGLB (elsdValues Q0 Q c) v ∧ IsGLB (weakElsdValues Q0 Q c) v := by
  have happ : ∀e:ℝ,0<e → ∃U W,WeakELSDFeasible Q0 Q c U W ∧ frob (U+W) Q0≤v+e := by
    intro e he
    obtain ⟨a,ha⟩ := hne
    have hca := hv.1 ⟨a,ha,rfl⟩
    exact upper_certificate hsys hQ ha (by linarith)
      (fun x hx => (hv.1 ⟨x,hx,rfl⟩).trans (by linarith))
  constructor
  · constructor
    · rintro z ⟨U,W,h,rfl⟩
      exact lub_le_cost hv h
    · intro b hb
      apply le_of_forall_pos_le_add
      intro e he
      obtain ⟨U,W,h,hcost⟩ := happ e he
      exact (hb ⟨U,W,weak_to_elsd h,rfl⟩).trans hcost
  · constructor
    · rintro z ⟨U,W,h,rfl⟩
      exact lub_le_weak_cost hv h
    · intro b hb
      apply le_of_forall_pos_le_add
      intro e he
      obtain ⟨U,W,h,hcost⟩ := happ e he
      exact (hb ⟨U,W,h,rfl⟩).trans hcost

theorem native_common_value (hsys : PolarSystem) (hQ : ∀i,(Q i).IsHermitian)
    (hne : (feasibleSet Q0 Q).Nonempty) (hbd : BddAbove (primalValues Q0 Q c)) :
    ∃v:ℝ,IsLUB (primalValues Q0 Q c) v ∧ IsGLB (elsdValues Q0 Q c) v ∧
      IsGLB (weakElsdValues Q0 Q c) v := by
  have hv := isLUB_csSup (primal_nonempty hne) hbd
  exact ⟨_,hv,dual_glbs hsys hQ hne hv⟩

end ExactSDPDuality.ELSD.Proof
-- End CommonValue

-- Begin HomogeneousModel

namespace ExactSDPDuality.ELSD.Proof
open Matrix Set
variable {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
  (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)

def homQ : Fin (m+1) → Matrix (Fin n) (Fin n) ℝ := Fin.cons (-Q0) Q

def homC (c : Fin m → ℝ) : Fin (m+1) → ℝ := Fin.cons 0 c

theorem homQ_qhat (x : Fin (m+1) → ℝ) :
    Qhat (homQ Q0 Q) x = -(x 0 • Q0)+Qhat Q (fun i => x i.succ) := by
  simp [Qhat,homQ,Fin.sum_univ_succ]

theorem homQ_qaff (x : Fin (m+1) → ℝ) :
    Qaff 0 (homQ Q0 Q) x = x 0 • Q0-Qhat Q (fun i => x i.succ) := by
  rw [Qaff,homQ_qhat]
  abel

theorem homC_dot (c : Fin m → ℝ) (x : Fin (m+1) → ℝ) :
    homC c ⬝ᵥ x = c ⬝ᵥ (fun i => x i.succ) := by
  simp [homC,dotProduct,Fin.sum_univ_succ]

theorem homQ_sharp (X : Matrix (Fin n) (Fin n) ℝ) :
    QsharpZero 0 (homQ Q0 Q) X ↔ QsharpZero Q0 Q X := by
  constructor
  · intro h
    have hz := congrFun h.2 0
    have ht := congrArg (fun y : Fin (m+1) → ℝ => fun i : Fin m => y i.succ) h.2
    constructor
    · change frob X (-Q0)=0 at hz
      rw [frob_comm] at hz
      simpa [frob] using hz
    · exact ht
  · rintro ⟨h0,h⟩
    constructor
    · simp [frob]
    · ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change frob X (-Q0)=0
        rw [frob_comm]
        simpa [frob] using congrArg Neg.neg h0
      · exact congrFun h j

theorem homQ_wset (k : ℕ) : Wset 0 (homQ Q0 Q) k = Wset Q0 Q k := by
  ext W
  simp only [Wset,Set.mem_ofPred_eq,IsCSeq,homQ_sharp]

theorem homQ_hermitian (h0 : Q0.IsHermitian) (hQ : ∀i,(Q i).IsHermitian) :
    ∀i,(homQ Q0 Q i).IsHermitian := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact h0.neg
  · exact hQ j

end ExactSDPDuality.ELSD.Proof
-- End HomogeneousModel

-- Begin HomogeneousFeasible

namespace ExactSDPDuality.ELSD.Proof
open Matrix Set
variable {n m : ℕ} {Q0 : Matrix (Fin n) (Fin n) ℝ}
  {Q : Fin m → Matrix (Fin n) (Fin n) ℝ}

theorem qhat_smul (a : ℝ) (x : Fin m → ℝ) : Qhat Q (a • x)=a • Qhat Q x := by
  simp [Qhat,Finset.smul_sum,smul_smul]

theorem hom_normalize {x : Fin (m+1) → ℝ} (hQ0 : Q0.PosSemidef)
    (hx : x ∈ feasibleSet 0 (homQ Q0 Q)) {r : ℝ} (hr : 0≤r)
    (ht : 0<x 0+r) :
    (x 0+r)⁻¹ • (fun i => x i.succ) ∈ feasibleSet Q0 Q := by
  have hh := (hx.add (hQ0.smul hr)).smul (inv_nonneg.mpr ht.le)
  have he : Qaff Q0 Q ((x 0+r)⁻¹ • (fun i => x i.succ)) =
      (x 0+r)⁻¹ • (Qaff 0 (homQ Q0 Q) x+r • Q0) := by
    rw [homQ_qaff,Qaff,qhat_smul]
    have he' : x 0 • Q0-Qhat Q (fun i => x i.succ)+r • Q0 =
        (x 0+r) • Q0-Qhat Q (fun i => x i.succ) := by rw [add_smul]; abel
    rw [he',smul_sub,smul_smul,inv_mul_cancel₀ (ne_of_gt ht),one_smul]
  rw [←he] at hh
  exact hh

theorem hom_objective_nonpos (hQ0 : Q0.PosSemidef) {c : Fin m → ℝ}
    (hub : ∀x ∈ feasibleSet Q0 Q,c ⬝ᵥ x≤0) :
    ∀x ∈ feasibleSet 0 (homQ Q0 Q),homC c ⬝ᵥ x≤0 := by
  intro x hx
  let r := |x 0|+1
  have hr : 0≤r := by dsimp [r]; positivity
  have ht : 0<x 0+r := by dsimp [r]; linarith [neg_abs_le (x 0)]
  have h := hub _ (hom_normalize hQ0 hx hr ht)
  rw [dotProduct_smul,smul_eq_mul] at h
  rw [homC_dot]
  have hh := mul_le_mul_of_nonneg_left h ht.le
  simpa [←mul_assoc,ne_of_gt ht] using hh

end ExactSDPDuality.ELSD.Proof
-- End HomogeneousFeasible

-- Begin ZeroAttainment

namespace ExactSDPDuality.ELSD.Proof
open Matrix Set
variable {n m : ℕ} {Q0 : Matrix (Fin n) (Fin n) ℝ}
  {Q : Fin m → Matrix (Fin n) (Fin n) ℝ} {c : Fin m → ℝ}

theorem zero_attainment (hsys : PolarSystem) (hQ0 : Q0.PosSemidef)
    (hQ : ∀i,(Q i).IsHermitian) (hub : ∀x ∈ feasibleSet Q0 Q,c ⬝ᵥ x≤0) :
    ∃U W,ELSDFeasible Q0 Q c U W ∧ frob (U+W) Q0=0 := by
  have hn : (feasibleSet (0 : Matrix (Fin n) (Fin n) ℝ) (homQ Q0 Q)).Nonempty :=
    ⟨0,zero_feasible PosSemidef.zero⟩
  have hb : BddAbove (primalValues 0 (homQ Q0 Q) (homC c)) := by
    refine ⟨0,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact hom_objective_nonpos hQ0 hub x hx
  obtain ⟨U,W,h⟩ := ((native_boundedness hsys (homQ_hermitian Q0 Q hQ0.isHermitian hQ) hn).2).mp hb
  have hw : W ∈ Wset Q0 Q m := by
    simpa only [Nat.add_sub_cancel,homQ_wset] using h.2.1
  have hc : Qstar Q (U+W)=c := by
    ext i
    exact congrFun h.1 i.succ
  have hz := congrFun h.1 0
  change frob (U+W) (-Q0)=0 at hz
  have hz' : frob (U+W) Q0=0 := by
    simpa [frob] using hz
  exact ⟨U,W,⟨hc,hw,h.2.2⟩,hz'⟩

end ExactSDPDuality.ELSD.Proof
-- End ZeroAttainment

-- Begin NativeAttainment

namespace ExactSDPDuality.ELSD.Proof
open Matrix Set
variable {n m : ℕ} {Q0 : Matrix (Fin n) (Fin n) ℝ}
  {Q : Fin m → Matrix (Fin n) (Fin n) ℝ} {c : Fin m → ℝ}

theorem attain_at_lub (hsys : PolarSystem) (hQ : ∀i,(Q i).IsHermitian)
    (hne : (feasibleSet Q0 Q).Nonempty) {v : ℝ}
    (hv : IsLUB (primalValues Q0 Q c) v) :
    ∃U W,ELSDFeasible Q0 Q c U W ∧ frob (U+W) Q0=v := by
  obtain ⟨a,ha⟩ := hne
  have hca : c ⬝ᵥ a≤v := hv.1 ⟨a,ha,rfl⟩
  have hub : ∀x ∈ feasibleSet (Qaff Q0 Q a) Q,c ⬝ᵥ x≤v-c ⬝ᵥ a := by
    intro x hx
    have hax := (feasible_translate Q0 Q a x).mp hx
    have h := hv.1 ⟨a+x,hax,rfl⟩
    change c ⬝ᵥ (a+x) ≤ v at h
    rw [dotProduct_add] at h
    linarith
  rcases lt_or_eq_of_le hca with hlt | heq
  · obtain ⟨U,W,h,hcost⟩ := positive_upper_certificate hsys ha hQ (sub_pos.mpr hlt) hub
    have hn := weak_to_elsd ((weakElsd_translate Q0 Q a c U W).mp h)
    have hlo := lub_le_cost hv hn
    rw [dual_cost_translate Q0 Q a hn.1] at hcost
    exact ⟨U,W,hn,by linarith⟩
  · have hu0 : ∀x ∈ feasibleSet (Qaff Q0 Q a) Q,c ⬝ᵥ x≤0 := by
      intro x hx
      simpa [heq] using hub x hx
    obtain ⟨U,W,h,hcost⟩ := zero_attainment hsys ha hQ hu0
    have hn := (elsd_translate Q0 Q a c U W).mp h
    rw [dual_cost_translate Q0 Q a hn.1] at hcost
    exact ⟨U,W,hn,by linarith⟩

theorem native_attainment (hsys : PolarSystem) (hQ : ∀i,(Q i).IsHermitian)
    (hne : (feasibleSet Q0 Q).Nonempty) (hbd : BddAbove (primalValues Q0 Q c)) :
    ∃v:ℝ,IsLUB (primalValues Q0 Q c) v ∧
      ∃U W,ELSDFeasible Q0 Q c U W ∧ frob (U+W) Q0=v := by
  have hv := isLUB_csSup (primal_nonempty hne) hbd
  exact ⟨_,hv,attain_at_lub hsys hQ hne hv⟩

end ExactSDPDuality.ELSD.Proof
-- End NativeAttainment

-- Begin RootFromCertificate

namespace ExactSDPDuality.ELSD.Proof

/-- Theorem 6, the Duality Theorem (Ramana 1997, p. 138), for the primal SDP
`sup cᵀx s.t. ∑ᵢ xᵢ Qᵢ ⪯ Q₀` with real symmetric data and no constraint qualification:
(i) weak duality for (ELSD) and (Weak-ELSD);
(ii) a feasible primal has finite optimal value iff (ELSD) (resp. (Weak-ELSD)) is feasible;
(iii) if the primal and (ELSD) (or (Weak-ELSD)) are feasible, the three optimal values coincide;
(iv) when the common optimal value is finite, (ELSD) attains it. -/
theorem duality_of_polar_system (hsys : PolarSystem) {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ)
    (_hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm) :
    -- (i) weak duality
    ((∀ x ∈ feasibleSet Q0 Q, ∀ U W : Matrix (Fin n) (Fin n) ℝ,
        ELSDFeasible Q0 Q c U W → c ⬝ᵥ x ≤ frob (U + W) Q0) ∧
      (∀ x ∈ feasibleSet Q0 Q, ∀ U W : Matrix (Fin n) (Fin n) ℝ,
        WeakELSDFeasible Q0 Q c U W → c ⬝ᵥ x ≤ frob (U + W) Q0)) ∧
    -- (ii) primal boundedness
    ((feasibleSet Q0 Q).Nonempty →
      (BddAbove (primalValues Q0 Q c) ↔ ∃ U W, ELSDFeasible Q0 Q c U W) ∧
        (BddAbove (primalValues Q0 Q c) ↔ ∃ U W, WeakELSDFeasible Q0 Q c U W)) ∧
    -- (iii) zero gap
    ((feasibleSet Q0 Q).Nonempty →
      ((∃ U W, ELSDFeasible Q0 Q c U W) ∨ (∃ U W, WeakELSDFeasible Q0 Q c U W)) →
      ∃ v : ℝ, IsLUB (primalValues Q0 Q c) v ∧ IsGLB (elsdValues Q0 Q c) v ∧
        IsGLB (weakElsdValues Q0 Q c) v) ∧
    -- (iv) dual attainment
    ((feasibleSet Q0 Q).Nonempty → BddAbove (primalValues Q0 Q c) →
      ∃ v : ℝ, IsLUB (primalValues Q0 Q c) v ∧
        ∃ U W, ELSDFeasible Q0 Q c U W ∧ frob (U + W) Q0 = v) := by
  have hQi : ∀i,(Q i).IsHermitian := hQ
  refine ⟨⟨?_,?_⟩,?_,?_,?_⟩
  · intro x hx U W h
    exact native_weak_duality hx h
  · intro x hx U W h
    exact native_weak_weak_duality hx h
  · intro hne
    exact native_boundedness hsys hQi hne
  · intro hne hd
    have hb : BddAbove (primalValues Q0 Q c) := by
      rcases hd with ⟨U,W,h⟩ | ⟨U,W,h⟩
      · exact elsd_feasible_bdd h
      · exact weak_feasible_bdd h
    exact native_common_value hsys hQi hne hb
  · intro hne hb
    exact native_attainment hsys hQi hne hb

end ExactSDPDuality.ELSD.Proof
-- End RootFromCertificate

-- Begin RootAssembly

namespace ExactSDPDuality.ELSD

/-- Theorem 6, the Duality Theorem (Ramana 1997, p. 138), for the primal SDP
`sup cᵀx s.t. ∑ᵢ xᵢ Qᵢ ⪯ Q₀` with real symmetric data and no constraint qualification:
(i) weak duality for (ELSD) and (Weak-ELSD);
(ii) a feasible primal has finite optimal value iff (ELSD) (resp. (Weak-ELSD)) is feasible;
(iii) if the primal and (ELSD) (or (Weak-ELSD)) are feasible, the three optimal values coincide;
(iv) when the common optimal value is finite, (ELSD) attains it. -/
theorem duality_theorem {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm) :
    -- (i) weak duality
    ((∀ x ∈ feasibleSet Q0 Q, ∀ U W : Matrix (Fin n) (Fin n) ℝ,
        ELSDFeasible Q0 Q c U W → c ⬝ᵥ x ≤ frob (U + W) Q0) ∧
      (∀ x ∈ feasibleSet Q0 Q, ∀ U W : Matrix (Fin n) (Fin n) ℝ,
        WeakELSDFeasible Q0 Q c U W → c ⬝ᵥ x ≤ frob (U + W) Q0)) ∧
    -- (ii) primal boundedness
    ((feasibleSet Q0 Q).Nonempty →
      (BddAbove (primalValues Q0 Q c) ↔ ∃ U W, ELSDFeasible Q0 Q c U W) ∧
        (BddAbove (primalValues Q0 Q c) ↔ ∃ U W, WeakELSDFeasible Q0 Q c U W)) ∧
    -- (iii) zero gap
    ((feasibleSet Q0 Q).Nonempty →
      ((∃ U W, ELSDFeasible Q0 Q c U W) ∨ (∃ U W, WeakELSDFeasible Q0 Q c U W)) →
      ∃ v : ℝ, IsLUB (primalValues Q0 Q c) v ∧ IsGLB (elsdValues Q0 Q c) v ∧
        IsGLB (weakElsdValues Q0 Q c) v) ∧
    -- (iv) dual attainment
    ((feasibleSet Q0 Q).Nonempty → BddAbove (primalValues Q0 Q c) →
      ∃ v : ℝ, IsLUB (primalValues Q0 Q c) v ∧
        ∃ U W, ELSDFeasible Q0 Q c U W ∧ frob (U + W) Q0 = v) := by
  exact Proof.duality_of_polar_system Proof.polar_system Q0 Q c hQ0 hQ

end ExactSDPDuality.ELSD
-- End RootAssembly

-- Begin Solution

open Matrix ExactSDPDuality.ELSD

theorem solution {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm) :
    -- (i) weak duality
    ((∀ x ∈ feasibleSet Q0 Q, ∀ U W : Matrix (Fin n) (Fin n) ℝ,
        ELSDFeasible Q0 Q c U W → c ⬝ᵥ x ≤ frob (U + W) Q0) ∧
      (∀ x ∈ feasibleSet Q0 Q, ∀ U W : Matrix (Fin n) (Fin n) ℝ,
        WeakELSDFeasible Q0 Q c U W → c ⬝ᵥ x ≤ frob (U + W) Q0)) ∧
    -- (ii) primal boundedness
    ((feasibleSet Q0 Q).Nonempty →
      (BddAbove (primalValues Q0 Q c) ↔ ∃ U W, ELSDFeasible Q0 Q c U W) ∧
        (BddAbove (primalValues Q0 Q c) ↔ ∃ U W, WeakELSDFeasible Q0 Q c U W)) ∧
    -- (iii) zero gap
    ((feasibleSet Q0 Q).Nonempty →
      ((∃ U W, ELSDFeasible Q0 Q c U W) ∨ (∃ U W, WeakELSDFeasible Q0 Q c U W)) →
      ∃ v : ℝ, IsLUB (primalValues Q0 Q c) v ∧ IsGLB (elsdValues Q0 Q c) v ∧
        IsGLB (weakElsdValues Q0 Q c) v) ∧
    -- (iv) dual attainment
    ((feasibleSet Q0 Q).Nonempty → BddAbove (primalValues Q0 Q c) →
      ∃ v : ℝ, IsLUB (primalValues Q0 Q c) v ∧
        ∃ U W, ELSDFeasible Q0 Q c U W ∧ frob (U + W) Q0 = v) := by
  exact ExactSDPDuality.ELSD.duality_theorem Q0 Q c hQ0 hQ

-- End Solution
