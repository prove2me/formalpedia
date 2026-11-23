-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.card_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:57.018949+00:00
-- url     : https://prove2.me/submissions/90a9b291-3753-4f32-8e85-5d7474dbd236

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix
variable {K : Type} [Field K] [Fintype K] [StarRing K]
omit [StarRing K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {n a c : ℕ} (A : Matrix (Fin a) (Fin n) K) (hA : A.rank = a)
    (B : Matrix (Fin a) (Fin c) K) :
    Nat.card {Y : Matrix (Fin n) (Fin c) K // A * Y = B} = Fintype.card K ^ ((n - a) * c) := by
  classical
  have hsurj : Function.Surjective A.mulVec := by
    have h1 : LinearMap.range A.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]; exact hA
    intro y
    have hy : y ∈ LinearMap.range A.mulVecLin := by rw [h1]; trivial
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, by simpa using hx⟩
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1 hsurj
  let φ : Matrix (Fin n) (Fin c) K →ₗ[K] Matrix (Fin a) (Fin c) K :=
    { toFun := fun Y => A * Y
      map_add' := fun x y => Matrix.mul_add A x y
      map_smul' := fun r x => by simp }
  have hφa : ∀ Y, φ Y = A * Y := fun _ => rfl
  have hφ : LinearMap.range φ = ⊤ :=
    LinearMap.range_eq_top.2 (fun Z => ⟨R * Z, by rw [hφa, ← Matrix.mul_assoc, hR, Matrix.one_mul]⟩)
  have hdim := LinearMap.finrank_range_add_finrank_ker φ
  rw [hφ, finrank_top, Module.finrank_matrix, Module.finrank_matrix] at hdim
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hdim
  have hker : Module.finrank K (LinearMap.ker φ) = (n - a) * c := by rw [Nat.sub_mul]; omega
  let e : {Y : Matrix (Fin n) (Fin c) K // A * Y = B} ≃ LinearMap.ker φ :=
    { toFun := fun Y => ⟨Y.1 - R * B, by
        rw [LinearMap.mem_ker, hφa, Matrix.mul_sub, Y.2, ← Matrix.mul_assoc, hR, Matrix.one_mul, sub_self]⟩
      invFun := fun Z => ⟨Z.1 + R * B, by
        have hz : A * Z.1 = 0 := Z.2
        rw [Matrix.mul_add, hz, ← Matrix.mul_assoc, hR, Matrix.one_mul, zero_add]⟩
      left_inv := fun Y => by simp
      right_inv := fun Z => by simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), hker]
end Formalism.FourierDecayAlt.P.S3x5
