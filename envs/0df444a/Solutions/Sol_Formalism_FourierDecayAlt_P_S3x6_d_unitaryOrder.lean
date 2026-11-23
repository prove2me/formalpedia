-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.d_unitaryOrder
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:24.331801+00:00
-- url     : https://prove2.me/submissions/f87b192b-6524-48ed-a6f2-cfd89b759621

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_exists_orthonormal
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_card_frames
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_exists_sigma
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_card_norm_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_gram_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_fconj_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_fconj_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_nondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_arith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
open Matrix Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution : UnitaryOrder := by
  intro K _ _ q b J hq hJh hJu
  obtain ⟨σ, hσ, hi⟩ := exists_sigma K q hq
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h
      have := Fintype.card_pos (α := K)
      omega
    · exact h
  have hH := d_herm hσ hi J hJh
  have hN : Nondeg (hJ σ J) := d_nondeg J hJu
  obtain ⟨bs, hbs⟩ := exists_orthonormal hi b (Fin b → K) (hJ σ J) hH hN (by simp)
  set P : Matrix (Fin b) (Fin b) K := Matrix.of fun k i => bs i k with hP
  have hPJ : fconj q P * J * P = 1 := by
    ext i j
    rw [d_gram_entry hσ, Matrix.one_apply]
    exact hbs i j
  have hPu : IsUnit P.det := by
    have := congrArg Matrix.det hPJ
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact this)
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  have hJP : J = fconj q P⁻¹ * P⁻¹ := by
    calc J = fconj q (P * P⁻¹) * J * (P * P⁻¹) := by rw [hPP, d_fconj_one hσ]; simp
      _ = fconj q P⁻¹ * (fconj q P * J * P) * P⁻¹ := by
          rw [d_fconj_mul hσ]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPJ]; simp
  let e1 : {g : Matrix (Fin b) (Fin b) K // fconj q g * J * g = J} ≃
      {Z : Matrix (Fin b) (Fin b) K // fconj q Z * J * Z = 1} :=
    { toFun := fun g => ⟨g.1 * P, by
        rw [d_fconj_mul hσ]
        calc fconj q P * fconj q g.1 * J * (g.1 * P) = fconj q P * (fconj q g.1 * J * g.1) * P := by
              simp only [Matrix.mul_assoc]
          _ = 1 := by rw [g.2, hPJ]⟩
      invFun := fun Z => ⟨Z.1 * P⁻¹, by
        rw [d_fconj_mul hσ]
        calc fconj q P⁻¹ * fconj q Z.1 * J * (Z.1 * P⁻¹)
            = fconj q P⁻¹ * (fconj q Z.1 * J * Z.1) * P⁻¹ := by simp only [Matrix.mul_assoc]
          _ = J := by rw [Z.2, hJP]; simp⟩
      left_inv := fun g => by
        apply Subtype.ext
        simp [Matrix.mul_assoc, hPP]
      right_inv := fun Z => by
        apply Subtype.ext
        simp [Matrix.mul_assoc, hPP'] }
  let e2 : {Z : Matrix (Fin b) (Fin b) K // fconj q Z * J * Z = 1} ≃
      {f : Fin b → (Fin b → K) // Ortho (hJ σ J) f} :=
    { toFun := fun Z => ⟨fun i k => Z.1 k i, by
        intro i j
        rw [← d_gram_entry hσ, Z.2, Matrix.one_apply]⟩
      invFun := fun f => ⟨Matrix.of fun k i => f.1 i k, by
        ext i j
        rw [d_gram_entry hσ, Matrix.one_apply]
        exact f.2 i j⟩
      left_inv := fun Z => rfl
      right_inv := fun f => rfl }
  rw [Nat.card_congr (e1.trans e2),
    card_frames hi (fun n => Nat.card {w : Fin n → K // ∑ i, σ (w i) * w i = 1}) (fun _ => rfl) b
      (Fin b → K) (hJ σ J) hH hN (by simp)]
  refine d_arith q hq0 (fun n => Nat.card {w : Fin n → K // ∑ i, σ (w i) * w i = 1}) ?_ b
  intro n
  have := card_norm_one K q hq n
  simpa only [hσ] using this
end Formalism.FourierDecayAlt.P.S3x6
