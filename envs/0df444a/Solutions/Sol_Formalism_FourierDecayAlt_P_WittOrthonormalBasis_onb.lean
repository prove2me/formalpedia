-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WittOrthonormalBasis.onb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:24:47.284743+00:00
-- url     : https://prove2.me/submissions/b9460b05-55f4-40ba-8efe-879d3f428b53

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WittOrthonormalBasis
import Theorems.Thm_Formalism_FourierDecayAlt_P_WittOrthonormalBasis_mul_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_mem_Uperp
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_gram_independent_signature__beaecb61dd07


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.WittOrthonormalBasis
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector FlagGramRestriction
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.WittOrthonormalBasis
theorem _root_.solution {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {γ : B.Mat k r} (hpos : C2.PosPt k r z z' γ) :
    ∃ Bm : Matrix (Fin (2 * r + k + 1)) (Fin (k - 1) ⊕ Fin 0) ℂ,
      (gnB k r z z' γ)ᴴ * Hpk k r * Bm = 0 ∧ Bmᴴ * Hpk k r * Bm = 1 := by
  classical
  letI : PartialOrder ℂ := Complex.partialOrder
  obtain ⟨-, -, hposU, hfin⟩ := gram_independent_signature' k r z z' γ hstd hpos
  have hH : (Hpk k r)ᴴ = Hpk k r := Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
  let b := Module.finBasisOfFinrankEq ℂ (C2.Uperp k r z z' γ) hfin
  let M : Matrix (Fin (2 * r + k + 1)) (Fin (k - 1)) ℂ :=
    Matrix.of fun i j => (b j : Fin (2 * r + k + 1) → ℂ) i
  have hMv : ∀ x : Fin (k - 1) → ℂ,
      M *ᵥ x = ((∑ j, x j • b j : C2.Uperp k r z z' γ) : Fin (2 * r + k + 1) → ℂ) := by
    intro x
    ext i
    simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hMmem : ∀ x, M *ᵥ x ∈ C2.Uperp k r z z' γ := fun x => by
    rw [hMv]
    exact Submodule.coe_mem _
  have hMne : ∀ x, x ≠ 0 → M *ᵥ x ≠ 0 := by
    intro x hx h
    rw [hMv] at h
    have h' : (∑ j, x j • b j) = 0 := Submodule.coe_eq_zero.mp h
    exact hx (funext (Fintype.linearIndependent_iff.mp b.linearIndependent x h'))
  have key : ∀ x : Fin (k - 1) → ℂ,
      star x ⬝ᵥ ((Mᴴ * Hpk k r * M) *ᵥ x) = herm (Hpk k r) (M *ᵥ x) (M *ᵥ x) := by
    intro x
    rw [herm, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hHerm : (Mᴴ * Hpk k r * M).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH,
      Matrix.mul_assoc]
  have hPD : (Mᴴ * Hpk k r * M).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hHerm (fun x hx => ?_)
    have hre := hposU _ (hMmem x) (hMne x hx)
    have him := hHerm.im_star_dotProduct_mulVec_self x
    rw [key] at him ⊢
    exact Complex.lt_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

  have hspec := hHerm.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  obtain ⟨Uu, hUu⟩ : ∃ U : Matrix (Fin (k - 1)) (Fin (k - 1)) ℂ, U = (hHerm.eigenvectorUnitary : _) := ⟨_, rfl⟩
  have hUU : Uuᴴ * Uu = 1 := by
    rw [hUu, ← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self _
  rw [← hUu, Matrix.star_eq_conjTranspose] at hspec
  let s : Fin (k - 1) → ℂ := fun i => (((Real.sqrt (hHerm.eigenvalues i))⁻¹ : ℝ) : ℂ)
  have hX : (Uu * Matrix.diagonal s)ᴴ * (Mᴴ * Hpk k r * M) * (Uu * Matrix.diagonal s) = 1 := by
    rw [hspec]
    calc (Uu * Matrix.diagonal s)ᴴ * (Uu * Matrix.diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) * Uuᴴ) *
          (Uu * Matrix.diagonal s)
        = (Matrix.diagonal s)ᴴ * (Uuᴴ * Uu) * Matrix.diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) *
            (Uuᴴ * Uu) * Matrix.diagonal s := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by
        rw [hUU, Matrix.mul_one, Matrix.mul_one, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
          Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        have hl : 0 < hHerm.eigenvalues i := hPD.eigenvalues_pos i
        have hsq := Real.mul_self_sqrt hl.le
        have hne : Real.sqrt (hHerm.eigenvalues i) ≠ 0 := (Real.sqrt_pos.mpr hl).ne'
        have hreal : (Real.sqrt (hHerm.eigenvalues i))⁻¹ * hHerm.eigenvalues i *
            (Real.sqrt (hHerm.eigenvalues i))⁻¹ = 1 := by
          rw [mul_right_comm, ← mul_inv, hsq, inv_mul_cancel₀ hl.ne']
        simp only [s, Pi.star_apply, Function.comp_apply, Complex.star_def, Complex.conj_ofReal]
        show (((Real.sqrt (hHerm.eigenvalues i))⁻¹ : ℝ) : ℂ) * ((hHerm.eigenvalues i : ℝ) : ℂ) *
          (((Real.sqrt (hHerm.eigenvalues i))⁻¹ : ℝ) : ℂ) = 1
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hreal, Complex.ofReal_one]
  let Bm0 := M * (Uu * Matrix.diagonal s)
  have hVM : (gnB k r z z' γ)ᴴ * Hpk k r * M = 0 := by
    ext i j
    rw [mul_col]
    have hcol : (fun a => M a j) = ((b j : C2.Uperp k r z z' γ) : Fin (2 * r + k + 1) → ℂ) := by
      funext a
      rfl
    rw [hcol, (mem_Uperp z z' γ _).mp (b j).2]
    rfl
  have h0 : (gnB k r z z' γ)ᴴ * Hpk k r * Bm0 = 0 := by
    simp only [Bm0, ← Matrix.mul_assoc, hVM, Matrix.zero_mul]
  have h1 : Bm0ᴴ * Hpk k r * Bm0 = 1 := by
    rw [← hX]
    simp only [Bm0, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  let e := Equiv.sumEmpty (Fin (k - 1)) (Fin 0)
  refine ⟨Bm0.submatrix id e, ?_, ?_⟩
  · ext i j
    have := congrFun (congrFun h0 i) (e j)
    simpa [Matrix.mul_apply] using this
  · ext i j
    have := congrFun (congrFun h1 (e i)) (e j)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id] at this ⊢
    rw [this]
    simp only [Matrix.one_apply, e.injective.eq_iff]
end Formalism.FourierDecayAlt.P.WittOrthonormalBasis
