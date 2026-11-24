-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.ddNe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:35:24.967022+00:00
-- url     : https://prove2.me/submissions/cc440e08-daae-4a4e-a666-076ae366e983

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_CompanionTheory_ThKR_Mp_sp_rel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution : DdNe l := by
  intro s
  let N : Matrix l (l ⊕ l) ℝ := Matrix.of fun a k => s.1 (.inl a) k
  let K : Matrix (l ⊕ l) l ℝ := Matrix.of fun k b =>
    Sum.elim (fun c => s.1 (.inr b) (.inr c)) (fun c => -s.1 (.inr b) (.inl c)) k
  have hNK : N * K = 1 := by
    ext a b
    have h := sp_rel s (.inl a) (.inr b)
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [N, K, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    calc _ = -∑ c, (s.1 (.inl a) (.inr c) * s.1 (.inr b) (.inl c) - s.1 (.inl a) (.inl c) * s.1 (.inr b) (.inr c)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ = _ := by rw [h]; simp [Matrix.J, Matrix.one_apply]
  have hM : (N * Nᵀ).det ≠ 0 := by
    intro hd
    obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    have h1 : (v ᵥ* N) ⬝ᵥ (v ᵥ* N) = 0 := by
      have : (v ᵥ* (N * Nᵀ)) ⬝ᵥ v = 0 := by rw [hvM, zero_dotProduct]
      rwa [← Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_transpose] at this
    have h2 : v ᵥ* N = 0 := dotProduct_self_eq_zero.1 h1
    apply hv
    calc v = v ᵥ* (N * K) := by rw [hNK, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, h2, Matrix.zero_vecMul]
  let W : Matrix l l ℂ := Matrix.of fun c b => (s.1 (.inl b) (.inl c) : ℂ) + I * s.1 (.inl b) (.inr c)
  have hPW : upperParabolic s.1 * W = (N * Nᵀ).map ofReal := by
    ext a b
    have hs := sp_rel s (.inl a) (.inl b)
    simp only [Matrix.J, fromBlocks_apply₁₁, Matrix.zero_apply] at hs
    have e : ∀ c, ((s.1 (.inl a) (.inl c) : ℂ) - I * s.1 (.inl a) (.inr c)) *
        ((s.1 (.inl b) (.inl c) : ℂ) + I * s.1 (.inl b) (.inr c)) =
        ((s.1 (.inl a) (.inl c) * s.1 (.inl b) (.inl c) + s.1 (.inl a) (.inr c) * s.1 (.inl b) (.inr c) : ℝ) : ℂ) -
        I * ((s.1 (.inl a) (.inr c) * s.1 (.inl b) (.inl c) - s.1 (.inl a) (.inl c) * s.1 (.inl b) (.inr c) : ℝ) : ℂ) :=
      fun c => by
        push_cast
        linear_combination (-((s.1 (.inl a) (.inr c) : ℂ) * (s.1 (.inl b) (.inr c) : ℂ))) * I_sq
    simp only [Matrix.mul_apply, upperParabolic, W, Matrix.of_apply, Matrix.map_apply, N, Matrix.transpose_apply,
      Fintype.sum_sum_type]
    rw [Finset.sum_congr rfl fun c _ => e c, Finset.sum_sub_distrib, ← Finset.mul_sum, ← ofReal_sum, ← ofReal_sum, hs]
    push_cast
    rw [Finset.sum_add_distrib]
    simp
  have e : ((N * Nᵀ).map ofReal).det = ((N * Nᵀ).det : ℂ) := by
    rw [show (N * Nᵀ).map ofReal = ofRealHom.mapMatrix (N * Nᵀ) from rfl, ← RingHom.map_det]
    rfl
  intro h0
  have := congrArg Matrix.det hPW
  rw [Matrix.det_mul, e] at this
  unfold dd at h0
  rw [h0, zero_mul] at this
  exact hM (ofReal_eq_zero.1 this.symm)
end CompanionTheory.ThKR.Mp
