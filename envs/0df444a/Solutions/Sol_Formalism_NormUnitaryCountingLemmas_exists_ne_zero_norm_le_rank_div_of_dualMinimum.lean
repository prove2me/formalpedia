-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.exists_ne_zero_norm_le_rank_div_of_dualMinimum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:10:36.431944+00:00
-- url     : https://prove2.me/submissions/7a9860a2-9138-43e9-873b-aeff696aae4e

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqCovolume
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ExistsNeZeroNormLeRankDivOfDualMinimum
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_discreteTopology_of_norm_ge
import Theorems.Thm_Formalism_F_covol_eq_gram
import Theorems.Thm_Formalism_F_gram_sum_smul_eq_transpose_mul
import Theorems.Thm_Formalism_F_shortVector_of
import Theorems.Thm_P2M_Formalism_F_covol_eq_covolume__7dd9eea74b94
import Theorems.Thm_P2M_Formalism_F_covol_pos__b55c804d1109


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.NormUnitaryCountingLemmas
theorem _root_.solution (Q : Submodule ℤ E) [hQd : DiscreteTopology Q] (hQ : Q ≠ ⊥) {l : ℝ}
    (hl : 0 < l)
    (hdual : ∀ y ∈ span ℝ (Q : Set E), y ≠ 0 →
      (∀ x ∈ Q, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖) :
    ∃ q ∈ Q, q ≠ 0 ∧ ‖q‖ ≤ (Formalism.F.rk Q : ℝ) / l := by
  classical
  set k := Module.finrank ℤ Q with hk
  let b := Module.finBasis ℤ Q
  let v : Fin k → E := fun i => (b i : E)
  let G := Matrix.gram ℝ v
  have hcovQ : Formalism.F.covol Q = Real.sqrt G.det := Formalism.F.covol_eq_gram E Q (Fin k) b
  have hpos : 0 < Formalism.F.covol Q := Formalism.F.covol_pos' E Q hQd
  have hdet : 0 < G.det := Real.sqrt_pos.mp (hcovQ ▸ hpos)
  have hdetu : IsUnit G.det := hdet.ne'.isUnit
  let P := G⁻¹
  let w : Fin k → E := fun j => ∑ i, P i j • v i
  have hGP : G * P = 1 := Matrix.mul_nonsing_inv G hdetu
  have hbi : ∀ l j, inner ℝ (v l) (w j) = if l = j then 1 else 0 := by
    intro l j
    have h1 : inner ℝ (v l) (w j) = (G * P) l j := by
      simp only [w, inner_sum, real_inner_smul_right, Matrix.mul_apply, G, Matrix.gram_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [h1, hGP, Matrix.one_apply]
  have hQv : ∀ x ∈ Q, ∃ a : Fin k → ℤ, x = ∑ i, (a i : ℝ) • v i := by
    intro x hx
    refine ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    have h2 : ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : E) = x := h1
    calc x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : E) := h2.symm
      _ = _ := by
        simp only [Int.cast_smul_eq_zsmul, v]
        try rfl
  let D := Submodule.span ℤ (Set.range w)
  have hint : ∀ y ∈ D, ∀ x ∈ Q, ∃ z : ℤ, inner ℝ x y = (z : ℝ) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      intro x hx
      obtain ⟨a, rfl⟩ := hQv x hx
      refine ⟨a j, ?_⟩
      simp only [sum_inner, real_inner_smul_left, hbi]
      simp
    | zero => exact fun x _ => ⟨0, by simp⟩
    | add y y' _ _ h1 h2 =>
      intro x hx
      obtain ⟨z1, e1⟩ := h1 x hx
      obtain ⟨z2, e2⟩ := h2 x hx
      exact ⟨z1 + z2, by rw [inner_add_right, e1, e2]; push_cast; ring⟩
    | smul c y _ h1 =>
      intro x hx
      obtain ⟨z1, e1⟩ := h1 x hx
      exact ⟨c * z1, by rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, e1]; push_cast; ring⟩
  have hDV : ∀ y ∈ D, y ∈ span ℝ (Q : Set E) := by
    intro y hy
    have hle : D ≤ (span ℝ (Q : Set E)).restrictScalars ℤ := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (b i).2))
    exact hle hy
  have hDl : ∀ y ∈ D, y ≠ 0 → l ≤ ‖y‖ := fun y hy hy0 => hdual y (hDV y hy) hy0 (hint y hy)
  have hDd : DiscreteTopology D := discreteTopology_of_norm_ge D hl hDl
  have hli : LinearIndependent ℤ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg l
    have h1 := congrArg (fun y => inner ℝ (v l) y) hg
    simp only [inner_sum, inner_zero_right] at h1
    simp only [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hbi, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
    exact_mod_cast h1
  let bw := Basis.span hli
  have hcovD : Formalism.F.covol D = Real.sqrt (Matrix.gram ℝ w).det := by
    rw [Formalism.F.covol_eq_gram E D (Fin k) bw]
    congr 3
    funext i
    exact congrArg Subtype.val (Basis.span_apply hli i)
  have hgw : Matrix.gram ℝ w = P.transpose * G * P := Formalism.F.gram_sum_smul_eq_transpose_mul v P
  have hdetw : (Matrix.gram ℝ w).det = G.det⁻¹ := by
    rw [hgw, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv']
    field_simp
  have hrkD : Formalism.F.rk D = k := by
    simp only [Formalism.F.rk]
    rw [Module.finrank_eq_card_basis bw, Fintype.card_fin]
  have hrkQ : Formalism.F.rk Q = k := rfl
  have hkpos : 0 < k := by
    have : Nontrivial Q := Submodule.nontrivial_iff_ne_bot.mpr hQ
    exact Module.finrank_pos
  have hD0 : D ≠ ⊥ := by
    intro h
    have hw0 : w ⟨0, hkpos⟩ ∈ D := Submodule.subset_span ⟨_, rfl⟩
    rw [h, Submodule.mem_bot] at hw0
    have h2 := hbi ⟨0, hkpos⟩ ⟨0, hkpos⟩
    rw [hw0, inner_zero_right] at h2
    simp at h2
  obtain ⟨q, hqQ, hq0, hqn⟩ := Formalism.F.shortVector_of Formalism.F.covol_eq_covolume' E Q hQd hQ
  obtain ⟨y, hyD, hy0, hyn⟩ := Formalism.F.shortVector_of Formalism.F.covol_eq_covolume' E D hDd hD0
  refine ⟨q, hqQ, hq0, ?_⟩
  have hly := hDl y hyD hy0
  rw [hrkD, hcovD, hdetw, Real.sqrt_inv, ← hcovQ] at hyn
  rw [hrkQ] at hqn ⊢
  have ht : 0 < Formalism.F.covol Q ^ ((1 : ℝ) / k) := Real.rpow_pos_of_pos hpos _
  rw [Real.inv_rpow hpos.le] at hyn
  have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (Nat.cast_nonneg k)
  have h1 : l * Formalism.F.covol Q ^ ((1 : ℝ) / k) ≤ Real.sqrt k := by
    have h2 := hly.trans hyn
    calc l * Formalism.F.covol Q ^ ((1 : ℝ) / k)
        ≤ Real.sqrt k * (Formalism.F.covol Q ^ ((1 : ℝ) / k))⁻¹ * Formalism.F.covol Q ^ ((1 : ℝ) / k) :=
          mul_le_mul_of_nonneg_right h2 ht.le
      _ = Real.sqrt k := by field_simp
  rw [le_div_iff₀ hl]
  calc ‖q‖ * l ≤ Real.sqrt k * Formalism.F.covol Q ^ ((1 : ℝ) / k) * l :=
        mul_le_mul_of_nonneg_right hqn hl.le
    _ = Real.sqrt k * (l * Formalism.F.covol Q ^ ((1 : ℝ) / k)) := by ring
    _ ≤ Real.sqrt k * Real.sqrt k := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = k := hsk
end Formalism.NormUnitaryCountingLemmas
