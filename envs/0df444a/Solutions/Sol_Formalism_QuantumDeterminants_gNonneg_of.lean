-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gNonneg_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:56:33.134644+00:00
-- url     : https://prove2.me/submissions/e47733e9-8da0-4013-b290-2cc5dd83742e

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
import Theorems.Thm_Formalism_QuantumDeterminants_gn_card_le_of_ker
import Theorems.Thm_Formalism_QuantumDeterminants_gn_quad_eig
import Theorems.Thm_Formalism_QuantumDeterminants_gn_herm_nonneg
import Theorems.Thm_Formalism_QuantumDeterminants_gn_gramM_herm
import Theorems.Thm_Formalism_QuantumDeterminants_gn_quad_B
import Theorems.Thm_Formalism_QuantumDeterminants_gn_quad_inl
import Theorems.Thm_Formalism_QuantumDeterminants_gn_sum_neg
import Theorems.Thm_Formalism_QuantumDeterminants_gn_sum_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution (h : GGram) : GNonneg := by
  intro k r z z' hz hz' hT _hT' g hg
  have hG := h k r z z' hz hz' g hg
  have hM := gn_gramM_herm k r z z' g
  rw [hM.det_eq_prod_eigenvalues] at hG
  have hzz : (herm (Hpk k r) z z).re ≤ 0 := by
    unfold Tz at hT
    linarith
  by_cases h0 : ∃ i, hM.eigenvalues i = 0
  · obtain ⟨i, hi⟩ := h0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi]; simp), mul_zero] at hG
    have : Gf k r z z' g = 0 := by exact_mod_cast hG
    rw [this]
  · push Not at h0
    have hneg : Fintype.card {i // hM.eigenvalues i < 0} ≤ r + 1 := by
      refine gn_card_le_of_ker ((gnPi k r).comp
        (gnB k r z z' g * (hM.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *
          gnExt (fun i => hM.eigenvalues i < 0)).mulVecLin) ?_
      intro v hv
      by_contra hv0
      obtain ⟨y, hy⟩ : ∃ y, y = gnB k r z z' g *ᵥ ((hM.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *ᵥ
          (gnExt (fun i => hM.eigenvalues i < 0) *ᵥ v)) := ⟨_, rfl⟩
      have hyv : (gnB k r z z' g * (hM.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *
          gnExt (fun i => hM.eigenvalues i < 0)) *ᵥ v = y := by
        rw [hy, mulVec_mulVec, mulVec_mulVec]
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, hyv] at hv
      have h1 : ∀ a : Fin r, y (eI k r a) = y (esI k r a) := by
        intro a
        have := congrFun hv ⟨a.val, by omega⟩
        simpa [gnPi, a.isLt, sub_eq_zero] using this
      have h2 : y ⟨r + k, by omega⟩ = 0 := by
        have := congrFun hv (Fin.last r)
        simpa [gnPi] using this
      have hpos := gn_herm_nonneg k r y h1 h2
      rw [hy, ← gn_quad_B, gn_quad_eig hM] at hpos
      have := gn_sum_neg hM.eigenvalues v hv0
      simp only [Complex.re_sum, Complex.ofReal_re] at hpos
      linarith
    have hposc : Fintype.card {i // 0 < hM.eigenvalues i} ≤ r + 1 := by
      refine gn_card_le_of_ker ((((hM.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *
          gnExt (fun i => 0 < hM.eigenvalues i)).submatrix Sum.inr id).mulVecLin) ?_
      intro v hv
      by_contra hv0
      obtain ⟨c, hc⟩ : ∃ c, c = (hM.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *ᵥ
          (gnExt (fun i => 0 < hM.eigenvalues i) *ᵥ v) := ⟨_, rfl⟩
      have hci : ∀ b, c (Sum.inr b) = 0 := by
        intro b
        have := congrFun hv b
        rw [hc, mulVec_mulVec]
        simpa [mulVec, dotProduct] using this
      have hq := gn_quad_inl k r z z' g hz hzz c hci
      rw [hc, gn_quad_eig hM] at hq
      have := gn_sum_pos hM.eigenvalues v hv0
      simp only [Complex.re_sum, Complex.ofReal_re] at hq
      linarith
    have hsum : Fintype.card {i // hM.eigenvalues i < 0} +
        Fintype.card {i // 0 < hM.eigenvalues i} = 2 * r + 2 := by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      have : (Finset.univ.filter fun i => 0 < hM.eigenvalues i) =
          Finset.univ.filter fun i => ¬ (hM.eigenvalues i < 0) := by
        apply Finset.filter_congr
        intro i _
        constructor
        · intro h
          linarith
        · intro h
          exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm (h0 i))
      rw [this, Finset.card_filter_add_card_filter_not]
      simp
      omega
    have hcard : (Finset.univ.filter fun i => hM.eigenvalues i < 0).card = r + 1 := by
      rw [← Fintype.card_subtype]
      omega
    have key : Gf k r z z' g = (-1) ^ (r + 1) * ∏ j, hM.eigenvalues j := by
      apply Complex.ofReal_injective
      rw [hG]
      push_cast
      rfl
    have e : ∀ j, hM.eigenvalues j =
        (if hM.eigenvalues j < 0 then (-1 : ℝ) else 1) * |hM.eigenvalues j| := by
      intro j
      split_ifs with hj
      · rw [abs_of_neg hj]
        ring
      · rw [abs_of_nonneg (not_lt.mp hj)]
        ring
    have hprod : ∏ j, hM.eigenvalues j = (-1) ^ (r + 1) * ∏ j, |hM.eigenvalues j| := by
      calc ∏ j, hM.eigenvalues j
          = ∏ j, ((if hM.eigenvalues j < 0 then (-1 : ℝ) else 1) * |hM.eigenvalues j|) :=
            Finset.prod_congr rfl (fun j _ => e j)
        _ = (-1) ^ (r + 1) * ∏ j, |hM.eigenvalues j| := by
            rw [Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
              mul_one, hcard]
    rw [key, hprod, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    norm_num
    positivity
end Formalism.QuantumDeterminants
