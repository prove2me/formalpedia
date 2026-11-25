-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.block3_apply_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:58:02.397189+00:00
-- url     : https://prove2.me/submissions/84df546a-b015-4784-97ea-8e44b452518d

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_wMat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_Hpk
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_mx_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_det_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_inv_entry_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_aux_statement_16
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_block3_mul_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_eq_block3_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_entry_bound_block3
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_det_Rn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_gN_le_of_EB
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_bk
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_wMat_mul_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_mul_w_w
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_skew_ct
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_beta_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mulF
import Theorems.Thm_Formalism_QuantumDeterminants_hermitian_pos_facts_hold


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
set_option maxHeartbeats 1000000
namespace Formalism.FourierDecayAlt.P.Ux5
namespace _root_.Formalism.FourierDecayAlt.P
theorem _root_.solution : BigCellCoordinateSizes := by
  intro k j ρ hj
  have hj0 : j ≠ 0 := by omega
  obtain ⟨A0, hA0⟩ : ∃ A0 : ℝ, A0 = (j.factorial : ℝ) * (j : ℝ) ^ j := ⟨_, rfl⟩
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, K0 = ((j - 1).factorial : ℝ) * (j : ℝ) ^ (j - 1) := ⟨_, rfl⟩
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ, K2 = (j : ℝ) ^ 2 * K0 := ⟨_, rfl⟩
  obtain ⟨Nr, hNr⟩ : ∃ Nr : ℝ, Nr = ((2 * ρ + k + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨nr, hnr⟩ : ∃ nr : ℝ, nr = ((2 * (j + ρ) + k + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = Nr * (j : ℝ) + (j : ℝ) ^ 2 + 1 := ⟨_, rfl⟩
  have hA00 : 0 ≤ A0 := by rw [hA0]; positivity
  have hK00 : 0 ≤ K0 := by rw [hK0]; positivity
  have hK20 : 0 ≤ K2 := by rw [hK2]; positivity
  have hNr0 : 0 ≤ Nr := by rw [hNr]; positivity
  have hnr0 : 0 ≤ nr := by rw [hnr]; positivity
  have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
  have hjr0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = nr * (A0 + K1 * K2) + (j : ℝ) + K0 + Nr * (A0 ^ 2 + (j : ℝ) * K2 * A0) :=
    ⟨_, rfl⟩
  have hCa : nr * (A0 + K1 * K2) ≤ C := by
    rw [hC]; have : 0 ≤ Nr * (A0 ^ 2 + (j : ℝ) * K2 * A0) := by positivity
    linarith
  have hCb : (j : ℝ) ≤ C := by
    rw [hC]; have : 0 ≤ Nr * (A0 ^ 2 + (j : ℝ) * K2 * A0) := by positivity
    have : 0 ≤ nr * (A0 + K1 * K2) := by positivity
    linarith
  have hCc : K0 ≤ C := by
    rw [hC]; have : 0 ≤ Nr * (A0 ^ 2 + (j : ℝ) * K2 * A0) := by positivity
    have : 0 ≤ nr * (A0 + K1 * K2) := by positivity
    linarith
  have hCd : Nr * (A0 ^ 2 + (j : ℝ) * K2 * A0) ≤ C := by
    rw [hC]; have : 0 ≤ nr * (A0 + K1 * K2) := by positivity
    linarith
  refine ⟨C, ?_⟩
  intro x x' Z γ hZ _hγ
  obtain ⟨hHct, hHH, -⟩ := hermitian_pos_facts_hold k ρ
  set w := G.wMat j with hw
  set H := Hpk k ρ with hH
  set c := Matrix.of x.1 with hc
  set S := skewOf x.2 with hS
  set α := -(w * cᴴ * H) with hα
  set β := w * ((-(1 / 2 : ℂ)) • (cᴴ * H * c) + S) with hβ
  set c' := Matrix.of x'.1 with hc'
  set α' := -(w * c'ᴴ * H) with hα'
  set β' := w * ((-(1 / 2 : ℂ)) • (c'ᴴ * H * c') + skewOf x'.2) with hβ'
  have hRn : Rn k j ρ x = blk3 1 α β 0 1 c 0 0 1 := rfl
  have hRn' : Rn k j ρ x' = blk3 1 α' β' 0 1 c' 0 0 1 := rfl
  have hmM : mMap k j ρ Z γ = blk3 0 0 (Zᴴ⁻¹ * w) 0 γ 0 (w * Z) 0 0 := rfl
  set g := (Rn k j ρ x)⁻¹ * mMap k j ρ Z γ * Rn k j ρ x' with hg
  set g' := B.gN g with hg'
  have hg'0 : 0 ≤ g' := Real.sqrt_nonneg _
  have key : Rn k j ρ x * g = mMap k j ρ Z γ * Rn k j ρ x' := by
    rw [hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (by rw [det_Rn]; exact isUnit_one),
      Matrix.one_mul]
  set FourierUniquenessMirabolic := bk g (q1 k ρ) (q1 k ρ) with hG11
  set WeakApproximationGL := bk g (q1 k ρ) (q2 k j) with hG12
  set WhittakerVanishingImpliesZero := bk g (q1 k ρ) (q3 k ρ) with hG13
  set G21 := bk g (q2 k j) (q1 k ρ) with hG21
  set G22 := bk g (q2 k j) (q2 k j) with hG22
  set G23 := bk g (q2 k j) (q3 k ρ) with hG23
  set G31 := bk g (q3 k ρ) (q1 k ρ) with hG31
  set ContDiffOnLocalExtension := bk g (q3 k ρ) (q2 k j) with hG32
  set G33 := bk g (q3 k ρ) (q3 k ρ) with hG33
  have key2 := key
  rw [eq_block3_of_blocks g, hRn, hRn', hmM, block3_mul_blocks, block3_mul_blocks] at key2
  have ex : ∀ a b : Ix k j ρ, _ := fun a b => congrFun (congrFun key2 (eB k j ρ a)) (eB k j ρ b)
  have E31 : G31 = w * Z := by
    ext a b
    have := ex (q3 k ρ a) (q1 k ρ b)
    simpa [aux_statement_16, q1, q3] using this
  have E32 : ContDiffOnLocalExtension = w * Z * α' := by
    ext a b
    have := ex (q3 k ρ a) (q2 k j b)
    simpa [aux_statement_16, q2, q3] using this
  have E33 : G33 = w * Z * β' := by
    ext a b
    have := ex (q3 k ρ a) (q3 k ρ b)
    simpa [aux_statement_16, q3] using this
  have E21 : G21 + c * G31 = 0 := by
    ext a b
    have := ex (q2 k j a) (q1 k ρ b)
    simpa [aux_statement_16, q1, q2] using this
  have E22 : G22 + c * ContDiffOnLocalExtension = γ := by
    ext a b
    have := ex (q2 k j a) (q2 k j b)
    simpa [aux_statement_16, q2] using this
  have E11 : FourierUniquenessMirabolic + α * G21 + β * G31 = 0 := by
    ext a b
    have := ex (q1 k ρ a) (q1 k ρ b)
    simpa [aux_statement_16, q1] using this

  have hZu : IsUnit Z.det := isUnit_iff_ne_zero.mpr hZ
  set W := Z⁻¹ * w with hW
  have hνW : w * Z * W = 1 := by
    rw [hW, Matrix.mul_assoc, ← Matrix.mul_assoc Z, mul_nonsing_inv _ hZu, Matrix.one_mul, hw, wMat_mul_self]
  have hWν : W * (w * Z) = 1 := by
    rw [hW, Matrix.mul_assoc, ← Matrix.mul_assoc w, hw, wMat_mul_self, Matrix.one_mul, nonsing_inv_mul _ hZu]
  have hα'W : α' = W * ContDiffOnLocalExtension := by
    rw [E32, ← Matrix.mul_assoc, hWν, Matrix.one_mul]
  have hβ'W : β' = W * G33 := by
    rw [E33, ← Matrix.mul_assoc, hWν, Matrix.one_mul]
  have hG21' : G21 = -(c * (w * Z)) := by
    rw [← E31]
    exact eq_neg_of_add_eq_zero_left E21
  have hcW : c = -(G21 * W) := by
    rw [hG21', Matrix.neg_mul, neg_neg, Matrix.mul_assoc, hνW, Matrix.mul_one]
  have hTW : β - α * c = -(FourierUniquenessMirabolic * W) := by
    have e1 : FourierUniquenessMirabolic = (α * c - β) * (w * Z) := by
      have e := E11
      rw [hG21', E31] at e
      calc FourierUniquenessMirabolic = (FourierUniquenessMirabolic + α * -(c * (w * Z)) + β * (w * Z)) + (α * (c * (w * Z)) - β * (w * Z)) := by
            rw [Matrix.mul_neg]; abel
        _ = (α * c - β) * (w * Z) := by rw [e, zero_add, Matrix.sub_mul, Matrix.mul_assoc α c]
    rw [e1, Matrix.mul_assoc, hνW, Matrix.mul_one, neg_sub]
  have hβT : β = -(w * (β - α * c)ᴴ * w) := beta_id H c S hHct (skew_ct x.2)
  have hc'α : c' = -(w * α' * H)ᴴ := by
    have e : w * α' * H = -c'ᴴ := by
      rw [hα', Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, hHH,
        Matrix.mul_one, ← Matrix.mul_assoc w w, hw, wMat_mul_self, Matrix.one_mul]
    rw [e, conjTranspose_neg, conjTranspose_conjTranspose, neg_neg]
  have hγG : γ = G22 + c * ContDiffOnLocalExtension := E22.symm

  have hZw : Z = w * G31 := by rw [E31, hw, mul_w_w]
  have hZb : EB Z ((j : ℝ) * g') := by
    rw [hZw]
    exact (EB_mulF (EB_wMat j) (EB_bk g (q3 k ρ) (q1 k ρ))).mono (le_of_eq (by ring))
  set δ := ‖Z.det‖ with hδ
  have hδ0 : 0 < δ := norm_pos_iff.mpr hZ
  have hδle : δ ≤ A0 * g' ^ j := by
    have := det_norm_le Z hZb
    rw [Fintype.card_fin, mul_pow] at this
    rw [hA0]
    linarith
  obtain ⟨ζ0, hζ0⟩ : ∃ ζ0 : ℝ, ζ0 = ((j - 1).factorial : ℝ) * ((j : ℝ) * g') ^ (j - 1) / δ := ⟨_, rfl⟩
  have hζ00 : 0 ≤ ζ0 := by rw [hζ0]; positivity
  have hZib : EB Z⁻¹ ζ0 := by
    have := inv_entry_le Z hZb
    rwa [← hζ0] at this
  have hWb : EB W ((j : ℝ) * ζ0) := (EB_mulF hZib (EB_wMat j)).mono (le_of_eq (by ring))
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (j : ℝ) ^ 2 * ζ0 * g' := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hα'b : EB α' Y := by
    rw [hα'W]
    exact (EB_mulF hWb (EB_bk g (q3 k ρ) (q2 k j))).mono (le_of_eq (by rw [hY]; ring))
  have hβ'b : EB β' Y := by
    rw [hβ'W]
    exact (EB_mulF hWb (EB_bk g (q3 k ρ) (q3 k ρ))).mono (le_of_eq (by rw [hY]; ring))
  have hcb : EB c Y := by
    rw [hcW]
    exact (EB_neg (EB_mulF (EB_bk g (q2 k j) (q1 k ρ)) hWb)).mono (le_of_eq (by rw [hY]; ring))
  have hTb : EB (β - α * c) Y := by
    rw [hTW]
    exact (EB_neg (EB_mulF (EB_bk g (q1 k ρ) (q1 k ρ)) hWb)).mono (le_of_eq (by rw [hY]; ring))
  have hβb : EB β ((j : ℝ) ^ 2 * Y) := by
    rw [hβT]
    exact (EB_neg (EB_mulF (EB_mulF (EB_wMat j) (EB_conjTranspose hTb)) (EB_wMat j))).mono
      (le_of_eq (by ring))
  have hαb : EB α (Nr * (j : ℝ) * Y) := by
    rw [hα]
    exact (EB_neg (EB_mulF (EB_mulF (EB_wMat j) (EB_conjTranspose hcb)) (EB_Hpk k ρ))).mono
      (le_of_eq (by rw [hNr]; ring))
  have hc'b : EB c' (Nr * (j : ℝ) * Y) := by
    rw [hc'α]
    exact (EB_neg (EB_conjTranspose (EB_mulF (EB_mulF (EB_wMat j) hα'b) (EB_Hpk k ρ)))).mono
      (le_of_eq (by rw [hNr]; ring))
  have hγb : EB γ (g' + (j : ℝ) * (Y * g')) := by
    rw [hγG]
    exact EB_add (EB_bk g (q2 k j) (q2 k j)) (EB_mulF hcb (EB_bk g (q3 k ρ) (q2 k j)))

  have hB1 : (1 : ℝ) ≤ 1 + K1 * Y := le_add_of_nonneg_right (mul_nonneg hK10 hY0)
  have hK1Y : K1 * Y = Nr * (j : ℝ) * Y + (j : ℝ) ^ 2 * Y + Y := by rw [hK1]; ring
  have hp1 : 0 ≤ Nr * (j : ℝ) * Y := by positivity
  have hp2 : 0 ≤ (j : ℝ) ^ 2 * Y := by positivity
  have hnb : EB (Rn k j ρ x) (1 + K1 * Y) := by
    rw [hRn]
    refine entry_bound_block3 (EB_one.mono hB1) (hαb.mono ?_) (hβb.mono ?_) (EB_zero.mono (by linarith))
      (EB_one.mono hB1) (hcb.mono ?_) (EB_zero.mono (by linarith)) (EB_zero.mono (by linarith)) (EB_one.mono hB1)
    · rw [hK1Y]; linarith
    · rw [hK1Y]; linarith
    · rw [hK1Y]; linarith
  have hn'b : EB (Rn k j ρ x') (1 + K1 * Y) := by
    rw [hRn']
    refine entry_bound_block3 (EB_one.mono hB1) (hα'b.mono ?_) (hβ'b.mono ?_) (EB_zero.mono (by linarith))
      (EB_one.mono hB1) (hc'b.mono ?_) (EB_zero.mono (by linarith)) (EB_zero.mono (by linarith)) (EB_one.mono hB1)
    · rw [hK1Y]; linarith
    · rw [hK1Y]; linarith
    · rw [hK1Y]; linarith

  have hYg : Y = K2 * (g' ^ j / δ) := by
    rw [hY, hζ0, hK2, hK0, mul_pow, ← pow_sub_one_mul hj0 g']
    field_simp
  set μ := min 1 δ with hμ
  have hμ0 : 0 < μ := lt_min one_pos hδ0
  have hμδ : μ ≤ δ := min_le_right _ _
  have hgj0 : 0 ≤ g' ^ j := pow_nonneg hg'0 j
  set R := g' ^ j / μ with hR
  have hR0 : 0 ≤ R := by positivity
  have hQR : g' ^ j / δ ≤ R := div_le_div_of_nonneg_left hgj0 hμ0 hμδ
  have hA0R : 1 ≤ A0 * R := by
    rw [hR, mul_div_assoc', le_div_iff₀ hμ0]
    linarith
  have hYR : Y ≤ K2 * R := by rw [hYg]; exact mul_le_mul_of_nonneg_left hQR hK20
  have hRn_le : ∀ M : B.Mat k (j + ρ), EB M (1 + K1 * Y) → B.gN M ≤ C * g' ^ j / μ := by
    intro M hM
    have h1 := gN_le_of_EB M hM (by linarith)
    rw [← hnr] at h1
    calc B.gN M ≤ nr * (1 + K1 * Y) := h1
      _ ≤ nr * (A0 * R + K1 * (K2 * R)) := by
          apply mul_le_mul_of_nonneg_left _ hnr0
          have := mul_le_mul_of_nonneg_left hYR hK10
          linarith
      _ = nr * (A0 + K1 * K2) * R := by ring
      _ ≤ C * R := mul_le_mul_of_nonneg_right hCa hR0
      _ = C * g' ^ j / μ := by rw [hR, mul_div_assoc]
  refine ⟨hRn_le _ hnb, hRn_le _ hn'b, ?_, ?_, ?_⟩
  ·
    exact (mx_le hZb (by positivity)).trans (mul_le_mul_of_nonneg_right hCb hg'0)
  ·
    refine (mx_le hZib hζ00).trans ?_
    rw [hζ0, mul_pow]
    have : ((j - 1).factorial : ℝ) * ((j : ℝ) ^ (j - 1) * g' ^ (j - 1)) = K0 * g' ^ (j - 1) := by
      rw [hK0]; ring
    rw [this]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCc (by positivity)) hδ0.le
  ·
    have h1 := gN_le_of_EB γ hγb (by positivity)
    rw [← hNr] at h1
    have hsq : 1 ≤ (A0 * R) ^ 2 := one_le_pow₀ hA0R
    have e1 : g' ≤ A0 ^ 2 * (g' * R ^ 2) := by
      have := mul_le_mul_of_nonneg_left hsq hg'0
      nlinarith
    have e2 : (j : ℝ) * (Y * g') ≤ (j : ℝ) * K2 * A0 * (g' * R ^ 2) := by
      have h3 : Y * g' ≤ K2 * R * g' := mul_le_mul_of_nonneg_right hYR hg'0
      have h4 : K2 * R * g' ≤ K2 * R * g' * (A0 * R) := le_mul_of_one_le_right (by positivity) hA0R
      have h5 : (j : ℝ) * (Y * g') ≤ (j : ℝ) * (K2 * R * g' * (A0 * R)) :=
        mul_le_mul_of_nonneg_left (h3.trans h4) hjr0
      calc (j : ℝ) * (Y * g') ≤ (j : ℝ) * (K2 * R * g' * (A0 * R)) := h5
        _ = (j : ℝ) * K2 * A0 * (g' * R ^ 2) := by ring
    have e3 : g' * R ^ 2 = g' ^ (2 * j + 1) / μ ^ 2 := by
      rw [hR, div_pow, ← pow_mul, pow_succ]
      ring
    calc B.gN γ ≤ Nr * (g' + (j : ℝ) * (Y * g')) := h1
      _ ≤ Nr * (A0 ^ 2 * (g' * R ^ 2) + (j : ℝ) * K2 * A0 * (g' * R ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hNr0
          linarith
      _ = Nr * (A0 ^ 2 + (j : ℝ) * K2 * A0) * (g' * R ^ 2) := by ring
      _ ≤ C * (g' * R ^ 2) := mul_le_mul_of_nonneg_right hCd (by positivity)
      _ = C * g' ^ (2 * j + 1) / μ ^ 2 := by rw [e3, mul_div_assoc]
end _root_.Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P.Ux5
