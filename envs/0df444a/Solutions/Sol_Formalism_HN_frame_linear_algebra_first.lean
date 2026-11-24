-- Prove2me | solution 1 for Formalism.HN.frame_linear_algebra_first
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:19.664442+00:00
-- url     : https://prove2.me/submissions/52259708-ad4e-4201-9c7d-97bf204ae4a1

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementFrameF
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameLinearAlgebraFirst
import Theorems.Thm_Formalism_HN_PframeLA1_final_real1
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_W_upper
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_fam_bound
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_hilbert_schmidt_eq_basis_sum
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_re_inner_Q
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_sum_re_inner_bound
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_tQ_eq
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_trace_frame_sq_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.HN
namespace PframeLA1
open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
open scoped InnerProductSpace
end PframeLA1
open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.CorankShareLayerCake.FR.Pgsn2pfrla PframeLA1
open scoped InnerProductSpace
private lemma hs2_nonneg {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : E →ₗ[ℂ] F) : 0 ≤ hs2 A := by
  rw [hilbert_schmidt_eq_basis_sum A (stdOrthonormalBasis ℂ E)]
  exact Finset.sum_nonneg (fun m _ => sq_nonneg _)
end Formalism.HN
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HN
open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.CorankShareLayerCake.FR.Pgsn2pfrla PframeLA1
open scoped InnerProductSpace
namespace Formalism.HN
theorem _root_.solution : FrameLA1 := by
  intro ι _ V _ _ _ H _ _ _ B c Nτ e η ε hc hd hK he0 he hη hQ hN
  set W : Submodule ℂ H := (⨆ i, (Nτ i).map (B i))ᗮ with hW
  have hwD : (finrank ℂ W : ℝ) ≤ (finrank ℂ H : ℝ) := by exact_mod_cast Submodule.finrank_le W
  by_cases hD0 : finrank ℂ H = 0
  · have h0 : finrank ℂ W = 0 := by have := Submodule.finrank_le W; omega
    simp [h0, hD0]
  have hD : 0 < (finrank ℂ H : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hD0
  have hR : 0 < ∑ i, (finrank ℂ (V i) : ℝ) := by rw [← Nat.cast_sum]; exact_mod_cast hd
  have hnk : ∀ i, (finrank ℂ (Nτ i) : ℝ) ≤ finrank ℂ (V i) := fun i => by
    exact_mod_cast Submodule.finrank_le (Nτ i)
  have hKnn : 0 ≤ ∑ i, ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) :=
    Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hnk i))
  have hε : 0 ≤ ε := by
    by_contra h
    push_neg at h
    have : ε * ∑ i, (finrank ℂ (V i) : ℝ) < 0 := mul_neg_of_neg_of_pos h hR
    linarith

  have hfull : ∀ i, (finrank ℂ (V i) : ℝ) - √(finrank ℂ (V i) : ℝ) * √(hs2 (frK (c i) (B i) - LinearMap.id))
      ≤ c i * ∑ m, ‖B i (stdOrthonormalBasis ℂ (V i) m)‖ ^ 2 := by
    intro i
    have h := fam_bound (c i) (B i) (stdOrthonormalBasis ℂ (V i)).orthonormal
    simp only [Fintype.card_fin] at h
    have := (abs_le.mp h).1
    linarith
  have hCS1 : ∑ i, √(finrank ℂ (V i) : ℝ) * √(hs2 (frK (c i) (B i) - LinearMap.id))
      ≤ (∑ i, (finrank ℂ (V i) : ℝ)) * √e := by
    calc _ ≤ √(∑ i, (finrank ℂ (V i) : ℝ)) * √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) :=
          Real.sum_sqrt_mul_sqrt_le Finset.univ (fun i => Nat.cast_nonneg _) (fun i => hs2_nonneg _)
      _ ≤ √(∑ i, (finrank ℂ (V i) : ℝ)) * √(e * ∑ i, (finrank ℂ (V i) : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hK) (Real.sqrt_nonneg _)
      _ = (∑ i, (finrank ℂ (V i) : ℝ)) * √e := by
          rw [Real.sqrt_mul he0]
          have := Real.mul_self_sqrt hR.le
          linear_combination √e * this
  have ht : (∑ i, (finrank ℂ (V i) : ℝ)) * (1 - √e) ≤ (LinearMap.trace ℂ H (frQ c B)).re := by
    rw [tQ_eq c B]
    have h2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hfull i)
    rw [Finset.sum_sub_distrib] at h2
    nlinarith [hCS1]

  set b := stdOrthonormalBasis ℂ W with hb
  set g : Fin (finrank ℂ W) → H := fun l => (b l : H) with hgdef
  have hg : Orthonormal ℂ g := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  set tW : ℝ := ∑ l, (⟪g l, frQ c B (g l)⟫_ℂ).re with htWdef
  have htW : tW = ∑ i, c i * ∑ l, ‖adjoint (B i) (g l)‖ ^ 2 := by
    rw [htWdef]
    simp only [re_inner_Q, Finset.mul_sum]
    exact Finset.sum_comm
  have hWi : ∀ i, c i * ∑ l, ‖adjoint (B i) (g l)‖ ^ 2 ≤
      ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) +
        √((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) * √(hs2 (frK (c i) (B i) - LinearMap.id)) := by
    intro i
    have hperp : ∀ l, ∀ n ∈ Nτ i, ⟪B i n, g l⟫_ℂ = 0 := by
      intro l n hn
      have hmem : B i n ∈ ⨆ j, (Nτ j).map (B j) :=
        Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem hn)
      exact (Submodule.mem_orthogonal _ _).mp (b l).2 _ hmem
    have h1 := W_upper (B i) (Nτ i) hg hperp
    have hf : Orthonormal ℂ (fun m => ((stdOrthonormalBasis ℂ (Nτ i)ᗮ m : (Nτ i)ᗮ) : V i)) :=
      (stdOrthonormalBasis ℂ (Nτ i)ᗮ).orthonormal.comp_linearIsometry (Nτ i)ᗮ.subtypeₗᵢ
    have h2 := fam_bound (c i) (B i) hf
    simp only [Fintype.card_fin] at h2
    have hk : (finrank ℂ (Nτ i)ᗮ : ℝ) = finrank ℂ (V i) - finrank ℂ (Nτ i) := by
      have := Submodule.finrank_add_finrank_orthogonal (Nτ i)
      rw [eq_sub_iff_add_eq]
      exact_mod_cast (by omega : finrank ℂ (Nτ i)ᗮ + finrank ℂ (Nτ i) = finrank ℂ (V i))
    rw [hk] at h2
    have h3 := (abs_le.mp h2).2
    have h4 := mul_le_mul_of_nonneg_left h1 (hc i).le
    linarith
  have hup : tW ≤ ε * (∑ i, (finrank ℂ (V i) : ℝ)) + (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
    rw [htW]
    have h1 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hWi i)
    rw [Finset.sum_add_distrib] at h1
    have hCS : ∑ i, √((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) * √(hs2 (frK (c i) (B i) - LinearMap.id))
        ≤ (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
      calc _ ≤ √(∑ i, ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i))) *
              √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) :=
            Real.sum_sqrt_mul_sqrt_le Finset.univ (fun i => sub_nonneg.mpr (hnk i))
              (fun i => hs2_nonneg _)
        _ ≤ √(ε * ∑ i, (finrank ℂ (V i) : ℝ)) * √(e * ∑ i, (finrank ℂ (V i) : ℝ)) :=
            mul_le_mul (Real.sqrt_le_sqrt hN) (Real.sqrt_le_sqrt hK) (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)
        _ = (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
            rw [← Real.sqrt_mul (mul_nonneg hε hR.le),
              show ε * (∑ i, (finrank ℂ (V i) : ℝ)) * (e * ∑ i, (finrank ℂ (V i) : ℝ))
                = ε * e * (∑ i, (finrank ℂ (V i) : ℝ)) ^ 2 by ring,
              Real.sqrt_mul (mul_nonneg hε he0), Real.sqrt_sq hR.le]
            ring
    linarith

  set s : ℝ := (LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) with hs
  set A : H →ₗ[ℂ] H := frQ c B - (s : ℂ) • LinearMap.id with hA
  have hlow : (LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) * (finrank ℂ W : ℝ)
      - √(finrank ℂ W : ℝ) * √(hs2 A) ≤ tW := by
    have h := sum_re_inner_bound A hg
    simp only [Fintype.card_fin] at h
    have h1 : ∀ l, ⟪g l, g l⟫_ℂ = 1 := fun l => by
      rw [inner_self_eq_norm_sq_to_K, hg.1 l]; simp
    have hsum : ∑ l, (⟪g l, A (g l)⟫_ℂ).re
        = tW - s * (finrank ℂ W : ℝ) := by
      simp only [hA, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_sub_right,
        inner_smul_right, h1, mul_one, Complex.sub_re, Complex.ofReal_re, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, htWdef]
      ring
    rw [hsum] at h
    have := (abs_le.mp h).1
    linarith
  have hX : hs2 A
      ≤ η * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) := by
    set u := stdOrthonormalBasis ℂ H with hu
    have hterm : ∀ n, ‖A (u n)‖ ^ 2
        = ‖frQ c B (u n)‖ ^ 2 - 2 * s * (⟪u n, frQ c B (u n)⟫_ℂ).re + s ^ 2 := by
      intro n
      simp only [hA, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      have hsym : (⟪frQ c B (u n), u n⟫_ℂ).re = (⟪u n, frQ c B (u n)⟫_ℂ).re :=
        inner_re_symm (𝕜 := ℂ) _ _
      rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul, u.orthonormal.1 n]
      simp only [RCLike.re_to_complex, Complex.re_ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
        mul_one, sq_abs, hsym]
      ring
    have htr : (LinearMap.trace ℂ H (frQ c B)).re = ∑ n, (⟪u n, frQ c B (u n)⟫_ℂ).re := by
      rw [LinearMap.trace_eq_sum_inner (frQ c B) u, Complex.re_sum]
    have hT2 : (LinearMap.trace ℂ H (frQ c B ∘ₗ frQ c B)).re = ∑ n, ‖frQ c B (u n)‖ ^ 2 := trace_frame_sq_eq_sum c B
    rw [hilbert_schmidt_eq_basis_sum _ u]
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← htr, ← hT2]
    have hsD : s * (finrank ℂ H : ℝ) = (LinearMap.trace ℂ H (frQ c B)).re := by
      rw [hs]; field_simp
    have hst : (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ)
        = s * (LinearMap.trace ℂ H (frQ c B)).re := by
      rw [hs]; field_simp
    have hQ' : (LinearMap.trace ℂ H (frQ c B ∘ₗ frQ c B)).re
        ≤ (1 + η) * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) := hQ
    rw [show (1 + η) * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ)
        = (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ)
          + η * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) by ring] at hQ'
    have hDs2 : (finrank ℂ H : ℝ) * s ^ 2 = s * (LinearMap.trace ℂ H (frQ c B)).re := by
      rw [← hsD]; ring
    linarith
  exact final_real1 _ _ _ e ε η _ _ tW hD hR he0 he hε (Nat.cast_nonneg _) hwD ht
    (hs2_nonneg _) hX hlow hup
end Formalism.HN
