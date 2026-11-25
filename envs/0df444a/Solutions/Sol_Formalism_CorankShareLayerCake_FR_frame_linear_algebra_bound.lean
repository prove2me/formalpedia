-- Prove2me | solution 1 for Formalism.CorankShareLayerCake.FR.frame_linear_algebra_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:39:39.713546+00:00
-- url     : https://prove2.me/submissions/181dfd8f-803b-4628-9c37-7e237617f7a2

import Mathlib
import Definitions.Def_Formalism_CorankShare_StatementFR
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_hilbert_schmidt_nonneg_alt
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_sum_re_inner_bound
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_fam_bound
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_re_inner_Q
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_tQ_eq
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_hilbert_schmidt_sub_scalar
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_W_upper
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_final_real
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.CorankShareLayerCake.FR
namespace Pgsn2pfrla
open Finset Module LinearMap
open scoped InnerProductSpace
section gen
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
private lemma re_inner_self_eq_norm_sq_corank_share {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] (x : G) :
    (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x
end gen
section fam
variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
end fam
section wup
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
end wup
end Pgsn2pfrla
open Finset Module LinearMap Pgsn2pfrla
open scoped InnerProductSpace
private lemma sum_sqrt_mul_sqrt_le_sqrt_sum_mul {ι : Type*} [Fintype ι] (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i) : ∑ i, √(a i) * √(b i) ≤ √(∑ i, a i) * √(∑ i, b i) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => √(a i)) (fun i => √(b i))
  have e1 : ∀ i, √(a i) ^ 2 = a i := fun i => Real.sq_sqrt (ha i)
  have e2 : ∀ i, √(b i) ^ 2 = b i := fun i => Real.sq_sqrt (hb i)
  simp only [e1, e2] at h
  have hs : 0 ≤ ∑ i, √(a i) * √(b i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc ∑ i, √(a i) * √(b i) = √((∑ i, √(a i) * √(b i)) ^ 2) := (Real.sqrt_sq hs).symm
    _ ≤ √((∑ i, a i) * ∑ i, b i) := Real.sqrt_le_sqrt h
    _ = √(∑ i, a i) * √(∑ i, b i) := Real.sqrt_mul (Finset.sum_nonneg (fun i _ => ha i)) _
end Formalism.CorankShareLayerCake.FR
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.CorankShareLayerCake Formalism.CorankShareLayerCake.FR
open Finset Module LinearMap Pgsn2pfrla
open scoped InnerProductSpace
namespace Formalism.CorankShareLayerCake.FR
theorem _root_.solution : FrameLA := by
  intro ι _ V _ _ _ H _ _ _ B c Nτ e η ε hc hR hF2 he0 he hF1 hcor
  classical
  have hRpos : 0 < (∑ i, (finrank ℂ (V i) : ℝ)) := by exact_mod_cast hR
  have hs0 : 0 ≤ √e := Real.sqrt_nonneg e
  have hs : √e ≤ 1 / 2 := by
    have h4 : √(1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [← h4]
    exact Real.sqrt_le_sqrt he
  have hh0 : ∀ i, 0 ≤ hs2 (frK (c i) (B i) - LinearMap.id) := fun i => hilbert_schmidt_nonneg_alt _

  have hlowi : ∀ i, (finrank ℂ (V i) : ℝ) - √(finrank ℂ (V i) : ℝ) * √(hs2 (frK (c i) (B i) - LinearMap.id))
      ≤ c i * ∑ m, ‖B i (stdOrthonormalBasis ℂ (V i) m)‖ ^ 2 := by
    intro i
    have h1 := fam_bound (c i) (B i) (stdOrthonormalBasis ℂ (V i)).orthonormal
    rw [Fintype.card_fin] at h1
    have h2 := (abs_le.mp h1).1
    linarith
  have ht : (∑ i, (finrank ℂ (V i) : ℝ)) * (1 - √e) ≤ (LinearMap.trace ℂ H (frQ c B)).re := by
    rw [tQ_eq c B]
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlowi i)
    rw [Finset.sum_sub_distrib] at hsum
    have hcs := sum_sqrt_mul_sqrt_le_sqrt_sum_mul (fun i => (finrank ℂ (V i) : ℝ)) (fun i => hs2 (frK (c i) (B i) - LinearMap.id))
      (fun i => Nat.cast_nonneg _) hh0
    have h2 : √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) ≤ √e * √(∑ i, (finrank ℂ (V i) : ℝ)) := by
      rw [← Real.sqrt_mul he0]
      exact Real.sqrt_le_sqrt hF2
    have h3 : √(∑ i, (finrank ℂ (V i) : ℝ)) * √(∑ i, (finrank ℂ (V i) : ℝ)) = (∑ i, (finrank ℂ (V i) : ℝ)) := Real.mul_self_sqrt hRpos.le
    have h4 : √(∑ i, (finrank ℂ (V i) : ℝ)) * √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) ≤ (∑ i, (finrank ℂ (V i) : ℝ)) * √e := by
      calc √(∑ i, (finrank ℂ (V i) : ℝ)) * √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) ≤ √(∑ i, (finrank ℂ (V i) : ℝ)) * (√e * √(∑ i, (finrank ℂ (V i) : ℝ))) :=
            mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
        _ = √e * (√(∑ i, (finrank ℂ (V i) : ℝ)) * √(∑ i, (finrank ℂ (V i) : ℝ))) := by ring
        _ = (∑ i, (finrank ℂ (V i) : ℝ)) * √e := by rw [h3]; ring
    linarith
  have hDpos : 0 < (finrank ℂ H : ℝ) := by
    rcases Nat.eq_zero_or_pos (finrank ℂ H) with h0 | h0
    · exfalso
      haveI : Subsingleton H := Module.finrank_zero_iff.mp h0
      have hQ0 : frQ c B = 0 := LinearMap.ext (fun x => Subsingleton.elim _ _)
      have h5 : (LinearMap.trace ℂ H (frQ c B)).re = 0 := by rw [hQ0, map_zero, Complex.zero_re]
      nlinarith
    · exact_mod_cast h0

  have hk : ∀ i, ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) = (finrank ℂ (Nτ i)ᗮ : ℝ) := by
    intro i
    have h1 := Submodule.finrank_add_finrank_orthogonal (Nτ i)
    rw [← h1]
    push_cast
    ring
  have hk' : ∑ i, (finrank ℂ (Nτ i)ᗮ : ℝ) ≤ ε * (∑ i, (finrank ℂ (V i) : ℝ)) := by
    rw [← Finset.sum_congr rfl (fun i _ => hk i)]
    exact hcor
  have hε : 0 ≤ ε := by
    have h1 : 0 ≤ ∑ i, (finrank ℂ (Nτ i)ᗮ : ℝ) := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
    by_contra hc2
    push_neg at hc2
    have := mul_neg_of_neg_of_pos hc2 hRpos
    linarith

  obtain ⟨g, hgdef⟩ : ∃ g : Fin (finrank ℂ (⨆ i, (Nτ i).map (B i))ᗮ) → H,
      g = fun l => ((stdOrthonormalBasis ℂ (⨆ i, (Nτ i).map (B i))ᗮ l : (⨆ i, (Nτ i).map (B i))ᗮ) : H) := ⟨_, rfl⟩
  have hg : Orthonormal ℂ g := by
    rw [hgdef]
    exact (stdOrthonormalBasis ℂ (⨆ i, (Nτ i).map (B i))ᗮ).orthonormal.comp_linearIsometry (⨆ i, (Nτ i).map (B i))ᗮ.subtypeₗᵢ
  have hgW : ∀ l, g l ∈ (⨆ i, (Nτ i).map (B i))ᗮ := by
    intro l
    rw [hgdef]
    exact (stdOrthonormalBasis ℂ (⨆ i, (Nτ i).map (B i))ᗮ l).2
  have hperp : ∀ i, ∀ l, ∀ n ∈ Nτ i, ⟪B i n, g l⟫_ℂ = 0 := by
    intro i l n hn
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem hn)) (hgW l)

  have htW : (∑ l, (⟪g l, frQ c B (g l)⟫_ℂ).re) = ∑ i, c i * ∑ l, ‖adjoint (B i) (g l)‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun l _ => re_inner_Q c B (g l)), Finset.sum_comm]
    simp only [Finset.mul_sum]
  have hupi : ∀ i, c i * ∑ l, ‖adjoint (B i) (g l)‖ ^ 2
      ≤ (finrank ℂ (Nτ i)ᗮ : ℝ) + √(finrank ℂ (Nτ i)ᗮ : ℝ) * √(hs2 (frK (c i) (B i) - LinearMap.id)) := by
    intro i
    have h1 := W_upper (B i) (Nτ i) hg (hperp i)
    have ho : Orthonormal ℂ (fun m => ((stdOrthonormalBasis ℂ (Nτ i)ᗮ m : (Nτ i)ᗮ) : V i)) :=
      (stdOrthonormalBasis ℂ (Nτ i)ᗮ).orthonormal.comp_linearIsometry (Nτ i)ᗮ.subtypeₗᵢ
    have h2 := fam_bound (c i) (B i) ho
    rw [Fintype.card_fin] at h2
    beta_reduce at h2
    have h3 := (abs_le.mp h2).2
    have h4 := mul_le_mul_of_nonneg_left h1 (hc i).le
    linarith
  have hup : (∑ l, (⟪g l, frQ c B (g l)⟫_ℂ).re) ≤ ε * (∑ i, (finrank ℂ (V i) : ℝ)) + (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
    rw [htW]
    have hs1 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hupi i)
    rw [Finset.sum_add_distrib] at hs1
    have hcs := sum_sqrt_mul_sqrt_le_sqrt_sum_mul (fun i => (finrank ℂ (Nτ i)ᗮ : ℝ)) (fun i => hs2 (frK (c i) (B i) - LinearMap.id))
      (fun i => Nat.cast_nonneg _) hh0
    have h2 : √(∑ i, (finrank ℂ (Nτ i)ᗮ : ℝ)) * √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) ≤ (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
      calc √(∑ i, (finrank ℂ (Nτ i)ᗮ : ℝ)) * √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) ≤ √(ε * (∑ i, (finrank ℂ (V i) : ℝ))) * √(e * (∑ i, (finrank ℂ (V i) : ℝ))) :=
            mul_le_mul (Real.sqrt_le_sqrt hk') (Real.sqrt_le_sqrt hF2) (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)
        _ = √((ε * e) * ((∑ i, (finrank ℂ (V i) : ℝ)) * (∑ i, (finrank ℂ (V i) : ℝ)))) := by
            rw [← Real.sqrt_mul (mul_nonneg hε hRpos.le)]
            congr 1
            ring
        _ = (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
            rw [Real.sqrt_mul (mul_nonneg hε he0), Real.sqrt_mul_self hRpos.le]
            ring
    linarith

  have hlow : (LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) * (finrank ℂ (⨆ i, (Nτ i).map (B i))ᗮ : ℝ) - √(finrank ℂ (⨆ i, (Nτ i).map (B i))ᗮ : ℝ) * √(hs2 (frQ c B - (((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) : ℝ) : ℂ) • LinearMap.id)) ≤ (∑ l, (⟪g l, frQ c B (g l)⟫_ℂ).re) := by
    have hb := sum_re_inner_bound (frQ c B - (((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) : ℝ) : ℂ) • LinearMap.id) hg
    rw [Fintype.card_fin] at hb
    have h1 : ∀ l, (⟪g l, g l⟫_ℂ).re = 1 := fun l => by rw [re_inner_self_eq_norm_sq_corank_share, hg.1 l]; norm_num
    have hsplit : ∑ l, (⟪g l, ((frQ c B - (((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) : ℝ) : ℂ) • LinearMap.id : H →ₗ[ℂ] H)) (g l)⟫_ℂ).re
        = (∑ l, (⟪g l, frQ c B (g l)⟫_ℂ).re) - (LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) * (finrank ℂ (⨆ i, (Nτ i).map (B i))ᗮ : ℝ) := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_sub_right,
        inner_smul_right, Complex.sub_re, Complex.re_ofReal_mul, Finset.sum_sub_distrib, h1, mul_one,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hsplit] at hb
    have h2 := (abs_le.mp hb).1
    linarith
  have hX : hs2 (frQ c B - (((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) : ℝ) : ℂ) • LinearMap.id) ≤ η * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) := by
    rw [hilbert_schmidt_sub_scalar c B ((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ))]
    have e2 : ((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ)) ^ 2 * (finrank ℂ H : ℝ) = (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) := by
      field_simp
    have e3 : (1 + η) * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) = (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) + η * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) := by ring
    have e4 : 2 * ((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ)) * (LinearMap.trace ℂ H (frQ c B)).re = 2 * ((LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ)) := by ring
    linarith
  have hwD : (finrank ℂ (⨆ i, (Nτ i).map (B i))ᗮ : ℝ) ≤ (finrank ℂ H : ℝ) := by exact_mod_cast Submodule.finrank_le (⨆ i, (Nτ i).map (B i))ᗮ
  exact final_real (finrank ℂ H : ℝ) (∑ i, (finrank ℂ (V i) : ℝ)) (finrank ℂ (⨆ i, (Nτ i).map (B i))ᗮ : ℝ) e ε η (LinearMap.trace ℂ H (frQ c B)).re (hs2 (frQ c B - (((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) : ℝ) : ℂ) • LinearMap.id)) (∑ l, (⟪g l, frQ c B (g l)⟫_ℂ).re) hDpos hRpos he0 he hε (Nat.cast_nonneg _) hwD ht
    (hilbert_schmidt_nonneg_alt _) hX hlow hup
end Formalism.CorankShareLayerCake.FR
