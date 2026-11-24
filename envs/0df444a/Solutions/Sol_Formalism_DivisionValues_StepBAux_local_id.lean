-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.local_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:20.05006+00:00
-- url     : https://prove2.me/submissions/4c6ce6cc-2580-4740-849c-cfc1fbe8a630

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Theorems.Thm_Formalism_DivisionValues_StepBAux_gram_change
import Theorems.Thm_Formalism_DivisionValues_StepBAux_gram_ne
import Theorems.Thm_Formalism_DivisionValues_StepBAux_image_li
import Theorems.Thm_Formalism_DivisionValues_StepBAux_gram_image
import Theorems.Thm_Formalism_DivisionValues_StepBAux_gram_ratHerm
import Theorems.Thm_Formalism_DivisionValues_StepBAux_matLat_lattice
import Theorems.Thm_Formalism_DivisionValues_StepBAux_vw_prod
import Theorems.Thm_Formalism_DivisionValues_StepBAux_vw_pow
import Theorems.Thm_Formalism_DivisionValues_StepBAux_detRatio_ne
import Theorems.Thm_Formalism_DivisionValues_StepBAux_lidx_add
import Theorems.Thm_Formalism_DivisionValues_StepBAux_key_alg
import Theorems.Thm_Formalism_DivisionValues_StepBAux_idx_change_img

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.StepBAux
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.StepBAux
theorem _root_.solution (hV : ValBasic) (hIC : IdxChange) (hJw : JwGram) [IsTotallyComplex K]
    (K0 : Subfield K) (hK0 : IsCMSub K0) (v0 : InfinitePlace K) (hv0 : IsConjAt v0)
    (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXE : ∀ v, IsUnit (XE v).det)
    (XQ0 XQ1 : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXQ0 : ∀ v, IsUnit (XQ0 v).det)
    (hXQ1 : ∀ v, IsUnit (XQ1 v).det)
    (Lam0 Lam1 : Submodule (𝓞 K) (Fin D → K)) (hL1 : Submodule.IsLattice K Lam1)
    (ι0 ι1 : Matrix (Fin D) (Fin D) K) (hι0 : IsUnit ι0.det) (hι1 : IsUnit ι1.det)
    (J : Type) [Fintype J] (d : J → ℕ)
    (XW : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ)
    (hXW : ∀ j v, IsUnit (XW j v).det)
    (M : ∀ j, Submodule (𝓞 K) (Fin (d j) → K)) (hM : ∀ j, Submodule.IsLattice K (M j))
    (HT0 HT1 : ∀ j, Matrix (Fin (d j)) (Fin (d j)) K)
    (XT0 XT1 : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ)
    (hHT0 : ∀ j, IsRatHerm K0 (HT0 j) (XT0 j)) (hHT1 : ∀ j, IsRatHerm K0 (HT1 j) (XT1 j))
    (T0 T1 : ∀ j, Submodule (𝓞 K) (Fin (d j) → K))
    (hT0 : ∀ j, Submodule.IsLattice K (T0 j)) (hT1 : ∀ j, Submodule.IsLattice K (T1 j))
    (θ0 θ1 : ∀ j, Matrix (Fin (d j)) (Fin (d j)) K) (hθ0 : ∀ j, IsUnit (θ0 j).det)
    (hθ1 : ∀ j, IsUnit (θ1 j).det)
    (κ0 ρr : ℝ) (hκ : 0 < κ0) (ρ : K) (hρ : v0.embedding ρ = (ρr : ℂ)) (hρpos : 0 < ρr)
    (w : HeightOneSpectrum (𝓞 K)) (hρv : vw w ρ = 0)
    (hdet0 : detRatio XQ0 XE ι0 v0 = κ0 ^ D * ∏ j, detRatio (XT0 j) (XW j) (θ0 j) v0)
    (hdet1 : detRatio XQ1 XE ι1 v0 = (κ0 * ρr) ^ D * ∏ j, detRatio (XT1 j) (XW j) (θ1 j) v0)
    (G0 G1 : K) (e0 e1 : Fin D → Fin D → K) (he0 : IsLocBasis Lam0 w e0)
    (he1 : IsLocBasis Lam1 w e1)
    (hG0 : v0.embedding G0 = (gram XQ0 v0 e0).det) (hG1 : v0.embedding G1 = (gram XQ1 v0 e1).det)
    (f0 f1 : ∀ j, Fin (d j) → Fin (d j) → K) (hf0 : ∀ j, IsLocBasis (T0 j) w (f0 j))
    (hf1 : ∀ j, IsLocBasis (T1 j) w (f1 j)) :
    idx w (matLat ι0 Lam0) (matLat ι1 Lam1) + idx (conjPl w) (matLat ι0 Lam0) (matLat ι1 Lam1) =
      vw w G1 - vw w G0 + ∑ j, ((idx w (M j) (matLat (θ1 j) (T1 j)) -
          idx w (M j) (matLat (θ0 j) (T0 j))) +
        (idx (conjPl w) (M j) (matLat (θ1 j) (T1 j)) -
          idx (conjPl w) (M j) (matLat (θ0 j) (T0 j))) +
        (jw (HT1 j) w (T1 j) - jw (HT0 j) w (T0 j))) := by
  classical
  obtain ⟨hmul, hstar, -, -, -, -, -⟩ := hV K w
  obtain ⟨γ, hγ, hy1, hy2⟩ := idx_change_img hIC ι0 ι1 hι0 hι1 Lam0 Lam1 hL1 w e0 e1 he0 he1
  choose δ hδ hz1 hz2 using fun j => idx_change_img hIC (θ0 j) (θ1 j) (hθ0 j) (hθ1 j) (T0 j)
    (T1 j) (hT1 j) w (f0 j) (f1 j) (hf0 j) (hf1 j)
  have hc : ∀ j (u : HeightOneSpectrum (𝓞 K)), idx u (M j) (matLat (θ1 j) (T1 j)) =
      idx u (M j) (matLat (θ0 j) (T0 j)) + idx u (matLat (θ0 j) (T0 j)) (matLat (θ1 j) (T1 j)) :=
    fun j u => lidx_add (K := K) u.asIdeal _ _ _ (hM j) (matLat_lattice _ (hθ0 j) _ (hT0 j))
      (matLat_lattice _ (hθ1 j) _ (hT1 j))
  have hj0 : ∀ j, jw (HT0 j) w (T0 j) = - vw w (gramR (HT0 j) (f0 j)) := fun j =>
    hJw K K0 hK0 (d j) (HT0 j) (XT0 j) (hHT0 j) (T0 j) (hT0 j) w (f0 j) (hf0 j)
  have hj1 : ∀ j, jw (HT1 j) w (T1 j) = - vw w (gramR (HT1 j) (f1 j)) := fun j =>
    hJw K K0 hK0 (d j) (HT1 j) (XT1 j) (hHT1 j) (T1 j) (hT1 j) w (f1 j) (hf1 j)
  have hXT0 : ∀ j v, IsUnit (XT0 j v).det := fun j v => ((hHT0 j).2 v).1
  have hXT1 : ∀ j v, IsUnit (XT1 j v).det := fun j v => ((hHT1 j).2 v).1
  have h1 : (gram XE v0 (fun i => ι1 *ᵥ e1 i)).det = star (v0.embedding γ.det) *
      v0.embedding γ.det * (gram XE v0 (fun i => ι0 *ᵥ e0 i)).det := by
    rw [hγ]; exact gram_change _ _ _ _
  have h21 : (gram XE v0 (fun i => ι1 *ᵥ e1 i)).det =
      (detRatio XQ1 XE ι1 v0 : ℂ) * v0.embedding G1 := by
    rw [hG1]; exact gram_image XQ1 XE hXQ1 ι1 e1 v0
  have h20 : (gram XE v0 (fun i => ι0 *ᵥ e0 i)).det =
      (detRatio XQ0 XE ι0 v0 : ℂ) * v0.embedding G0 := by
    rw [hG0]; exact gram_image XQ0 XE hXQ0 ι0 e0 v0
  have h4 : ∀ j, (gram (XW j) v0 (fun i => θ1 j *ᵥ f1 j i)).det =
      star (v0.embedding (δ j).det) * v0.embedding (δ j).det *
        (gram (XW j) v0 (fun i => θ0 j *ᵥ f0 j i)).det := fun j => by
    rw [hδ j]; exact gram_change _ _ _ _
  have h51 : ∀ j, (gram (XW j) v0 (fun i => θ1 j *ᵥ f1 j i)).det =
      (detRatio (XT1 j) (XW j) (θ1 j) v0 : ℂ) * v0.embedding (gramR (HT1 j) (f1 j)) := fun j => by
    rw [← gram_ratHerm K0 (HT1 j) (XT1 j) (hHT1 j) v0 hv0]
    exact gram_image (XT1 j) (XW j) (hXT1 j) (θ1 j) (f1 j) v0
  have h50 : ∀ j, (gram (XW j) v0 (fun i => θ0 j *ᵥ f0 j i)).det =
      (detRatio (XT0 j) (XW j) (θ0 j) v0 : ℂ) * v0.embedding (gramR (HT0 j) (f0 j)) := fun j => by
    rw [← gram_ratHerm K0 (HT0 j) (XT0 j) (hHT0 j) v0 hv0]
    exact gram_image (XT0 j) (XW j) (hXT0 j) (θ0 j) (f0 j) v0
  have hθne : ∀ j, (detRatio (XT0 j) (XW j) (θ0 j) v0 : ℂ) ≠ 0 := fun j => by
    exact_mod_cast detRatio_ne (XT0 j) (XW j) (hXT0 j) (hXW j) (θ0 j) (hθ0 j) v0
  have hC := key_alg (J := J) D
    (gE0 := (gram XE v0 (fun i => ι0 *ᵥ e0 i)).det) (gE1 := (gram XE v0 (fun i => ι1 *ᵥ e1 i)).det)
    (dR0 := (detRatio XQ0 XE ι0 v0 : ℂ)) (dR1 := (detRatio XQ1 XE ι1 v0 : ℂ))
    (G0 := v0.embedding G0) (G1 := v0.embedding G1)
    (Ny := star (v0.embedding γ.det) * v0.embedding γ.det) (κ := (κ0 : ℂ)) (ρ := (ρr : ℂ))
    (gW0 := fun j => (gram (XW j) v0 (fun i => θ0 j *ᵥ f0 j i)).det)
    (gW1 := fun j => (gram (XW j) v0 (fun i => θ1 j *ᵥ f1 j i)).det)
    (dθ0 := fun j => (detRatio (XT0 j) (XW j) (θ0 j) v0 : ℂ))
    (dθ1 := fun j => (detRatio (XT1 j) (XW j) (θ1 j) v0 : ℂ))
    (gT0 := fun j => v0.embedding (gramR (HT0 j) (f0 j)))
    (gT1 := fun j => v0.embedding (gramR (HT1 j) (f1 j)))
    (Nz := fun j => star (v0.embedding (δ j).det) * v0.embedding (δ j).det)
    h1 h21 h20 (by rw [hdet1]; push_cast; ring) (by rw [hdet0]; push_cast; ring) h4 h51 h50
    (by exact_mod_cast hκ.ne') hθne
  have hK : ρ ^ D * G1 * ∏ j, (star (δ j).det * (δ j).det * gramR (HT0 j) (f0 j)) =
      star γ.det * γ.det * G0 * ∏ j, gramR (HT1 j) (f1 j) := by
    have hv0' : ∀ a : K, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a) := hv0
    apply v0.embedding.injective
    simp only [map_mul, map_pow, map_prod, hv0', hρ]
    simp only [Complex.star_def] at hC
    exact hC
  have hG0ne : G0 ≠ 0 := fun h => gram_ne XQ0 hXQ0 e0 he0.1 v0 (by rw [← hG0, h, map_zero])
  have hG1ne : G1 ≠ 0 := fun h => gram_ne XQ1 hXQ1 e1 he1.1 v0 (by rw [← hG1, h, map_zero])
  have hγne : γ.det ≠ 0 := by
    intro h
    apply gram_ne XE hXE _ (image_li ι1 hι1 e1 he1.1) v0
    rw [h1, h, map_zero]; ring
  have hδne : ∀ j, (δ j).det ≠ 0 := by
    intro j h
    apply gram_ne (XW j) (hXW j) _ (image_li (θ1 j) (hθ1 j) (f1 j) (hf1 j).1) v0
    rw [h4 j, h, map_zero]; ring
  have hgT0ne : ∀ j, gramR (HT0 j) (f0 j) ≠ 0 := fun j h =>
    gram_ne (XT0 j) (hXT0 j) (f0 j) (hf0 j).1 v0
      (by rw [gram_ratHerm K0 (HT0 j) (XT0 j) (hHT0 j) v0 hv0, h, map_zero])
  have hgT1ne : ∀ j, gramR (HT1 j) (f1 j) ≠ 0 := fun j h =>
    gram_ne (XT1 j) (hXT1 j) (f1 j) (hf1 j).1 v0
      (by rw [gram_ratHerm K0 (HT1 j) (XT1 j) (hHT1 j) v0 hv0, h, map_zero])
  have hρne : ρ ≠ 0 := by
    intro h
    rw [h, map_zero] at hρ
    exact hρpos.ne' (by exact_mod_cast hρ.symm)
  have hv := congrArg (vw w) hK
  have hL : vw w (ρ ^ D * G1 * ∏ j, (star (δ j).det * (δ j).det * gramR (HT0 j) (f0 j))) =
      vw w G1 + ∑ j, (vw (conjPl w) (δ j).det + vw w (δ j).det + vw w (gramR (HT0 j) (f0 j))) := by
    have hne : ∀ j, star (δ j).det * (δ j).det * gramR (HT0 j) (f0 j) ≠ 0 := fun j =>
      mul_ne_zero (mul_ne_zero (star_ne_zero.mpr (hδne j)) (hδne j)) (hgT0ne j)
    rw [hmul _ _ (mul_ne_zero (pow_ne_zero _ hρne) hG1ne)
        (Finset.prod_ne_zero_iff.mpr fun j _ => hne j),
      hmul _ _ (pow_ne_zero _ hρne) hG1ne, vw_pow hV w ρ hρne, hρv, vw_prod hV w _ _ hne]
    simp only [mul_zero, zero_add]
    refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
    rw [hmul _ _ (mul_ne_zero (star_ne_zero.mpr (hδne j)) (hδne j)) (hgT0ne j),
      hmul _ _ (star_ne_zero.mpr (hδne j)) (hδne j), hstar]
  have hR : vw w (star γ.det * γ.det * G0 * ∏ j, gramR (HT1 j) (f1 j)) =
      vw (conjPl w) γ.det + vw w γ.det + vw w G0 + ∑ j, vw w (gramR (HT1 j) (f1 j)) := by
    rw [hmul _ _ (mul_ne_zero (mul_ne_zero (star_ne_zero.mpr hγne) hγne) hG0ne)
        (Finset.prod_ne_zero_iff.mpr fun j _ => hgT1ne j),
      hmul _ _ (mul_ne_zero (star_ne_zero.mpr hγne) hγne) hG0ne,
      hmul _ _ (star_ne_zero.mpr hγne) hγne, hstar, vw_prod hV w _ _ hgT1ne]
  have hsum : ∑ j, ((idx w (M j) (matLat (θ1 j) (T1 j)) -
          idx w (M j) (matLat (θ0 j) (T0 j))) +
        (idx (conjPl w) (M j) (matLat (θ1 j) (T1 j)) -
          idx (conjPl w) (M j) (matLat (θ0 j) (T0 j))) +
        (jw (HT1 j) w (T1 j) - jw (HT0 j) w (T0 j))) =
      ∑ j, (vw (conjPl w) (δ j).det + vw w (δ j).det + vw w (gramR (HT0 j) (f0 j))) -
        ∑ j, vw w (gramR (HT1 j) (f1 j)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc j w, hc j (conjPl w), hz1 j, hz2 j, hj0 j, hj1 j]
    ring
  rw [hsum, hy1, hy2]
  rw [hL, hR] at hv
  linarith
end Formalism.DivisionValues.StepBAux
