-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovolBound_covol_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:17.468648+00:00
-- url     : https://prove2.me/submissions/2942031a-86a6-496c-b225-ae68111afa4a

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_mem_zmap
import Theorems.Thm_Formalism_E_covolumeEqSqrtDetGram


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (N : ℕ)
    (ι : V →+ EuclideanSpace ℝ (Fin N))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (M : Submodule (𝓞 K) V) [DiscreteTopology (zmap ι M)] [IsZLattice ℝ (zmap ι M)]
    (D : ℕ) (hD0 : 0 < D)
    (hD : ∀ y y' : V, (∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = z) →
       (∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x y') = z) →
       ∃ z : ℤ, (D : ℚ) * Algebra.trace ℚ K (h y y') = z) :
    ZLattice.covolume (zmap ι M) ≤ Real.sqrt ((D : ℝ) ^ N) := by
  classical
  set Λ := zmap ι M with hΛdef

  let n := Module.Free.ChooseBasisIndex ℤ Λ
  let bZ : Module.Basis n ℤ Λ := Module.Free.chooseBasis ℤ Λ
  let b : Module.Basis n ℝ (EuclideanSpace ℝ (Fin N)) := bZ.ofZLatticeBasis ℝ Λ
  have hb : ∀ i, b i = (bZ i : EuclideanSpace ℝ (Fin N)) := fun i =>
    Module.Basis.ofZLatticeBasis_apply ℝ Λ bZ i
  have hspan : Submodule.span ℤ (Set.range b) = Λ := Module.Basis.ofZLatticeBasis_span ℝ Λ bZ
  have hcard : Fintype.card n = N := by
    rw [← Module.finrank_eq_card_basis b, finrank_euclideanSpace_fin]
  have hpre : ∀ i, ∃ x ∈ M, ι x = b i := by
    intro i
    have hi : b i ∈ Λ := by rw [hb]; exact (bZ i).2
    exact (genusCovolBound_mem_zmap N ι M (b i)).mp hi
  choose x hxM hxb using hpre
  let Gq : Matrix n n ℚ := Matrix.of fun i j => Algebra.trace ℚ K (h (x i) (x j))
  have e1 : ∀ i k, inner ℝ (b i) (b k) = ((Gq i k : ℚ) : ℝ) := fun i k => by
    rw [← hxb i, ← hxb k, hι]
    rfl
  have hG : Matrix.gram ℝ b = (Rat.castHom ℝ).mapMatrix Gq := by
    ext i j
    rw [Matrix.gram_apply, e1]
    rfl
  have hdetG : 0 < (Matrix.gram ℝ b).det :=
    (Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos
  have hdetq : ((Gq.det : ℚ) : ℝ) = (Matrix.gram ℝ b).det := by
    rw [hG, ← RingHom.map_det]
    rfl
  have hdq0 : 0 < Gq.det := by
    have : (0 : ℝ) < (Gq.det : ℝ) := by rw [hdetq]; exact hdetG
    exact_mod_cast this
  let Hq := Gq⁻¹
  have hGH : Gq * Hq = 1 := Matrix.mul_nonsing_inv Gq (isUnit_iff_ne_zero.mpr hdq0.ne')

  let w : n → EuclideanSpace ℝ (Fin N) := fun j => ∑ k, ((Hq k j : ℚ) : ℝ) • b k
  let y : n → V := fun j => ∑ k, ((Hq k j : ℚ) : K) • x k
  have hy : ∀ j, ι (y j) = w j := by
    intro j
    simp only [y, w, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_ratCast_smul ι K ℝ, hxb]
  have hbw : ∀ i j, inner ℝ (b i) (w j) = (((1 : Matrix n n ℚ) i j : ℚ) : ℝ) := by
    intro i j
    have hw : w j = ∑ k, ((Hq k j : ℚ) : ℝ) • b k := rfl
    rw [hw, inner_sum, ← hGH, Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_smul_right, e1]
    ring
  have hint : ∀ v ∈ Λ, ∀ j, ∃ z : ℤ, inner ℝ v (w j) = z := by
    intro v hv j
    rw [← hspan] at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      rw [hbw, Matrix.one_apply]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    | zero => exact ⟨0, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨c, hc⟩ := hv
      exact ⟨a + c, by rw [inner_add_left, ha, hc]; push_cast; ring⟩
    | smul a u _ hu =>
      obtain ⟨c, hc⟩ := hu
      exact ⟨a * c, by rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hc]; push_cast; ring⟩
  have hyd : ∀ j, ∀ x' ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x' (y j)) = z := by
    intro j x' hx'
    obtain ⟨z, hz⟩ := hint (ι x') ((genusCovolBound_mem_zmap N ι M _).mpr ⟨x', hx', rfl⟩) j
    refine ⟨z, ?_⟩
    rw [← hy j, hι] at hz
    exact_mod_cast hz
  have hww : ∀ i j, inner ℝ (w i) (w j) = ((Hq j i : ℚ) : ℝ) := by
    intro i j
    have hw : w i = ∑ k, ((Hq k i : ℚ) : ℝ) • b k := rfl
    rw [hw, sum_inner, Finset.sum_eq_single j]
    · rw [real_inner_smul_left, hbw, Matrix.one_apply_eq]
      push_cast
      ring
    · intro k _ hk
      rw [real_inner_smul_left, hbw, Matrix.one_apply_ne hk]
      simp
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hZ : ∀ i j, ∃ z : ℤ, (D : ℚ) * Hq j i = z := by
    intro i j
    obtain ⟨z, hz⟩ := hD (y i) (y j) (hyd i) (hyd j)
    refine ⟨z, ?_⟩
    have e : ((Algebra.trace ℚ K (h (y i) (y j)) : ℚ) : ℝ) = ((Hq j i : ℚ) : ℝ) := by
      rw [← hι, hy, hy, hww]
    have e' : Algebra.trace ℚ K (h (y i) (y j)) = Hq j i := by exact_mod_cast e
    rw [← e', hz]
  choose Z hZ' using hZ
  have hZm : (Int.castRingHom ℚ).mapMatrix (Matrix.of Z) = (D : ℚ) • Hq.transpose := by
    ext i j
    simp [hZ']
  have hdetZ : (((Matrix.of Z).det : ℤ) : ℚ) = (D : ℚ) ^ N * (Gq.det)⁻¹ := by
    have := RingHom.map_det (Int.castRingHom ℚ) (Matrix.of Z)
    rw [hZm, Matrix.det_smul, Matrix.det_transpose, Matrix.det_nonsing_inv, hcard,
      Ring.inverse_eq_inv'] at this
    simpa using this
  have hpos : (0 : ℚ) < (((Matrix.of Z).det : ℤ) : ℚ) := by rw [hdetZ]; positivity
  have h1 : (1 : ℚ) ≤ (((Matrix.of Z).det : ℤ) : ℚ) := by
    have h0 : 0 < (Matrix.of Z).det := by exact_mod_cast hpos
    have h1' : (1 : ℤ) ≤ (Matrix.of Z).det := by omega
    exact_mod_cast h1'
  have hq : Gq.det ≤ (D : ℚ) ^ N := by
    rw [hdetZ] at h1
    have := mul_le_mul_of_nonneg_right h1 hdq0.le
    rwa [mul_assoc, inv_mul_cancel₀ hdq0.ne', mul_one, one_mul] at this
  have hle : (Matrix.gram ℝ b).det ≤ (D : ℝ) ^ N := by
    rw [← hdetq]
    exact_mod_cast hq
  have hcg := Formalism.E.covolumeEqSqrtDetGram (EuclideanSpace ℝ (Fin N)) n b
  rw [hspan] at hcg
  rw [hcg]
  exact Real.sqrt_le_sqrt hle
end Formalism.HermitianLatticesTheory
