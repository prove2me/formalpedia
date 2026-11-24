-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G1.exists_unif_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:28:37.980887+00:00
-- url     : https://prove2.me/submissions/4547f495-bae4-4b67-85a9-514fa70b4b39

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AlmostEverywhereSpherical
import Theorems.Thm_Formalism_L2_SG_Pf_G1_mem_pow_iff
import Theorems.Thm_Formalism_L2_SG_Pf_G1_mem_pow_of_coprime
import Theorems.Thm_Formalism_L2_SG_Pf_G1_sup_top_of_notMem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_locR
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_exists_star_int
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_isUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.L2.SG.Pf.G1
theorem _root_.solution (hF : IsFixF K F) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ π : K, IsUnif (locRing P) π ∧ ∀ a : K, a ≠ 0 → ∃ N : ℕ, a * π⁻¹ ^ N ∉ locRing P := by
  obtain ⟨π, hπ, -, -⟩ := exists_isUnif hF hP
  refine ⟨π, hπ, fun a ha => ?_⟩
  have inj := IsFractionRing.injective (𝓞 K) K
  have hπ0 : π ≠ 0 := hπ.ne
  have hP1 : (1 : 𝓞 K) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h)

  have hc : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, s ∉ P ∧
      ∀ s' : 𝓞 K, algebraMap (𝓞 K) K s' = star (algebraMap (𝓞 K) K s) → s' ∉ P := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs => exact hs
    | one =>
      refine ⟨hP1, fun s' hs' => ?_⟩
      have e : s' = 1 := inj (by rw [hs', map_one, star_one])
      rw [e]
      exact hP1
    | mul x y _ _ hx hy =>
      refine ⟨fun h => (hP.isPrime.mem_or_mem h).elim hx.1 hy.1, fun s' hs' => ?_⟩
      obtain ⟨x', hx'⟩ := Formalism.HermitianLattices.Ext.L3.MeanB.exists_star_int x
      obtain ⟨y', hy'⟩ := Formalism.HermitianLattices.Ext.L3.MeanB.exists_star_int y
      have e : s' = x' * y' := inj (by rw [hs', map_mul, map_mul, star_mul', hx', hy'])
      rw [e]
      exact fun h => (hP.isPrime.mem_or_mem h).elim (hx.2 x' hx') (hy.2 y' hy')

  have hπmem : π ∈ Formalism.HermitianLatticesTheory.locR (K := K) P := hπ.mem
  obtain ⟨s0, hs0, hu⟩ := (Formalism.HermitianLatticesTheory.locDual_mem_locR (K := K) P π).mp hπmem
  obtain ⟨u, hu⟩ := Submodule.mem_one.mp hu
  have hu_not : u ∈ P ∨ ∃ t ∈ P, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K u) := by
    by_contra hcon
    push_neg at hcon
    have hu_h : u ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P :=
      Submonoid.subset_closure ⟨hcon.1, fun t ht htP => hcon.2 t htP ht⟩
    have hinv : π⁻¹ ∈ locRing P := by
      change π⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P
      rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
      refine ⟨u, hu_h, Submodule.mem_one.mpr ⟨s0, ?_⟩⟩
      rw [hu, mul_assoc, mul_inv_cancel₀ hπ0, mul_one]
    have h1 := hπ.rad (-π⁻¹) (neg_mem hinv)
    rw [mul_neg, mul_inv_cancel₀ hπ0, add_neg_cancel] at h1
    exact h1.1 rfl

  obtain ⟨X, Y, hY, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have hX0 : X ≠ 0 := by
    rintro rfl
    simp at ha
  have hY0 : algebraMap (𝓞 K) K Y ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hY (inj (by rw [h, map_zero]))
  by_contra hall
  push_neg at hall
  have key : ∀ N, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, ∃ r : 𝓞 K, s * X * s0 ^ N = r * Y * u ^ N := by
    intro N
    have hm : algebraMap (𝓞 K) K X / algebraMap (𝓞 K) K Y * π⁻¹ ^ N ∈ Formalism.HermitianLatticesTheory.locR (K := K) P :=
      hall N
    obtain ⟨s, hs, hr⟩ := (Formalism.HermitianLatticesTheory.locDual_mem_locR (K := K) P _).mp hm
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hr
    refine ⟨s, hs, r, inj ?_⟩
    simp only [map_mul, map_pow]
    rw [hu, hr]
    have e1 : (algebraMap (𝓞 K) K Y)⁻¹ * algebraMap (𝓞 K) K Y = 1 := inv_mul_cancel₀ hY0
    have e2 : π⁻¹ ^ N * π ^ N = 1 := by rw [← mul_pow, inv_mul_cancel₀ hπ0, one_pow]
    linear_combination (-(algebraMap (𝓞 K) K s * algebraMap (𝓞 K) K X * algebraMap (𝓞 K) K s0 ^ N *
      (π⁻¹ ^ N * π ^ N))) * e1 +
      (-(algebraMap (𝓞 K) K s * algebraMap (𝓞 K) K X * algebraMap (𝓞 K) K s0 ^ N)) * e2
  obtain ⟨Z, hZ0, hZ⟩ : ∃ Z : 𝓞 K, Z ≠ 0 ∧ ∀ N, Z ∈ P ^ N := by
    rcases hu_not with huP | ⟨t, htP, ht⟩
    · refine ⟨X, hX0, fun N => ?_⟩
      obtain ⟨s, hs, r, hsr⟩ := key N
      have hmem : s * s0 ^ N * X ∈ P ^ N := by
        rw [show s * s0 ^ N * X = r * Y * u ^ N by rw [← hsr]; ring]
        exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow huP N)
      refine mem_pow_of_coprime (sup_top_of_notMem hP ?_) N hmem
      intro h
      rcases hP.isPrime.mem_or_mem h with h1 | h1
      · exact (hc s hs).1 h1
      · exact (hc s0 hs0).1 (hP.isPrime.mem_of_pow_mem N h1)
    · obtain ⟨X', hX'⟩ := Formalism.HermitianLattices.Ext.L3.MeanB.exists_star_int X
      refine ⟨X', ?_, fun N => ?_⟩
      · intro h
        have h0 : star (algebraMap (𝓞 K) K X) = 0 := by rw [← hX', h, map_zero]
        rw [star_eq_zero] at h0
        exact hX0 (inj (by rw [h0, map_zero]))
      · obtain ⟨s, hs, r, hsr⟩ := key N
        obtain ⟨s', hs'⟩ := Formalism.HermitianLattices.Ext.L3.MeanB.exists_star_int s
        obtain ⟨s0', hs0'⟩ := Formalism.HermitianLattices.Ext.L3.MeanB.exists_star_int s0
        obtain ⟨r', hr'⟩ := Formalism.HermitianLattices.Ext.L3.MeanB.exists_star_int r
        obtain ⟨Y', hY'⟩ := Formalism.HermitianLattices.Ext.L3.MeanB.exists_star_int Y
        have e := congrArg (fun w => star (algebraMap (𝓞 K) K w)) hsr
        simp only [map_mul, map_pow, star_mul', star_pow] at e
        rw [← hs', ← hX', ← hs0', ← hr', ← hY', ← ht] at e
        have e' : s' * X' * s0' ^ N = r' * Y' * t ^ N := inj (by simpa only [map_mul, map_pow] using e)
        have hmem : s' * s0' ^ N * X' ∈ P ^ N := by
          rw [show s' * s0' ^ N * X' = r' * Y' * t ^ N by rw [← e']; ring]
          exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow htP N)
        refine mem_pow_of_coprime (sup_top_of_notMem hP ?_) N hmem
        intro h
        rcases hP.isPrime.mem_or_mem h with h1 | h1
        · exact (hc s hs).2 s' hs' h1
        · exact (hc s0 hs0).2 s0' hs0' (hP.isPrime.mem_of_pow_mem N h1)
  have h1 := (mem_pow_iff hP hZ0 (vF P Z + 1)).mp (hZ _)
  omega
end Formalism.L2.SG.Pf.G1
