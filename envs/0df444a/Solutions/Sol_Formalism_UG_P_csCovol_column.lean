-- Prove2me | solution 1 for Formalism.UG.P.csCovol_column
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:17.292178+00:00
-- url     : https://prove2.me/submissions/e87c6dae-1a73-453d-8cd8-ad7679a4c34e

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsCovol
import Theorems.Thm_Formalism_UG_P_csCovol_discr_mul
import Theorems.Thm_Formalism_UG_P_csCovol_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module NumberField Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {N : ℕ}
  (ι : V →+ EuclideanSpace ℝ (Fin N))
namespace Formalism.UG.P
theorem _root_.solution
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (M : Submodule (𝓞 K) V) (b : Basis (Fin N) ℤ (Formalism.HermitianLatticesTheory.zmap ι M)) (m : Fin N → V)
    (hm : ∀ i, ι (m i) = b i) (e : 𝓞 K)
    (hdual : ∀ x ∈ Formalism.HermitianLatticesTheory.dual h M, (e : K) • x ∈ M) (n : ℤ) (c : 𝓞 K)
    (hc : algebraMap ℤ (𝓞 K) n = c * e)
    (hG : (Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k))).det ≠ 0) (j : Fin N) :
    ∃ a : Fin N → ℤ,
      (Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k))) *ᵥ (fun k => (a k : ℚ)) =
        ((n * discr K : ℤ) : ℚ) • Pi.single j (1 : ℚ) := by
  classical
  set G : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k)) with hGdef
  have htr : ∀ (q : ℚ) (y : K), Algebra.trace ℚ K ((q : K) * y) = q * Algebra.trace ℚ K y := by
    intro q y
    rw [← Rat.smul_def, map_smul, smul_eq_mul]
  have hunit : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  set cc : Fin N → ℚ := G⁻¹ *ᵥ Pi.single j (1 : ℚ) with hcc
  have hGc : G *ᵥ cc = Pi.single j (1 : ℚ) := by
    rw [hcc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hunit, Matrix.one_mulVec]
  set x : V := ∑ k, ((cc k : ℚ) : K) • m k with hx
  have hmx : ∀ i, Algebra.trace ℚ K (h (m i) x) = (Pi.single j (1 : ℚ) : Fin N → ℚ) i := by
    intro i
    rw [← hGc, hx, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul, htr]
    simp only [Matrix.mulVec, dotProduct, hGdef, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  have hloc : ∀ w ∈ M, ((discr K : ℚ) : K) * h w x ∈ Set.range (algebraMap (𝓞 K) K) := by
    intro w hw
    apply csCovol_discr_mul
    intro a
    have hai : IsIntegral ℤ (star (a : K)) :=
      (NumberField.RingOfIntegers.isIntegral_coe a).map (starRingEnd K).toIntAlgHom
    set a' : 𝓞 K := ⟨star (a : K), hai⟩ with ha'
    have hw' : a' • w ∈ M := M.smul_mem a' hw
    obtain ⟨aa, -, haa⟩ := csCovol_expand h ι hι M b m hm (a' • w) hw'
    have e1 := haa x
    simp only [hmx] at e1
    have hsmul : a' • w = (star (a : K)) • w := by
      rw [← algebraMap_smul K a' w]
      rfl
    rw [hsmul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul] at e1
    refine ⟨aa j, ?_⟩
    rw [e1]
    simp [Pi.single_apply]
  have hdx : ((discr K : ℚ) : K) • x ∈ Formalism.HermitianLatticesTheory.dual h M := by
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply]
    intro w hw
    rw [map_smul, smul_eq_mul]
    obtain ⟨r, hr⟩ := hloc w hw
    exact Submodule.mem_one.mpr ⟨r, hr⟩
  have hy : (((n * discr K : ℤ) : ℚ) : K) • x ∈ M := by
    have h1 := hdual _ hdx
    have h2 := M.smul_mem c h1
    have hcK : ((n : ℤ) : K) = (c : K) * (e : K) := by
      have := congrArg (fun t : 𝓞 K => (t : K)) hc
      simpa using this
    convert h2 using 1
    rw [← algebraMap_smul K c, smul_smul, smul_smul]
    congr 1
    push_cast
    rw [hcK]
    try simp only [algebraMap_smul, RingOfIntegers.coe_eq_algebraMap]
    try ring
  obtain ⟨aa, haa, -⟩ := csCovol_expand h ι hι M b m hm _ hy
  refine ⟨aa, ?_⟩
  funext i
  have e1 := haa (m i)
  rw [map_smul, smul_eq_mul, htr, hmx] at e1
  simp only [Matrix.mulVec, dotProduct, hGdef, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  rw [e1]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
end Formalism.UG.P
