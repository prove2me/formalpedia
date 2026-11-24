-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovolBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:50:24.94041+00:00
-- url     : https://prove2.me/submissions/8320b23a-f604-4b82-b138-0a9023158386

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_covol_le
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_dual_genus
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_discr
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_trace_int
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusScale


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
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : GenusCovolBound := by
  intro K V _ _ _ _ _ _ _ _ h hs hpos N ι hι L hL
  have hnd : h.Nondegenerate := by
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · by_contra hne
      have := hpos x hne
      rw [hx x] at this
      simp at this
    · by_contra hne
      have := hpos y hne
      rw [hy y] at this
      simp at this
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := by
    intro r
    have hi : IsIntegral ℤ (star (algebraMap (𝓞 K) K r)) := by
      have := (RingOfIntegers.isIntegral_coe r).map ((starRingEnd K).toIntAlgHom)
      rwa [RingHom.toIntAlgHom_apply, starRingEnd_apply] at this
    exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp hi
  have hdL := dualLattice (𝓞 K) K V h hs hnd hstar L hL
  obtain ⟨d, hd0, hd⟩ := genusScale K V h hs (dual h L) hdL.1
  set δ : ℤ := NumberField.discr K with hδ
  have hδ0 : δ ≠ 0 := NumberField.discr_ne_zero K
  refine ⟨Real.sqrt (((d * δ.natAbs ^ 2 : ℕ) : ℝ) ^ N), fun M hM _ _ => ?_⟩
  refine genusCovolBound_covol_le h N ι hι M (d * δ.natAbs ^ 2)
    (Nat.mul_pos hd0 (pow_pos (Int.natAbs_pos.mpr hδ0) 2)) ?_

  have key : ∀ y : V, (∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = z) →
      (δ : K) • y ∈ dual h M := by
    intro y hy
    simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.coe_restrictScalars]
    intro x hx
    rw [map_smul, smul_eq_mul]
    apply genusCovolBound_discr
    intro r
    obtain ⟨s, hs'⟩ := hstar r
    obtain ⟨z, hz⟩ := hy (s • x) (M.smul_mem s hx)
    refine ⟨z, ?_⟩
    rw [← hz, ← algebraMap_smul K s x, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hs',
      starRingEnd_apply, star_star, smul_eq_mul, mul_comm]
  intro y y' hy hy'
  have hmem := genusCovolBound_dual_genus h hs hnd hstar L hL M hM
  have h1 := hd (dual h M) hmem _ (key y hy) _ (key y' hy')
  obtain ⟨w, hw⟩ := Submodule.mem_one.mp h1
  obtain ⟨z, hz⟩ := genusCovolBound_trace_int w
  refine ⟨z, ?_⟩
  have e2 : h ((δ : K) • y) ((δ : K) • y') = (δ : K) * ((δ : K) * h y y') := by
    rw [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply, star_intCast, smul_eq_mul,
      smul_eq_mul]
  rw [← hz, hw, e2]
  have e : (d : K) * ((δ : K) * ((δ : K) * h y y')) =
      algebraMap ℚ K (((d * δ.natAbs ^ 2 : ℕ) : ℚ)) * h y y' := by
    have hna : ((δ.natAbs ^ 2 : ℕ) : ℚ) = (δ : ℚ) ^ 2 := by
      push_cast
      simp [sq_abs]
    rw [Nat.cast_mul, hna, map_mul, map_pow, map_natCast, map_intCast]
    ring
  rw [e, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
end Formalism.HermitianLatticesTheory
