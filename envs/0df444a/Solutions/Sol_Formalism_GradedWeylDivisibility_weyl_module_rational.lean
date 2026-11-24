-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.weyl_module_rational
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:04.739359+00:00
-- url     : https://prove2.me/submissions/4f2b8b8d-f567-4eeb-a0f1-2627a6657b25

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylRationalOf
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_weyl_denom
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
open MvPolynomial
noncomputable section
namespace Formalism.GradedWeylDivisibility
private theorem colAddGen_map_intCast {r n : ℕ} (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) ℤ) :
    colAddGen ℚ (r := r) l j (map (Int.castRingHom ℚ) f) =
      map (Int.castRingHom ℚ) (colAddGen ℤ (r := r) l j f) := by
  induction f using MvPolynomial.induction_on
  next c =>
    simp [colAddGen]
  next p q hp hq =>
    rw [_root_.map_add, _root_.map_add, _root_.map_add, hp, hq, _root_.map_add]
  next p v hp =>
    rw [_root_.map_mul, map_X, _root_.map_mul, _root_.map_mul, _root_.map_mul, hp]
    congr 1
    simp only [colAddGen, aeval_X]
    split_ifs <;> simp
private theorem map_intCast_mem_dualWeyl {r n : ℕ} (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) ℤ)
    (hf : f ∈ dualWeyl ℤ r n ν) : map (Int.castRingHom ℚ) f ∈ dualWeyl ℚ r n ν := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero,
    mem_weightedHomogeneousSubmodule] at hf ⊢
  obtain ⟨h1, h2⟩ := hf
  refine ⟨?_, ?_⟩
  · intro d hd
    apply h1
    intro h0
    apply hd
    rw [coeff_map, h0, _root_.map_zero]
  · intro l j hlj
    rw [colAddGen_map_intCast, h2 l j hlj, map_rename]
end Formalism.GradedWeylDivisibility
end
end

set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : WeylRationalOf := by
  unfold WeylRationalOf WeylRational
  intro h r n hn ν hν f hf
  have hfQ : map (Int.castRingHom ℚ) f ∈ weyl ℚ r n hn ν := by
    rw [h r n hn ν hν]
    exact map_intCast_mem_dualWeyl ν f hf
  obtain ⟨c, hc, u, hu, hmap⟩ := lclosedeq_weyl_denom hn ν _ hfQ
  refine ⟨c, hc, ?_⟩
  have huf : u = c • f := by
    apply MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ))
    rw [hmap, _root_.map_zsmul]
    exact Int.cast_smul_eq_zsmul ℚ c _
  rw [← huf]
  exact hu
end Formalism.GradedWeylDivisibility
