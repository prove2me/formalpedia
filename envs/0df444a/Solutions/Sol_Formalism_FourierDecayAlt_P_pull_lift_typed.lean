-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.pull_lift_typed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:53.875747+00:00
-- url     : https://prove2.me/submissions/43621f09-e511-4b49-a130-e6cc06be7ae9

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx12_lift_per
import Theorems.Thm_Formalism_FourierDecayAlt_P_pull_lattice_typed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.PullLiftTyped := by
  intro hT E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ R u α ψ η Θ hR hu x
  have h0 := Formalism.FourierDecayAlt.P.pull_lattice_typed hT E g (-ν) s hg hpd P hP hgP K o σ hσ R u α ψ η Θ
    hR hu ((g : E) ^ 2 * x)
  have hloc : (g : E) ^ 2 * x ∈ S6.locAt E P (S6.perLat E g (-ν) s) ↔
      x ∈ S6.locAt E P (S6.liftLat E g ν s) := by
    simp only [S6.locAt, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, ha, h⟩
      refine ⟨a, ha, (Formalism.FourierDecayAlt.P.Jx12.lift_per E g hg ν s _).2 ?_⟩
      rwa [mul_left_comm]
    · rintro ⟨a, ha, h⟩
      refine ⟨a, ha, ?_⟩
      have h' := (Formalism.FourierDecayAlt.P.Jx12.lift_per E g hg ν s _).1 h
      rwa [mul_left_comm] at h'
  refine Iff.trans ?_ (h0.trans hloc)
  have hg' : (g : K) ≠ 0 := by
    intro h
    apply Units.ne_zero u
    rw [hu, h, inv_zero, mul_zero]
    rfl
  have hs2 : ((-1 : K) ^ s) * (-1) ^ s = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hgg : (g : K)⁻¹ * (g : K)⁻¹ * (g : K) ^ 2 = 1 := by field_simp
  have hinv : ((u⁻¹ : (K × K)ˣ) : K × K) = (u : K × K) * (g : K × K) ^ 2 := by
    rw [Units.val_inv_eq_inv_val]
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [hu]
    ext
    · simp only [Prod.fst_mul, Prod.pow_fst, Prod.fst_natCast, Prod.fst_one]
      linear_combination hgg
    · simp only [Prod.snd_mul, Prod.pow_snd, Prod.snd_natCast, Prod.snd_one]
      linear_combination ((g : K)⁻¹ * (g : K)⁻¹ * (g : K) ^ 2) * hs2 + hgg
  show ((u⁻¹ : (K × K)ˣ) : K × K) * (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) x ∈ R ↔
    (u : K × K) * (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) ((g : E) ^ 2 * x) ∈ R
  rw [hinv, map_mul, map_pow, map_natCast, mul_assoc]
end Formalism.FourierDecayAlt.P
