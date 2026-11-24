-- Prove2me | solution 1 for Formalism.L2.SG.Pf.SatGramLoc.reduction_structure_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:28:41.255038+00:00
-- url     : https://prove2.me/submissions/f22441a2-6714-4e9c-962b-96d13c48d981

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLoc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLocPfB
import Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_rc_isIntegral
import Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_rc_idem_zero
import Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_rc_finrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.SatGramLoc
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace Formalism.L2.SG.Pf.SatGramLoc
theorem _root_.solution : RedCore := by
  intro F E _ _ _ _ _ σ hσ h2 v e he hee hes hct
  obtain ⟨c, hc, t, ht, hft⟩ := hct
  set e' := Formalism.UG.sigR σ (v.adicCompletion F) e with he'
  have he'e' : e' * e' = e' := by rw [he', ← map_mul, hee]
  have hee' : e * e' = 0 := hes
  have he'e : e' * e = 0 := by rw [mul_comm]; exact hee'

  have hidem : (1 - e - e') * (1 - e - e') = 1 - e - e' := by
    linear_combination hee + he'e' + 2 * hee'
  have hf0 : 1 - e - e' = 0 := rc_idem_zero v (1 - e - e') t c hc hidem hft (rc_isIntegral v t ht)
  have hsum : e + e' = 1 := by linear_combination -hf0
  have hfr : Module.finrank (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) = 2 := by
    rw [rc_finrank, h2]
  haveI : Nontrivial (E ⊗[F] v.adicCompletion F) := by
    have hpos : 0 < Module.finrank (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) := by
      rw [hfr]; norm_num
    exact Module.nontrivial_of_finrank_pos hpos
  have he0 : e ≠ 0 := by
    intro h0
    have h3 : e' = 0 := by rw [he', h0, map_zero]
    have h1 : (1 : E ⊗[F] v.adicCompletion F) = 0 := by rw [← hsum, h0, h3, add_zero]
    exact one_ne_zero h1

  have hli : LinearIndependent (v.adicCompletion F) ![e, e'] := by
    rw [LinearIndependent.pair_iff]
    intro s s' hst
    have h1 : s • e = 0 := by
      have h := congrArg (e * ·) hst
      simpa only [mul_add, mul_smul_comm, hee, hee', smul_zero, add_zero, mul_zero] using h
    have h3 : s' • e' = 0 := by
      have h := congrArg (e' * ·) hst
      simpa only [mul_add, mul_smul_comm, he'e, he'e', smul_zero, zero_add, mul_zero] using h
    have he'0 : e' ≠ 0 := by
      intro h0
      have h4 : e = 1 := by rw [← hsum, h0, add_zero]
      have h5 : e' = 1 := by rw [he', h4, map_one]
      rw [h0] at h5
      exact zero_ne_one h5
    exact ⟨(smul_eq_zero.mp h1).resolve_right he0, (smul_eq_zero.mp h3).resolve_right he'0⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) := by
    rw [hfr]; rfl
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = e := by simp [b]
  have hb1 : b 1 = e' := by simp [b]
  let r0 : E ⊗[F] v.adicCompletion F → v.adicCompletion F := fun x => b.repr x 0
  have hr : ∀ x, e * x = r0 x • e := by
    intro x
    have hx := b.sum_repr x
    rw [Fin.sum_univ_two, hb0, hb1] at hx
    conv_lhs => rw [← hx]
    rw [mul_add, mul_smul_comm, mul_smul_comm, hee, hee', smul_zero, add_zero]
  have huniq : ∀ α β : v.adicCompletion F, α • e = β • e → α = β :=
    fun α β h => smul_left_injective (v.adicCompletion F) he0 h
  have halg : ∀ a : v.adicCompletion F, ((1 : E) ⊗ₜ[F] a) * e = a • e := by
    intro a; rw [Algebra.smul_def]; rfl
  have hr1 : r0 1 = 1 := huniq _ _ (by rw [← hr, mul_one, one_smul])
  have hr0 : r0 0 = 0 := huniq _ _ (by rw [← hr, mul_zero, zero_smul])
  have hra : ∀ x y, r0 (x + y) = r0 x + r0 y := fun x y =>
    huniq _ _ (by rw [← hr, mul_add, hr, hr, add_smul])
  have hrm : ∀ x y, r0 (x * y) = r0 x * r0 y := fun x y =>
    huniq _ _ (calc r0 (x * y) • e = e * (x * y) := (hr _).symm
      _ = (e * x) * y := (mul_assoc _ _ _).symm
      _ = (r0 x • e) * y := by rw [hr]
      _ = r0 x • (e * y) := smul_mul_assoc _ _ _
      _ = r0 x • (r0 y • e) := by rw [hr]
      _ = (r0 x * r0 y) • e := (mul_smul _ _ _).symm)
  have hr2 : ∀ a : v.adicCompletion F, r0 ((1 : E) ⊗ₜ[F] a) = a := fun a =>
    huniq _ _ (by rw [← hr, mul_comm, halg])
  let r : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F :=
    { toFun := r0, map_one' := hr1, map_mul' := hrm, map_zero' := hr0, map_add' := hra }
  refine ⟨r, ?_, hr2, ?_, ?_⟩
  · show r0 e = 1
    exact huniq _ _ (by rw [← hr, hee, one_smul])
  · intro x hx
    have hint := rc_isIntegral v x hx
    letI := rcIntAlg (E := E) v
    have hint' : IsIntegral (v.adicCompletionIntegers F) (r x) := by
      refine IsIntegral.map_of_comp_eq (RingHom.id _) r ?_ hint
      refine RingHom.ext fun y => ?_
      show ((y : v.adicCompletionIntegers F) : v.adicCompletion F) =
        r0 ((1 : E) ⊗ₜ[F] ((y : v.adicCompletionIntegers F) : v.adicCompletion F))
      exact (hr2 _).symm
    first
    | (obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'; rw [← hy]; exact y.2)
    | exact ValuationSubring.mem_of_isIntegral _ hint'
    | exact (Valuation.integer.integers _).mem_of_integral hint'
  · intro x hx
    show x = ((1 : E) ⊗ₜ[F] r0 x) * e
    rw [halg, ← hr, hx]
end Formalism.L2.SG.Pf.SatGramLoc
