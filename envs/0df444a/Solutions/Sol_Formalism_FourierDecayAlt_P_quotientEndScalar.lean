-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.quotientEndScalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:50:07.248518+00:00
-- url     : https://prove2.me/submissions/d9776928-04e2-4714-bb0c-dce76992b616

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mk_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_smul_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open A5x3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.EndKR := by
  intro K _ _ _ R ψ hD f
  obtain ⟨ϖ, hϖ, hex⟩ := hD.unif
  have := hD.t2
  have hcl : IsClosed (R : Set K) := hD.isCompact.isClosed
  let A : ℕ → Set K := fun m => {r | r ∈ R ∧ ∀ x : K, (ϖ : K) ^ m * x ∈ R →
    f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (r * x)}
  have hclosed : ∀ m, IsClosed (A m) := by
    intro m
    have h1 : A m = (R : Set K) ∩ ⋂ x : K, ⋂ _ : (ϖ : K) ^ m * x ∈ R,
        {r | f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (r * x)} := by
      ext r
      simp only [A, Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_iInter]
    rw [h1]
    refine hcl.inter (isClosed_iInter fun x => isClosed_iInter fun _ => ?_)
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (f (Submodule.Quotient.mk x))
    have h2 : {r : K | f (Submodule.Quotient.mk x) = (Submodule.Quotient.mk (r * x) : KR R)} =
        (fun r => y - r * x) ⁻¹' (R : Set K) := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe]
      rw [← hy, mk_eq_mk]
    rw [h2]
    exact hcl.preimage (by fun_prop)
  have hne : (⋂ m, A m).Nonempty := by
    apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    · intro m r hr
      refine ⟨hr.1, fun x hx => hr.2 x ?_⟩
      rw [pow_succ', mul_assoc]
      exact R.mul_mem hϖ hx
    · intro m
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
        (f (Submodule.Quotient.mk (((ϖ⁻¹ : Kˣ) : K) ^ m)))
      have hpow : (ϖ : K) ^ m * ((ϖ⁻¹ : Kˣ) : K) ^ m = 1 := by
        rw [← mul_pow, Units.mul_inv, one_pow]
      have hpm : (ϖ : K) ^ m ∈ R := R.pow_mem hϖ m
      have hr : (ϖ : K) ^ m * y ∈ R := by
        rw [← mk_eq_zero, ← smul_mk R ⟨_, hpm⟩, hy, ← map_smul, smul_mk, hpow,
          (mk_eq_zero R 1).2 R.one_mem, map_zero]
      refine ⟨(ϖ : K) ^ m * y, hr, fun x hx => ?_⟩
      have hx1 : (Submodule.Quotient.mk x : KR R) =
          (⟨_, hx⟩ : R) • Submodule.Quotient.mk (((ϖ⁻¹ : Kˣ) : K) ^ m) := by
        rw [smul_mk]
        congr 1
        simp only
        rw [mul_right_comm, hpow, one_mul]
      rw [hx1, map_smul, ← hy, smul_mk]
      congr 1
      simp only
      ring
    · exact hD.isCompact.of_isClosed_subset (hclosed 0) fun r hr => hr.1
    · exact hclosed
  obtain ⟨r, hr⟩ := hne
  rw [Set.mem_iInter] at hr
  refine ⟨⟨r, (hr 0).1⟩, fun x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    obtain ⟨m, hm⟩ := hex x
    rw [(hr m).2 x hm, smul_mk]
end Formalism.FourierDecayAlt.P
