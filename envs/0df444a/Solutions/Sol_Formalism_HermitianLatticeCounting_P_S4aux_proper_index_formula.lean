-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.proper_index_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:26.014867+00:00
-- url     : https://prove2.me/submissions/ad96a6b2-25c0-4487-8084-083f29838790

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : ProperIndex := by
  intro O B _ _ _ _ q hq I hI
  have hcard : Nat.card B = Nat.card (B ⧸ I) * Nat.card I := by
    have := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup I.toAddSubgroup
    exact this
  obtain ⟨b, hb⟩ : ∃ b, b ∉ I := by
    by_contra hcon
    push Not at hcon
    exact hI (eq_top_iff.2 fun x _ => hcon x)
  set x : B ⧸ I := I.mkQ b with hx
  have hx0 : x ≠ 0 := by
    rw [hx, Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]; exact hb
  set f : O →ₗ[O] (B ⧸ I) := LinearMap.toSpanSingleton O (B ⧸ I) x with hf
  set J : Ideal O := LinearMap.ker f with hJ
  have hJtop : J ≠ ⊤ := by
    intro h
    have : (1 : O) ∈ J := by rw [h]; trivial
    rw [hJ, LinearMap.mem_ker, hf, LinearMap.toSpanSingleton_apply, one_smul] at this
    exact hx0 this
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJtop
  have hinj : Function.Injective (J.liftQ f le_rfl) := by
    rw [← LinearMap.ker_eq_bot]; exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have : Finite (B ⧸ I) := Finite.of_surjective _ I.mkQ_surjective
  have : Finite (O ⧸ J) := Finite.of_injective _ hinj
  have h1 : Nat.card (O ⧸ J) ≤ Nat.card (B ⧸ I) := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (O ⧸ P) ≤ Nat.card (O ⧸ J) :=
    Nat.card_le_card_of_surjective (Ideal.Quotient.factor hJP) (Ideal.Quotient.factor_surjective hJP)
  rw [hcard]
  exact Nat.mul_le_mul_right _ ((hq P hP).trans (h2.trans h1))
end Formalism.HermitianLatticeCounting.P.S4aux
