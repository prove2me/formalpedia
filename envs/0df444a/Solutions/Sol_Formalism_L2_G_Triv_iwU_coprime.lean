-- Prove2me | solution 1 for Formalism.L2.G.Triv.iwU_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:26:12.045798+00:00
-- url     : https://prove2.me/submissions/dc360225-f733-4a87-b773-92ad483a3d10

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ClosureUpperUni
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddPowOfMulSelfEqZero
import Definitions.Def_Lemmata_GeneralBFactLeftTail_Imports
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_OneAddPowOfSq
import Theorems.Thm_Formalism_L2_G_Triv_bc_injective
import Theorems.Thm_Formalism_L2_G_Triv_unip_coprime
import Theorems.Thm_Formalism_L2_G_Triv_closure_upperUni
import Theorems.Thm_Formalism_L2_G_Triv_natCast_mem_max
import Theorems.Thm_UpperTheory_Reformulated_B_Qe27_closure_upperUni


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {F : Type} [Field F] [NumberField F] {k : ℕ}
namespace Formalism.L2.G.Triv
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (hg : g.Prime) (hgv : (g : 𝓞 F) ∈ v.asIdeal)
    (δ : GL (Fin k) (v.adicCompletion F)) (hδ : δ ∈ iwU F k v) (N : ℕ) (hc : Nat.Coprime N g) (hN : δ ^ N = 1) : δ = 1 := by
  obtain ⟨a, ha, rfl⟩ := hδ
  have hinj : Function.Injective (bc (n := Fin k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) :=
    bc_injective _ (FaithfulSMul.algebraMap_injective _ _)
  have haN : a ^ N = 1 := hinj (by rw [map_pow, hN, map_one])
  have hu := closure_upperUni _ _ (Subgroup.mem_comap.1 ha)
  have hgm := natCast_mem_max v g hgv
  have hNu : IsUnit (N : v.adicCompletionIntegers F) := by
    by_contra h
    have hm : (N : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
      (IsLocalRing.mem_maximalIdeal _).2 h
    have h1 : ((Nat.gcd N g : ℕ) : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
      have hb := Nat.gcd_eq_gcd_ab N g
      have : ((Nat.gcd N g : ℕ) : v.adicCompletionIntegers F) =
          (N : v.adicCompletionIntegers F) * ((Nat.gcdA N g : ℤ) : v.adicCompletionIntegers F) +
          (g : v.adicCompletionIntegers F) * ((Nat.gcdB N g : ℤ) : v.adicCompletionIntegers F) := by
        have := congrArg (fun z : ℤ => (z : v.adicCompletionIntegers F)) hb
        push_cast at this
        exact this
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hm) (Ideal.mul_mem_right _ _ hgm)
    rw [hc, Nat.cast_one] at h1
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1
  have hA : ∀ i j : Fin k, j ≤ i → ((a : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) - 1) i j ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    intro i j hij
    rw [← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub]
    rcases hij.lt_or_eq with h | h
    · have := (hu i j).1 h
      have h' : Ideal.Quotient.mk _ ((a : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) i j) = 0 := this
      rw [h', Matrix.one_apply_ne h.ne', map_zero, sub_zero]
    · subst h
      have := (hu j j).2
      have h' : Ideal.Quotient.mk _ ((a : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) j j) = 1 := this
      rw [h', Matrix.one_apply_eq, map_one, sub_self]
  have h1 : (a : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) = 1 :=
    unip_coprime _ (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top) g hg hgm _ hA N hNu hc
      (by rw [← Units.val_pow_eq_pow_val, haN, Units.val_one])
  have : a = 1 := Units.ext h1
  rw [this, map_one]
end Formalism.L2.G.Triv
