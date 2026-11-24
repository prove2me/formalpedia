-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.hecke_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:25:07.257143+00:00
-- url     : https://prove2.me/submissions/a536d028-ae1a-4f54-af30-533798d321fe

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_idem_sandwich
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_idem_sandwich_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_antiLift_of
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_antiLift_idem
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {G : Type} [Group G] [Fintype G]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσσ : ∀ x, σ (σ x) = x)
    (J : Subgroup G) (χ : J →* ℂˣ) (hJ : ∀ u : J, ∃ h : σ u ∈ J, χ ⟨σ u, h⟩ = χ u)
    (H : ∀ g, (∃ u u' : J, σ g = u * g * u' ∧ χ u * χ u' = 1) ∨
      (∃ u u' : J, (u : G) * g * u' = g ∧ χ u * χ u' ≠ 1)) (g g' : G) :
    (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) *
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) =
      (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) *
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) := by
  have key : ∀ g, twistedIdem J χ * MonoidAlgebra.of ℂ G (σ g) * twistedIdem J χ =
      twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ := by
    intro g
    rcases H g with ⟨u, u', h1, h2⟩ | ⟨u, u', h1, h2⟩
    · rw [h1, idem_sandwich, h2, Units.val_one, one_smul]
    · rw [idem_sandwich_zero J χ u u' g h1 h2]
      obtain ⟨m, hm⟩ := hJ u
      obtain ⟨m', hm'⟩ := hJ u'
      refine idem_sandwich_zero J χ ⟨σ u', m'⟩ ⟨σ u, m⟩ (σ g) ?_ ?_
      · show σ u' * σ g * σ u = σ g
        rw [← hσ, ← hσ, ← mul_assoc, h1]
      · rw [hm, hm', mul_comm]; exact h2
  have fix : ∀ a, antiLift σ hσ (twistedIdem J χ * a * twistedIdem J χ) =
      MulOpposite.op (twistedIdem J χ * a * twistedIdem J χ) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      rw [map_mul, map_mul, antiLift_idem σ hσ hσσ J χ hJ, antiLift_of, ← MulOpposite.op_mul,
        ← MulOpposite.op_mul, ← mul_assoc, key]
    | add x y hx hy => rw [mul_add, add_mul, map_add, hx, hy, MulOpposite.op_add]
    | smul r x hx => rw [mul_smul_comm, smul_mul_assoc, map_smul, hx, MulOpposite.op_smul]
  have h := map_mul (antiLift σ hσ) (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ)
    (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ)
  rw [fix, fix, ← MulOpposite.op_mul] at h
  have h' : (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) *
      (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) =
      twistedIdem J χ * (MonoidAlgebra.of ℂ G g * twistedIdem J χ * twistedIdem J χ *
        MonoidAlgebra.of ℂ G g') * twistedIdem J χ := by simp only [mul_assoc]
  rw [h', fix, ← h'] at h
  exact MulOpposite.op_injective h
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
