-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.prime_to_part_endomorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:59:40.432132+00:00
-- url     : https://prove2.me/submissions/bea87a4c-3a92-42f9-9e59-eb9aa9b1abe6

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_PropositionOneCentralCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_primeToPart_unique
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
private theorem ptp_lemma {M : Type} [Monoid M] {l : ℕ} (hl : l.Prime) {x : M}
    (hx : IsOfFinOrder x) :
    (primeToPart l x) ^ (l ^ (orderOf x).factorization l) = x ^ (l ^ (orderOf x).factorization l) ∧
    Nat.Coprime l (orderOf (primeToPart l x)) ∧ IsOfFinOrder (primeToPart l x) ∧
    ∀ b, (orderOf x).factorization l ≤ b → (primeToPart l x) ^ (l ^ b) = x ^ (l ^ b) := by
  have hmpos : 0 < orderOf x := hx.orderOf_pos
  have hm0 : orderOf x ≠ 0 := hmpos.ne'
  have hcl : Nat.Coprime l (orderOf x / l ^ (orderOf x).factorization l) :=
    Nat.coprime_ordCompl hl hm0
  have hcop' := Nat.Coprime.pow_left ((orderOf x).factorization l) hcl
  have hm'pos : 0 < orderOf x / l ^ (orderOf x).factorization l := Nat.ordCompl_pos l hm0
  have hsplit : l ^ (orderOf x).factorization l * (orderOf x / l ^ (orderOf x).factorization l) =
      orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ l
  have hφm : 0 < Nat.totient (orderOf x / l ^ (orderOf x).factorization l) := by
    first
    | exact Nat.totient_pos.2 hm'pos
    | exact Nat.totient_pos hm'pos
  have hP : primeToPart l x = x ^ ((l ^ (orderOf x).factorization l) ^
      Nat.totient (orderOf x / l ^ (orderOf x).factorization l)) := rfl
  set v := (orderOf x).factorization l with hv
  set m' := orderOf x / l ^ v with hm'
  set N := (l ^ v) ^ Nat.totient m' with hN
  have hlvN : l ^ v ∣ N := dvd_pow_self _ hφm.ne'
  have ha : (primeToPart l x) ^ (l ^ v) = x ^ (l ^ v) := by
    rw [hP, ← pow_mul, ← pow_mod_orderOf x (N * l ^ v), ← pow_mod_orderOf x (l ^ v)]
    congr 1
    have h1 : N * l ^ v ≡ 1 * l ^ v [MOD m'] := (Nat.ModEq.pow_totient hcop').mul_right _
    rw [one_mul] at h1
    have h2 : N * l ^ v ≡ l ^ v [MOD l ^ v] :=
      (Nat.modEq_zero_iff_dvd.2 (dvd_mul_left _ _)).trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl).symm
    have h3 := (Nat.modEq_and_modEq_iff_modEq_mul hcop').1 ⟨h2, h1⟩
    rw [hsplit] at h3
    exact h3
  have hb : Nat.Coprime l (orderOf (primeToPart l x)) := by
    have h4 : (primeToPart l x) ^ m' = 1 := by
      rw [hP, ← pow_mul]
      obtain ⟨c, hc⟩ := hlvN
      have h5 : N * m' = c * orderOf x := by rw [hc, ← hsplit]; ring
      rw [h5, pow_mul', pow_orderOf_eq_one, one_pow]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one h4) hcl
  have hc : IsOfFinOrder (primeToPart l x) := by
    rw [hP]
    exact hx.pow
  refine ⟨ha, hb, hc, fun b hvb => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hvb
  rw [pow_add, pow_mul, pow_mul, ha]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial Formalism.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial
section aux
variable {α β : Type} [Fintype α]
end aux
section prod
variable {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
end prod
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

set_option autoImplicit false
open Finset Polynomial
open scoped ComplexOrder
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : PrimeToPartEndo := by
  intro M M' _ _ l x y φ hl hx hy
  obtain ⟨hxa, hxc, hxf, hxd⟩ := ptp_lemma hl hx
  obtain ⟨hya, hyc, hyf, hyd⟩ := ptp_lemma hl hy
  have hmap : ∀ w : M, IsOfFinOrder w → IsOfFinOrder (φ w) := fun w hw => by
    obtain ⟨n, hn, hwn⟩ := isOfFinOrder_iff_pow_eq_one.1 hw
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, by rw [← map_pow, hwn, map_one]⟩
  constructor
  · have hxy : IsOfFinOrder (x * y) := (Commute.all x y).isOfFinOrder_mul hx hy
    refine primeToPart_unique (a := max ((orderOf x).factorization l) ((orderOf y).factorization l))
      hl hxy ((Commute.all _ _).isOfFinOrder_mul hxf hyf) ?_ ?_
    · exact Nat.Coprime.coprime_dvd_right ((Commute.all _ _).orderOf_mul_dvd_mul_orderOf)
        (Nat.Coprime.mul_right hxc hyc)
    · rw [mul_pow, mul_pow, hxd _ (le_max_left _ _), hyd _ (le_max_right _ _)]
  · refine (primeToPart_unique (a := (orderOf x).factorization l) hl (hmap x hx) (hmap _ hxf) ?_ ?_).symm
    · exact Nat.Coprime.coprime_dvd_right (orderOf_map_dvd φ _) hxc
    · rw [← map_pow, ← map_pow, hxa]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
