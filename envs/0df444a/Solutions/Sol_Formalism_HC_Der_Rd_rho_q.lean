-- Prove2me | solution 1 for Formalism.HC.Der.Rd.rho_q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:10.100101+00:00
-- url     : https://prove2.me/submissions/6191632f-392b-417a-9baa-49e1e58b6e4b

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Theorems.Thm_Formalism_HC_Der_Rd_div_q
import Theorems.Thm_Formalism_HC_Der_Rd_q_ne_d
import Theorems.Thm_Formalism_HC_Der_Rd_mem_KK
import Theorems.Thm_Formalism_HC_Der_Rd_mem_ker_iff
import Theorems.Thm_Formalism_HC_Der_Rd_rho_le_half


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
open Formalism.HC.Der.Rd
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der.Rd
theorem _root_.solution : rho H.art.ker (H.condN / H.q) ≤ 1 / 2 := by
  rw [div_q]
  have : Fact H.q.Prime := ⟨H.hyp.1⟩
  have hf : H.QS * H.d ∣ H.condN := ⟨H.q, mul_right_comm _ _ _⟩
  have hq : H.q ∣ H.condN := (dvd_mul_left _ _).mul_right _
  have hc : Nat.Coprime (H.QS * H.d) H.q := Nat.Coprime.mul_left H.QS_coprime.coprime_mul_right_right
    ((Nat.coprime_primes H.hyp.2.1 H.hyp.1).mpr (q_ne_d H).symm)
  have hcyc : IsCyclic (ZMod.unitsMap hf).ker := by
    refine isCyclic_of_injective ((ZMod.unitsMap hq).comp (ZMod.unitsMap hf).ker.subtype) ?_
    rw [injective_iff_map_eq_one]
    rintro ⟨u, hu⟩ h1
    have h2 := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨(mem_ker_iff hf u).mp hu, (mem_ker_iff hq u).mp h1⟩
    rw [mul_right_comm, ← mem_ker_iff dvd_rfl, ZMod.unitsMap_self, MonoidHom.mem_ker, MonoidHom.id_apply] at h2
    exact Subtype.ext h2
  obtain ⟨⟨g, hg⟩, hgen⟩ := hcyc.exists_generator
  have hg2 := H.art_q g ((mem_ker_iff hf g).mp hg)
  have key : ∀ u ∈ KK H.condN (H.QS * H.d), H.art u ≠ 1 → H.art u = H.art g := by
    intro u hu h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨u, (mem_ker_iff hf u).mpr (mem_KK.mp hu)⟩)
    have h2 : g ^ k = u := congrArg Subtype.val hk
    rw [← h2, map_zpow] at h1 ⊢
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [zpow_mul, zpow_ofNat, hg2, one_zpow] at h1
      exact absurd rfl h1
    · rw [zpow_add, zpow_mul, zpow_ofNat, hg2, one_zpow, one_mul, zpow_one]
  refine rho_le_half _ hf fun u hu v hv h1 h2 => ?_
  rw [MonoidHom.mem_ker] at h1 h2 ⊢
  rw [map_mul, key u hu h1, key v hv h2, ← sq, hg2]
end Formalism.HC.Der.Rd
